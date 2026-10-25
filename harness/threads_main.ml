(* Differential driver for the thread layer (theories/Core/Threads.v), cloned from machine_main.ml.
   threads_main <classdir[:...]> <class> <method> <descriptor> <inputs> <fuel> [unicode-table]
   Each input runs under several schedulers; if they all give the same answer it is printed,
   otherwise "NONDET <a> | <b>" (a mismatch for these schedule-independent tests).
   Below: the original header of machine_main.ml.
   Differential driver for the machine with the JDK models (heap, calls, exceptions, <clinit>, Strings).
   machine_main <classdir[:classdir...]> <binary class name> <method> <descriptor> <inputs> <fuel> [unicode-table]
   Loads every .class under <classdir>; each input line is one fresh run.
   Arguments: decimal ints/longs; Strings as "s:<4 hex digits per UTF-16 unit>" or "null".
   Output: "V <n>" | "V void" | "V null" | "S <hex units>" | "E <class>[ m:<hex units>|m:null]" | "STUCK <why>" | "FUEL".
   An exception's message is printed only when the machine models it. *)
open Jvm

let rec pos_of_int n =
  if n = 1 then XH else if n land 1 = 1 then XI (pos_of_int (n lsr 1)) else XO (pos_of_int (n lsr 1))
let z_of_int n = if n = 0 then Z0 else if n > 0 then Zpos (pos_of_int n) else Zneg (pos_of_int (-n))
let rec int_of_pos = function XH -> 1 | XO p -> 2 * int_of_pos p | XI p -> 2 * int_of_pos p + 1
let int_of_z = function Z0 -> 0 | Zpos p -> int_of_pos p | Zneg p -> - (int_of_pos p)
let rec int_of_nat = function O -> 0 | S n -> 1 + int_of_nat n
let nat_of_int n = let rec go n acc = if n = 0 then acc else go (n - 1) (S acc) in go n O

let rec class_files dir =
  Sys.readdir dir |> Array.to_list |> List.sort compare |> List.concat_map (fun f ->
    let p = Filename.concat dir f in
    if Sys.is_directory p then class_files p
    else if Filename.check_suffix f ".class" then [p] else [])

(* Unicode environment from the JDK's own tables (harness/java/UnicodeTables.java) *)
let n_cp = 0x110000
let up = Array.init n_cp (fun i -> i) and lo = Array.init n_cp (fun i -> i)
let dg = Array.make n_cp (-1) and fl = Array.make n_cp 0
let load_tables f =
  In_channel.with_open_text f (fun ic ->
    let rec loop () = match In_channel.input_line ic with
      | None -> ()
      | Some l when String.length l > 0 && l.[0] = '#' -> loop ()
      | Some l -> Scanf.sscanf l "%d %d %d %d %d" (fun cp u w d f -> up.(cp) <- u; lo.(cp) <- w; dg.(cp) <- d; fl.(cp) <- f); loop ()
    in loop ())
let inr z = let i = int_of_z z in if i >= 0 && i < n_cp then Some i else None
let uenv = {
  u_upper = (fun z -> match inr z with Some i -> z_of_int up.(i) | None -> z);
  u_lower = (fun z -> match inr z with Some i -> z_of_int lo.(i) | None -> z);
  u_digit = (fun z r -> if int_of_z r <> 10 then failwith "digit: only radix 10 tabled"
                        else match inr z with Some i -> z_of_int dg.(i) | None -> z_of_int (-1));
  u_is_whitespace = (fun z -> match inr z with Some i -> fl.(i) land 1 <> 0 | None -> false);
  u_is_letter = (fun z -> match inr z with Some i -> fl.(i) land 2 <> 0 | None -> false);
  u_is_digit = (fun z -> match inr z with Some i -> fl.(i) land 4 <> 0 | None -> false);
  u_is_upper = (fun z -> match inr z with Some i -> fl.(i) land 8 <> 0 | None -> false);
  u_is_lower = (fun z -> match inr z with Some i -> fl.(i) land 16 <> 0 | None -> false) }
(* identity hash codes: a fixed mix of the heap address (HotSpot's are unspecified: results that depend
   on them are not comparable) *)
let env = { j_u = uenv; j_log_enabled = (fun _ -> false);
            j_ihash = (fun z -> z_of_int (((int_of_z z) * 2654435761) land 0x7fffffff));
            (* seeds the JDK draws once per run (ModelEnv.seed n); MODEL_SEED<n> overrides *)
            j_seed = (fun n -> let v = (try int_of_string (Sys.getenv ("MODEL_SEED" ^ string_of_int (int_of_z n)))
                                        with _ -> 0x2545F491 + 977 * (int_of_z n)) in z_of_int v) }

let hex_units s =
  let n = String.length s / 4 in
  List.init n (fun i -> z_of_int (int_of_string ("0x" ^ String.sub s (4 * i) 4)))
let units_hex u = String.concat "" (List.map (fun z -> Printf.sprintf "%04x" (int_of_z z)) u)


(* Schedulers: round robin with quanta 1, 3 and 17, and three pseudo-random ones. The value is
   reduced modulo the number of threads that can step, so it is kept small (unary nat). *)
let lcg seed = let x = ref seed in fun () -> x := (!x * 1103515245 + 12345) land 0x3fffffff; !x
let schedulers () =
  let rr q = (fun k -> nat_of_int ((int_of_nat k / q) mod 8)) in
  let rnd seed = let g = lcg seed in let memo = Hashtbl.create 1024 in
    (fun k -> let k = int_of_nat k in
      match Hashtbl.find_opt memo k with Some v -> v | None -> let v = nat_of_int (g () mod 8) in Hashtbl.add memo k v; v) in
  [rr 1; rr 3; rr 17; rnd 1; rnd 2; rnd 3]

let show s v = match v with
  | None -> "V void"
  | Some (VInt z) | Some (VLong z) -> "V " ^ z_to_string z
  | Some VNull -> "V null"
  | Some (VFloat b) -> "F " ^ z_to_string (canon32 b)
  | Some (VDouble b) -> "D " ^ z_to_string (canon64 b)
  | Some v -> (match str_value s v with Some u -> String.trim ("S " ^ units_hex u) | None -> "V other")

let render = function
  | TRValue (v, tm) -> show (tm_ms tm) v
  | TRExc (e, tm) ->
      let s = tm_ms tm in
      let msg = match s.ms_heap e with
        | Some (OObj (_, fs)) -> (match List.assoc_opt "detailMessage" fs with
            | Some VNull -> " m:null"
            | Some v -> (match str_value s v with Some u -> " m:" ^ units_hex u | None -> "")
            | None -> "")
        | _ -> "" in
      "E " ^ exn_class s e ^ msg
  | TRDeadlock _ -> "DEADLOCK"
  | TRStuckRun w -> "STUCK " ^ w
  | TROutOfFuel -> "FUEL"

let () =
  let dir = Sys.argv.(1) and cls = String.map (fun c -> if c = '.' then '/' else c) Sys.argv.(2)
  and name = Sys.argv.(3) and desc = Sys.argv.(4) and inp = Sys.argv.(5) in
  let fuel = nat_of_int (int_of_string Sys.argv.(6)) in
  if Array.length Sys.argv > 7 then load_tables Sys.argv.(7);
  let files = String.split_on_char ':' dir |> List.concat_map class_files |> List.map (fun f ->
    let d = In_channel.with_open_bin f In_channel.input_all in
    List.init (String.length d) (fun i -> z_of_int (Char.code d.[i]))) in
  let prog = match load_program files with Some p -> p | None -> prerr_endline "a class file did not parse"; exit 2 in
  let mdl = jdk_model prog env in
  let ps = match parse_mdesc desc with Some (ps, _) -> ps | None -> exit 2 in
  In_channel.with_open_text inp (fun ic ->
    let rec loop () =
      match In_channel.input_line ic with
      | None -> ()
      | Some line ->
        let toks = String.split_on_char ' ' (String.trim line) |> List.filter (fun s -> s <> "") in
        let args = List.map2 (fun t s -> match t with
            | TLong -> JVal (VLong (z_of_string s))
            | TRef _ when s = "null" -> JNull
            | TRef _ when String.length s >= 2 && String.sub s 0 2 = "s:" -> JStr (hex_units (String.sub s 2 (String.length s - 2)))
            | _ -> JVal (VInt (z_of_string s))) ps toks in
        let outs = List.map (fun sch -> render (call_static_args_threads prog mdl sch fuel cls name desc args)) (schedulers ()) in
        let first = List.hd outs in
        (match List.find_opt (fun o -> o <> first) outs with
         | None -> print_endline first
         | Some other -> print_endline ("NONDET " ^ first ^ " | " ^ other));
        loop ()
    in loop ())

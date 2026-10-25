(* Differential driver for the machine with the JDK models (heap, calls, exceptions, <clinit>, Strings).
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
let env = { j_u = uenv; j_log_enabled = (fun _ -> false) }

let hex_units s =
  let n = String.length s / 4 in
  List.init n (fun i -> z_of_int (int_of_string ("0x" ^ String.sub s (4 * i) 4)))
let units_hex u = String.concat "" (List.map (fun z -> Printf.sprintf "%04x" (int_of_z z)) u)

let () =
  let dir = Sys.argv.(1) and cls = String.map (fun c -> if c = '.' then '/' else c) Sys.argv.(2)
  and name = Sys.argv.(3) and desc = Sys.argv.(4) and inp = Sys.argv.(5) in
  let fuel = nat_of_int (int_of_string Sys.argv.(6)) in
  if Array.length Sys.argv > 7 then load_tables Sys.argv.(7);
  (* <classdir> may be a ':'-separated list of directories; the first definition of a class wins *)
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
            | TFloat -> JVal (VFloat (z_of_string s))
            | TDouble -> JVal (VDouble (z_of_string s))
            | TRef _ when s = "null" -> JNull
            | TRef _ when String.length s >= 2 && String.sub s 0 2 = "s:" -> JStr (hex_units (String.sub s 2 (String.length s - 2)))
            | _ -> JVal (VInt (z_of_string s))) ps toks in
        let out = match call_static_args prog mdl fuel cls name desc args with
          | MRValue (None, _) -> "V void"
          | MRValue (Some (VInt z), _) | MRValue (Some (VLong z), _) -> "V " ^ z_to_string z
          | MRValue (Some VNull, _) -> "V null"
          | MRValue (Some (VFloat b), _) -> "F " ^ z_to_string (canon32 b)
          | MRValue (Some (VDouble b), _) -> "D " ^ z_to_string (canon64 b)
          | MRValue (Some v, s) -> (match str_value s v with Some u -> String.trim ("S " ^ units_hex u) | None ->
              (* an object: its class and the length of each array-valued field *)
              (match v with
               | VRef l -> (match s.ms_heap l with
                   | Some (OObj (c, fs)) ->
                       let arr = List.filter_map (fun (f, fv) -> match fv with
                           | VRef a -> (match s.ms_heap a with Some (OArr (_, es)) -> Some (Printf.sprintf "%s.length=%d" f (List.length es)) | _ -> None)
                           | _ -> None) fs in
                       String.concat " " (("O " ^ c) :: arr)
                   | _ -> "V other")
               | _ -> "V other"))
          | MRExc (e, s) ->
              (* the message, when the machine models it (field "detailMessage" of a VM-created exception) *)
              let msg = match s.ms_heap e with
                | Some (OObj (_, fs)) -> (match List.assoc_opt "detailMessage" fs with
                    | Some VNull -> " m:null"
                    | Some v -> (match str_value s v with Some u -> " m:" ^ units_hex u | None -> "")
                    | None -> "")
                | _ -> "" in
              "E " ^ exn_class s e ^ msg
          | MRStuck w -> "STUCK " ^ w
          | MROutOfFuel -> "FUEL" in
        print_endline out; loop ()
    in loop ())

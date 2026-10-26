(* Differential-test driver for the extracted Rocq model.
   model_main <file.class> <method> <descriptor> <inputs> <fuel>
   Each input line holds the decimal arguments; prints one result line per input:
   "V <n>" | "V void" | "E <internal class name>" | "STUCK <why>" | "FUEL". *)
open Jvm

let z_of_int n = Big_int_Z.big_int_of_int n
let nat_of_int n = let rec go n acc = if n = 0 then acc else go (n - 1) (S acc) in go n O

let () =
  let cls = Sys.argv.(1) and name = Sys.argv.(2) and desc = Sys.argv.(3) and inp = Sys.argv.(4) in
  let fuel = nat_of_int (int_of_string Sys.argv.(5)) in
  let data = In_channel.with_open_bin cls In_channel.input_all in
  let bytes = List.init (String.length data) (fun i -> z_of_int (Char.code data.[i])) in
  let ps = match parse_mdesc desc with Some (ps, _) -> ps | None -> prerr_endline "bad descriptor"; exit 2 in
  match load_method bytes name desc with
  | None -> prerr_endline ("method not found or class file not parsed: " ^ name ^ desc); exit 2
  | Some m ->
    In_channel.with_open_text inp (fun ic ->
      let rec loop () =
        match In_channel.input_line ic with
        | None -> ()
        | Some line ->
          let toks = String.split_on_char ' ' (String.trim line) |> List.filter (fun s -> s <> "") in
          let args = List.map2 (fun t s -> match t with
              | TLong -> VLong (z_of_string s)
              | _ -> VInt (z_of_string s)) ps toks in
          let out = match invoke_static fuel m args with
            | RValue None -> "V void"
            | RValue (Some (VInt z)) | RValue (Some (VLong z)) -> "V " ^ z_to_string z
            | RValue (Some _) -> "V other"
            | RExc c -> "E " ^ c
            | RStuck w -> "STUCK " ^ w
            | ROutOfFuel -> "FUEL" in
          print_endline out; loop ()
      in loop ())

(* Model side of the float/double differential test.

   Usage: model_float.exe OP INFILE OUTFILE

   Each input line holds one or two operands: float bits as unsigned hex
   (8 digits), double bits as unsigned hex (16 digits), int / long as signed
   decimal.  Output: one result per line, float/double bits as lowercase
   unsigned hex without leading zeros (like Integer/Long.toHexString), int
   and long results as signed decimal.

   OCaml machine integers are used only to parse and print; all arithmetic
   is the extracted Rocq code over the inductive [z]/[positive]. *)

open Float_model

(* ---- int64 <-> extracted z ---- *)

let pos_of_u64 (v : int64) : positive option =
  let rec go acc i =
    if i < 0 then acc
    else
      let b = Int64.logand (Int64.shift_right_logical v i) 1L = 1L in
      match acc with
      | None -> go (if b then Some XH else None) (i - 1)
      | Some p -> go (Some (if b then XI p else XO p)) (i - 1)
  in
  go None 63

let z_of_u64 v = match pos_of_u64 v with None -> Z0 | Some p -> Zpos p

let z_of_s64 v =
  if Int64.compare v 0L >= 0 then z_of_u64 v
  else match pos_of_u64 (Int64.neg v) with Some p -> Zneg p | None -> Z0

let rec pos_size = function XH -> 1 | XO p | XI p -> 1 + pos_size p

let rec u64_of_pos = function
  | XH -> 1L
  | XO p -> Int64.shift_left (u64_of_pos p) 1
  | XI p -> Int64.logor (Int64.shift_left (u64_of_pos p) 1) 1L

(* bit pattern of width w, printed as unsigned hex; anything outside
   [0, 2^w) is printed as "BAD" and will mismatch *)
let show_bits w (z : z) =
  match z with
  | Z0 -> "0"
  | Zpos p when pos_size p <= w -> Printf.sprintf "%Lx" (u64_of_pos p)
  | _ -> "BAD"

(* signed integer of width w (32 or 64) *)
let show_int w (z : z) =
  match z with
  | Z0 -> "0"
  | Zpos p when pos_size p <= w - 1 -> Printf.sprintf "%Lu" (u64_of_pos p)
  | Zneg p when pos_size p <= w - 1 || (pos_size p = w && (match p with XO _ -> true | _ -> false)
                                        && Int64.equal (u64_of_pos p) (Int64.shift_left 1L (w - 1))) ->
    "-" ^ Printf.sprintf "%Lu" (u64_of_pos p)
  | _ -> "BAD"

let hex s = z_of_u64 (Int64.of_string ("0x" ^ s))  (* hex accepts the full unsigned range *)
let dec s = z_of_s64 (Int64.of_string s)

(* ---- operation table ---- *)

type arg = F | D | I | L
type res = RF | RD | RI | RL

let mode0 = Z0
let mode1 = Zpos XH
let mode2 = Zpos (XO XH)

let ops : (string * (arg list * res * (z list -> z))) list =
  let b2 f = function [a; b] -> f a b | _ -> failwith "arity" in
  let u1 f = function [a] -> f a | _ -> failwith "arity" in
  [ "fadd", ([F; F], RF, b2 fadd32);
    "fsub", ([F; F], RF, b2 fsub32);
    "fmul", ([F; F], RF, b2 fmul32);
    "fdiv", ([F; F], RF, b2 fdiv32);
    "frem", ([F; F], RF, b2 frem32);
    "fneg", ([F], RF, u1 (fun a -> canon32 (fneg32 a)));
    "fneg_raw", ([F], RF, u1 fneg32);
    "dadd", ([D; D], RD, b2 dadd64);
    "dsub", ([D; D], RD, b2 dsub64);
    "dmul", ([D; D], RD, b2 dmul64);
    "ddiv", ([D; D], RD, b2 ddiv64);
    "drem", ([D; D], RD, b2 drem64);
    "dneg", ([D], RD, u1 (fun a -> canon64 (dneg64 a)));
    "dneg_raw", ([D], RD, u1 dneg64);
    "i2f", ([I], RF, u1 i2f);
    "i2d", ([I], RD, u1 i2d);
    "l2f", ([L], RF, u1 l2f);
    "l2d", ([L], RD, u1 l2d);
    "f2d", ([F], RD, u1 f2d);
    "d2f", ([D], RF, u1 d2f);
    "f2i", ([F], RI, u1 f2i);
    "f2l", ([F], RL, u1 f2l);
    "d2i", ([D], RI, u1 d2i);
    "d2l", ([D], RL, u1 d2l);
    "fcmpl", ([F; F], RI, b2 fcmpl);
    "fcmpg", ([F; F], RI, b2 fcmpg);
    "dcmpl", ([D; D], RI, b2 dcmpl);
    "dcmpg", ([D; D], RI, b2 dcmpg);
    (* canary mutants (see FloatExtract.v) *)
    "mut_tiesaway_fadd", ([F; F], RF, b2 (add_mut mode1 binary32));
    "mut_tiesaway_dadd", ([D; D], RD, b2 (add_mut mode1 binary64));
    "mut_tiesaway_fmul", ([F; F], RF, b2 (mul_mut mode1 binary32));
    "mut_tiesaway_dmul", ([D; D], RD, b2 (mul_mut mode1 binary64));
    "mut_ftz_fadd", ([F; F], RF, b2 (add_mut mode2 binary32));
    "mut_ftz_dadd", ([D; D], RD, b2 (add_mut mode2 binary64));
    "mut_ftz_fmul", ([F; F], RF, b2 (mul_mut mode2 binary32));
    "mut_ftz_dmul", ([D; D], RD, b2 (mul_mut mode2 binary64));
  ]

let parse_arg = function F | D -> hex | I | L -> dec
let show = function RF -> show_bits 32 | RD -> show_bits 64 | RI -> show_int 32 | RL -> show_int 64

let () =
  if Array.length Sys.argv <> 4 then (prerr_endline "usage: model_float OP IN OUT"; exit 2);
  let op = Sys.argv.(1) in
  let args, res, fn =
    try List.assoc op ops with Not_found -> prerr_endline ("unknown op " ^ op); exit 2 in
  let ic = open_in Sys.argv.(2) and oc = open_out Sys.argv.(3) in
  (try
     while true do
       let line = input_line ic in
       let toks = List.filter (fun s -> s <> "") (String.split_on_char ' ' line) in
       if List.length toks <> List.length args then failwith ("bad line: " ^ line);
       let zs = List.map2 parse_arg args toks in
       output_string oc (show res (fn zs));
       output_char oc '\n'
     done
   with End_of_file -> ());
  close_in ic; close_out oc

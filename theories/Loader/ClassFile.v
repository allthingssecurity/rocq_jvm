(** * Class-file parser and bytecode decoder, written in Rocq (JVMS SE 21, chapter 4).

    The loader's only job outside Rocq is to copy the bytes of a real
    [.class] file into a Rocq list (tools/classdump.py, which also records the
    file's SHA-256 so the copy can be re-checked).  Everything else -- the
    constant pool, methods, the [Code] attribute, exception tables and the
    decoding of every opcode -- is done here, so the theorems about a Camel
    method are statements about [parse_class <bytes of the real file>].

    Parsing is partial ([option]): malformed input gives [None].  Constant
    pool resolution happens during decoding: [ldc] carries the constant,
    field/method instructions carry symbolic references. *)

From Stdlib Require Import ZArith String Ascii List Bool.
From JVM.Core Require Import Int Instr.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Definition bind {A B} (o : option A) (f : A -> option B) : option B :=
  match o with Some a => f a | None => None end.
Notation "'let*' p ':=' c 'in' b" := (bind c (fun p => b))
  (at level 10, p pattern, c at level 100, b at level 200).

(** ** Byte-level readers.  A parser consumes a prefix of a byte list. *)
Definition bytes := list Z.

Definition u1 (l : bytes) : option (Z * bytes) :=
  match l with b :: r => Some (b, r) | nil => None end.

Definition u2 (l : bytes) : option (Z * bytes) :=
  let* (a, l) := u1 l in let* (b, l) := u1 l in Some (a * 256 + b, l).

Definition u4 (l : bytes) : option (Z * bytes) :=
  let* (a, l) := u2 l in let* (b, l) := u2 l in Some (a * 65536 + b, l).

Definition s1 (z : Z) : Z := if z <? 128 then z else z - 256.
Definition s2 (z : Z) : Z := if z <? 32768 then z else z - 65536.
Definition s4 (z : Z) : Z := wrap32 z.

Fixpoint take (n : nat) (l : bytes) : option (bytes * bytes) :=
  match n with
  | O => Some (nil, l)
  | S k => match l with
           | b :: r => let* (xs, rest) := take k r in Some (b :: xs, rest)
           | nil => None
           end
  end.

(** Modified-UTF-8 bytes are kept byte-for-byte in a Rocq [string]
    (8-bit [ascii]); for ASCII names this is the name itself. *)
Definition bytes_to_string (bs : bytes) : string :=
  fold_right (fun b s => String (ascii_of_N (Z.to_N b)) s) EmptyString bs.

(** ** Constant pool (JVMS 4.4) *)
Inductive cp_entry : Type :=
| CPUtf8 (s : string)
| CPInt (z : Z) | CPFloat (bits : Z) | CPLong (z : Z) | CPDouble (bits : Z)
| CPClass (name : Z) | CPString (utf : Z)
| CPFieldref (cls nat_ : Z) | CPMethodref (cls nat_ : Z) | CPIMethodref (cls nat_ : Z)
| CPNameAndType (name desc : Z)
| CPMethodHandle (kind ref : Z) | CPMethodType (desc : Z)
| CPDynamic (bsm nat_ : Z) | CPInvokeDynamic (bsm nat_ : Z)
| CPModule (name : Z) | CPPackage (name : Z)
| CPUnusable.

Definition cp_entry1 (l : bytes) : option (cp_entry * bool * bytes) :=
  (* the bool says whether the entry takes two slots (long, double) *)
  let* (tag, l) := u1 l in
  if tag =? 1 then
    let* (n, l) := u2 l in let* (bs, l) := take (Z.to_nat n) l in
    Some (CPUtf8 (bytes_to_string bs), false, l)
  else if tag =? 3 then let* (z, l) := u4 l in Some (CPInt (s4 z), false, l)
  else if tag =? 4 then let* (z, l) := u4 l in Some (CPFloat z, false, l)
  else if tag =? 5 then
    let* (hi, l) := u4 l in let* (lo, l) := u4 l in
    Some (CPLong (wrap64 (hi * 2 ^ 32 + lo)), true, l)
  else if tag =? 6 then
    let* (hi, l) := u4 l in let* (lo, l) := u4 l in Some (CPDouble (hi * 2 ^ 32 + lo), true, l)
  else if tag =? 7 then let* (n, l) := u2 l in Some (CPClass n, false, l)
  else if tag =? 8 then let* (n, l) := u2 l in Some (CPString n, false, l)
  else if tag =? 9 then let* (a, l) := u2 l in let* (b, l) := u2 l in Some (CPFieldref a b, false, l)
  else if tag =? 10 then let* (a, l) := u2 l in let* (b, l) := u2 l in Some (CPMethodref a b, false, l)
  else if tag =? 11 then let* (a, l) := u2 l in let* (b, l) := u2 l in Some (CPIMethodref a b, false, l)
  else if tag =? 12 then let* (a, l) := u2 l in let* (b, l) := u2 l in Some (CPNameAndType a b, false, l)
  else if tag =? 15 then let* (a, l) := u1 l in let* (b, l) := u2 l in Some (CPMethodHandle a b, false, l)
  else if tag =? 16 then let* (a, l) := u2 l in Some (CPMethodType a, false, l)
  else if tag =? 17 then let* (a, l) := u2 l in let* (b, l) := u2 l in Some (CPDynamic a b, false, l)
  else if tag =? 18 then let* (a, l) := u2 l in let* (b, l) := u2 l in Some (CPInvokeDynamic a b, false, l)
  else if tag =? 19 then let* (a, l) := u2 l in Some (CPModule a, false, l)
  else if tag =? 20 then let* (a, l) := u2 l in Some (CPPackage a, false, l)
  else None.

(** [n] = number of slots still to read.  Result is in index order 1..count-1. *)
Fixpoint cp_entries (fuel : nat) (n : Z) (l : bytes) : option (list cp_entry * bytes) :=
  match fuel with
  | O => None
  | S k =>
    if n <=? 0 then Some (nil, l) else
    let* (e, two, l) := cp_entry1 l in
    if two then
      let* (es, l) := cp_entries k (n - 2) l in Some (e :: CPUnusable :: es, l)
    else
      let* (es, l) := cp_entries k (n - 1) l in Some (e :: es, l)
  end.

(** The pool with a dummy entry at index 0, so [nth i] is entry [i]. *)
Definition cp := list cp_entry.
Definition cp_get (c : cp) (i : Z) : option cp_entry :=
  if (i <=? 0) then None else nth_error c (Z.to_nat i).

Definition cp_utf8 (c : cp) (i : Z) : option string :=
  match cp_get c i with Some (CPUtf8 s) => Some s | _ => None end.
Definition cp_class (c : cp) (i : Z) : option string :=
  match cp_get c i with Some (CPClass n) => cp_utf8 c n | _ => None end.
Definition cp_nat (c : cp) (i : Z) : option (string * string) :=
  match cp_get c i with
  | Some (CPNameAndType n d) => let* a := cp_utf8 c n in let* b := cp_utf8 c d in Some (a, b)
  | _ => None
  end.
Definition cp_fieldref (c : cp) (i : Z) : option fieldref :=
  match cp_get c i with
  | Some (CPFieldref k nt) =>
      let* cn := cp_class c k in let* (n, d) := cp_nat c nt in
      Some {| fr_class := cn; fr_name := n; fr_desc := d |}
  | _ => None
  end.
Definition cp_methodref (c : cp) (i : Z) : option methodref :=
  match cp_get c i with
  | Some (CPMethodref k nt) =>
      let* cn := cp_class c k in let* (n, d) := cp_nat c nt in
      Some {| mr_class := cn; mr_name := n; mr_desc := d; mr_interface := false |}
  | Some (CPIMethodref k nt) =>
      let* cn := cp_class c k in let* (n, d) := cp_nat c nt in
      Some {| mr_class := cn; mr_name := n; mr_desc := d; mr_interface := true |}
  | _ => None
  end.

(** [ldc]/[ldc_w] (single-slot) and [ldc2_w] (long/double) constants. *)
Definition ldc_instr (c : cp) (i : Z) (wide2 : bool) : option instr :=
  match cp_get c i, wide2 with
  | Some (CPInt z), false => Some (Iconst z)
  | Some (CPFloat b), false => Some (Fconst b)
  | Some (CPString u), false => let* s := cp_utf8 c u in Some (Ldc (LdcString s))
  | Some (CPClass n), false => let* s := cp_utf8 c n in Some (Ldc (LdcClass s))
  | Some (CPMethodType d), false => let* s := cp_utf8 c d in Some (Ldc (LdcMethodType s))
  | Some (CPMethodHandle k r), false => Some (Ldc (LdcMethodHandle k r))
  | Some (CPDynamic b nt), _ => let* (n, d) := cp_nat c nt in Some (Ldc (LdcDynamic b n d))
  | Some (CPLong z), true => Some (Lconst z)
  | Some (CPDouble b), true => Some (Dconst b)
  | _, _ => None
  end.

(** ** Instruction decoding (JVMS 6.5) *)
Definition FLOAT_1 : Z := 1065353216.            (* 0x3f800000 *)
Definition FLOAT_2 : Z := 1073741824.            (* 0x40000000 *)
Definition DOUBLE_1 : Z := 4607182418800017408.  (* 0x3ff0000000000000 *)

Definition tkind_of (n : Z) : tkind :=
  if n =? 0 then KI else if n =? 1 then KL else if n =? 2 then KF else if n =? 3 then KD else KA.
Definition akind_of (n : Z) : akind :=
  if n =? 0 then AI else if n =? 1 then AL else if n =? 2 then AF else if n =? 3 then AD
  else if n =? 4 then AA else if n =? 5 then AB else if n =? 6 then AC else AS.
Definition binop_of (n : Z) : binop :=
  if n =? 0 then Add else if n =? 1 then Sub else if n =? 2 then Mul else if n =? 3 then Div
  else Rem.
Definition cond_of (n : Z) : cond :=
  if n =? 0 then CEq else if n =? 1 then CNe else if n =? 2 then CLt else if n =? 3 then CGe
  else if n =? 4 then CGt else CLe.
Definition conv_of (n : Z) : conv :=
  nth (Z.to_nat n) [I2L; I2F; I2D; L2I; L2F; L2D; F2I; F2L; F2D; D2I; D2L; D2F; I2B; I2C; I2S] I2L.

Fixpoint read_s4s (n : nat) (base : Z) (l : bytes) : option (list Z * bytes) :=
  match n with
  | O => Some (nil, l)
  | S k => let* (o, l) := u4 l in let* (os, l) := read_s4s k base l in Some ((base + s4 o) :: os, l)
  end.

Fixpoint read_pairs (n : nat) (base : Z) (l : bytes) : option (list (Z * Z) * bytes) :=
  match n with
  | O => Some (nil, l)
  | S k =>
      let* (m, l) := u4 l in let* (o, l) := u4 l in
      let* (ps, l) := read_pairs k base l in Some ((s4 m, base + s4 o) :: ps, l)
  end.

(** Decode the instruction at byte offset [p]; [l] starts right after the
    opcode byte [op].  Returns the instruction and the remaining bytes. *)
Definition decode1 (c : cp) (p op : Z) (l : bytes) : option (instr * bytes) :=
  let branch2 (mk : Z -> instr) := let* (o, l) := u2 l in Some (mk (p + s2 o), l) in
  if op =? 0 then Some (Nop, l)
  else if op =? 1 then Some (AconstNull, l)
  else if (2 <=? op) && (op <=? 8) then Some (Iconst (op - 3), l)
  else if op =? 9 then Some (Lconst 0, l)
  else if op =? 10 then Some (Lconst 1, l)
  else if op =? 11 then Some (Fconst 0, l)
  else if op =? 12 then Some (Fconst FLOAT_1, l)
  else if op =? 13 then Some (Fconst FLOAT_2, l)
  else if op =? 14 then Some (Dconst 0, l)
  else if op =? 15 then Some (Dconst DOUBLE_1, l)
  else if op =? 16 then let* (b, l) := u1 l in Some (Iconst (s1 b), l)
  else if op =? 17 then let* (b, l) := u2 l in Some (Iconst (s2 b), l)
  else if op =? 18 then let* (i, l) := u1 l in let* ins := ldc_instr c i false in Some (ins, l)
  else if op =? 19 then let* (i, l) := u2 l in let* ins := ldc_instr c i false in Some (ins, l)
  else if op =? 20 then let* (i, l) := u2 l in let* ins := ldc_instr c i true in Some (ins, l)
  else if (21 <=? op) && (op <=? 25) then let* (i, l) := u1 l in Some (Load (tkind_of (op - 21)) i, l)
  else if (26 <=? op) && (op <=? 45) then
    Some (Load (tkind_of ((op - 26) / 4)) ((op - 26) mod 4), l)
  else if (46 <=? op) && (op <=? 53) then Some (ALoadArr (akind_of (op - 46)), l)
  else if (54 <=? op) && (op <=? 58) then let* (i, l) := u1 l in Some (Store (tkind_of (op - 54)) i, l)
  else if (59 <=? op) && (op <=? 78) then
    Some (Store (tkind_of ((op - 59) / 4)) ((op - 59) mod 4), l)
  else if (79 <=? op) && (op <=? 86) then Some (AStoreArr (akind_of (op - 79)), l)
  else if op =? 87 then Some (Pop, l)
  else if op =? 88 then Some (Pop2, l)
  else if op =? 89 then Some (Dup, l)
  else if op =? 90 then Some (DupX1, l)
  else if op =? 91 then Some (DupX2, l)
  else if op =? 92 then Some (Dup2, l)
  else if op =? 93 then Some (Dup2X1, l)
  else if op =? 94 then Some (Dup2X2, l)
  else if op =? 95 then Some (Swap, l)
  else if (96 <=? op) && (op <=? 115) then
    let bo := binop_of ((op - 96) / 4) in
    let k := (op - 96) mod 4 in
    Some (if k =? 0 then IBin bo else if k =? 1 then LBin bo else if k =? 2 then FBin bo else DBin bo, l)
  else if op =? 116 then Some (INeg, l)
  else if op =? 117 then Some (LNeg, l)
  else if op =? 118 then Some (FNeg, l)
  else if op =? 119 then Some (DNeg, l)
  else if op =? 120 then Some (IBin Shl, l)
  else if op =? 121 then Some (LBin Shl, l)
  else if op =? 122 then Some (IBin Shr, l)
  else if op =? 123 then Some (LBin Shr, l)
  else if op =? 124 then Some (IBin Ushr, l)
  else if op =? 125 then Some (LBin Ushr, l)
  else if op =? 126 then Some (IBin And, l)
  else if op =? 127 then Some (LBin And, l)
  else if op =? 128 then Some (IBin Or, l)
  else if op =? 129 then Some (LBin Or, l)
  else if op =? 130 then Some (IBin Xor, l)
  else if op =? 131 then Some (LBin Xor, l)
  else if op =? 132 then let* (i, l) := u1 l in let* (k, l) := u1 l in Some (Iinc i (s1 k), l)
  else if (133 <=? op) && (op <=? 147) then Some (Conv (conv_of (op - 133)), l)
  else if op =? 148 then Some (Lcmp, l)
  else if op =? 149 then Some (FCmp Fcmpl, l)
  else if op =? 150 then Some (FCmp Fcmpg, l)
  else if op =? 151 then Some (FCmp Dcmpl, l)
  else if op =? 152 then Some (FCmp Dcmpg, l)
  else if (153 <=? op) && (op <=? 158) then branch2 (If (cond_of (op - 153)))
  else if (159 <=? op) && (op <=? 164) then branch2 (IfIcmp (cond_of (op - 159)))
  else if op =? 165 then branch2 (IfAcmp true)
  else if op =? 166 then branch2 (IfAcmp false)
  else if op =? 167 then branch2 Goto
  else if op =? 168 then branch2 Jsr
  else if op =? 169 then let* (i, l) := u1 l in Some (Ret i, l)
  else if op =? 170 then
    let pad := (4 - ((p + 1) mod 4)) mod 4 in
    let* (_, l) := take (Z.to_nat pad) l in
    let* (d, l) := u4 l in let* (lo, l) := u4 l in let* (hi, l) := u4 l in
    let lo := s4 lo in let hi := s4 hi in
    if hi <? lo then None else
    let* (ts, l) := read_s4s (Z.to_nat (hi - lo + 1)) p l in
    Some (Tableswitch (p + s4 d) lo hi ts, l)
  else if op =? 171 then
    let pad := (4 - ((p + 1) mod 4)) mod 4 in
    let* (_, l) := take (Z.to_nat pad) l in
    let* (d, l) := u4 l in let* (n, l) := u4 l in
    if s4 n <? 0 then None else
    let* (ps, l) := read_pairs (Z.to_nat (s4 n)) p l in
    Some (Lookupswitch (p + s4 d) ps, l)
  else if (172 <=? op) && (op <=? 176) then Some (Return (Some (tkind_of (op - 172))), l)
  else if op =? 177 then Some (Return None, l)
  else if (178 <=? op) && (op <=? 181) then
    let* (i, l) := u2 l in let* f := cp_fieldref c i in
    Some (if op =? 178 then Getstatic f else if op =? 179 then Putstatic f
          else if op =? 180 then Getfield f else Putfield f, l)
  else if (182 <=? op) && (op <=? 184) then
    let* (i, l) := u2 l in let* m := cp_methodref c i in
    Some (Invoke (if op =? 182 then InvVirtual else if op =? 183 then InvSpecial else InvStatic) m, l)
  else if op =? 185 then
    let* (i, l) := u2 l in let* (_, l) := u1 l in let* (_, l) := u1 l in
    let* m := cp_methodref c i in Some (Invoke InvInterface m, l)
  else if op =? 186 then
    let* (i, l) := u2 l in let* (_, l) := u2 l in
    match cp_get c i with
    | Some (CPInvokeDynamic b nt) => let* (n, d) := cp_nat c nt in Some (Invokedynamic b n d, l)
    | _ => None
    end
  else if op =? 187 then let* (i, l) := u2 l in let* s := cp_class c i in Some (New s, l)
  else if op =? 188 then let* (t, l) := u1 l in Some (Newarray t, l)
  else if op =? 189 then let* (i, l) := u2 l in let* s := cp_class c i in Some (Anewarray s, l)
  else if op =? 190 then Some (Arraylength, l)
  else if op =? 191 then Some (Athrow, l)
  else if op =? 192 then let* (i, l) := u2 l in let* s := cp_class c i in Some (Checkcast s, l)
  else if op =? 193 then let* (i, l) := u2 l in let* s := cp_class c i in Some (Instanceof s, l)
  else if op =? 194 then Some (Monitorenter, l)
  else if op =? 195 then Some (Monitorexit, l)
  else if op =? 196 then
    let* (op2, l) := u1 l in
    if op2 =? 132 then
      let* (i, l) := u2 l in let* (k, l) := u2 l in Some (Iinc i (s2 k), l)
    else if (21 <=? op2) && (op2 <=? 25) then let* (i, l) := u2 l in Some (Load (tkind_of (op2 - 21)) i, l)
    else if (54 <=? op2) && (op2 <=? 58) then let* (i, l) := u2 l in Some (Store (tkind_of (op2 - 54)) i, l)
    else if op2 =? 169 then let* (i, l) := u2 l in Some (Ret i, l)
    else None
  else if op =? 197 then
    let* (i, l) := u2 l in let* (d, l) := u1 l in let* s := cp_class c i in Some (Multianewarray s d, l)
  else if op =? 198 then branch2 (IfNull true)
  else if op =? 199 then branch2 (IfNull false)
  else if op =? 200 then let* (o, l) := u4 l in Some (Goto (p + s4 o), l)
  else if op =? 201 then let* (o, l) := u4 l in Some (Jsr (p + s4 o), l)
  else None.

Fixpoint decode_all (fuel : nat) (c : cp) (p : Z) (l : bytes) : option (list (pc * instr)) :=
  match l with
  | nil => Some nil
  | op :: r =>
    match fuel with
    | O => None
    | S k =>
      let* (i, r') := decode1 c p op r in
      let p' := p + 1 + Z.of_nat (length r) - Z.of_nat (length r') in
      let* rest := decode_all k c p' r' in
      Some ((p, i) :: rest)
    end
  end.

Definition decode (c : cp) (code : bytes) : option (list (pc * instr)) :=
  decode_all (S (length code)) c 0 code.

(** ** Attributes, fields, methods, class *)
Definition attribute := (string * bytes)%type.

Fixpoint attributes (n : nat) (c : cp) (l : bytes) : option (list attribute * bytes) :=
  match n with
  | O => Some (nil, l)
  | S k =>
      let* (ni, l) := u2 l in let* (len, l) := u4 l in let* (bs, l) := take (Z.to_nat len) l in
      let* name := cp_utf8 c ni in
      let* (rest, l) := attributes k c l in Some ((name, bs) :: rest, l)
  end.

Fixpoint handlers (n : nat) (c : cp) (l : bytes) : option (list handler * bytes) :=
  match n with
  | O => Some (nil, l)
  | S k =>
      let* (s, l) := u2 l in let* (e, l) := u2 l in let* (h, l) := u2 l in let* (t, l) := u2 l in
      let* ct := (if t =? 0 then Some None else let* nm := cp_class c t in Some (Some nm)) in
      let* (rest, l) := handlers k c l in
      Some ({| h_start := s; h_end := e; h_pc := h; h_catch := ct |} :: rest, l)
  end.

Definition parse_code (c : cp) (l : bytes) : option code :=
  let* (ms, l) := u2 l in let* (ml, l) := u2 l in let* (len, l) := u4 l in
  let* (bs, l) := take (Z.to_nat len) l in
  let* (nh, l) := u2 l in let* (hs, _) := handlers (Z.to_nat nh) c l in
  let* ins := decode c bs in
  Some {| c_max_stack := ms; c_max_locals := ml; c_length := len; c_instrs := ins; c_handlers := hs |}.

Fixpoint find_attr (name : string) (l : list attribute) : option bytes :=
  match l with
  | nil => None
  | (n, b) :: r => if String.eqb n name then Some b else find_attr name r
  end.

Record member := { mb_access : Z; mb_name : string; mb_desc : string; mb_attrs : list attribute }.

Fixpoint members (n : nat) (c : cp) (l : bytes) : option (list member * bytes) :=
  match n with
  | O => Some (nil, l)
  | S k =>
      let* (acc, l) := u2 l in let* (ni, l) := u2 l in let* (di, l) := u2 l in
      let* (na, l) := u2 l in let* (ats, l) := attributes (Z.to_nat na) c l in
      let* name := cp_utf8 c ni in let* desc := cp_utf8 c di in
      let* (rest, l) := members k c l in
      Some ({| mb_access := acc; mb_name := name; mb_desc := desc; mb_attrs := ats |} :: rest, l)
  end.

Definition to_method (c : cp) (m : member) : option method :=
  match find_attr "Code" (mb_attrs m) with
  | None => Some {| m_name := mb_name m; m_desc := mb_desc m; m_access := mb_access m; m_code := None |}
  | Some bs =>
      let* cd := parse_code c bs in
      Some {| m_name := mb_name m; m_desc := mb_desc m; m_access := mb_access m; m_code := Some cd |}
  end.

Fixpoint map_opt {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | nil => Some nil
  | a :: r => let* b := f a in let* bs := map_opt f r in Some (b :: bs)
  end.

Record classfile := {
  cf_major : Z;
  cf_cp : cp;
  cf_access : Z;
  cf_this : string;
  cf_super : option string;
  cf_interfaces : list string;
  cf_fields : list member;
  cf_methods : list method;
  cf_attrs : list attribute;      (** class attributes (BootstrapMethods, ...) *)
}.

Fixpoint u2s (n : nat) (l : bytes) : option (list Z * bytes) :=
  match n with
  | O => Some (nil, l)
  | S k => let* (x, l) := u2 l in let* (xs, l) := u2s k l in Some (x :: xs, l)
  end.

Definition parse_class (l : bytes) : option classfile :=
  let* (magic, l) := u4 l in
  if negb (magic =? 3405691582) then None else       (* 0xCAFEBABE *)
  let* (_minor, l) := u2 l in let* (major, l) := u2 l in
  let* (cpn, l) := u2 l in
  let* (es, l) := cp_entries (Z.to_nat cpn) (cpn - 1) l in
  let c := CPUnusable :: es in
  let* (acc, l) := u2 l in let* (thi, l) := u2 l in let* (sup, l) := u2 l in
  let* this := cp_class c thi in
  let* super := (if sup =? 0 then Some None else let* s := cp_class c sup in Some (Some s)) in
  let* (ni, l) := u2 l in let* (ifs, l) := u2s (Z.to_nat ni) l in
  let* ifnames := map_opt (cp_class c) ifs in
  let* (nf, l) := u2 l in let* (fs, l) := members (Z.to_nat nf) c l in
  let* (nm, l) := u2 l in let* (ms, l) := members (Z.to_nat nm) c l in
  let* meths := map_opt (to_method c) ms in
  let* (na, l) := u2 l in let* (ats, _) := attributes (Z.to_nat na) c l in
  Some {| cf_major := major; cf_cp := c; cf_access := acc; cf_this := this; cf_super := super;
          cf_interfaces := ifnames; cf_fields := fs; cf_methods := meths;
          cf_attrs := ats |}.

Fixpoint find_method_in (name desc : string) (ms : list method) : option method :=
  match ms with
  | nil => None
  | m :: r => if String.eqb (m_name m) name && String.eqb (m_desc m) desc then Some m
              else find_method_in name desc r
  end.

Definition find_method (cf : classfile) (name desc : string) : option method :=
  find_method_in name desc (cf_methods cf).

Definition load_method (bs : bytes) (name desc : string) : option method :=
  let* cf := parse_class bs in find_method cf name desc.

(** ** Modified UTF-8 (JVMS 4.4.7) to UTF-16 code units, for String constants. *)
Fixpoint mutf8_units (fuel : nat) (bs : list Z) : option (list Z) :=
  match fuel with
  | O => None
  | S k =>
    match bs with
    | nil => Some nil
    | b :: r =>
      if b <? 128 then
        (if b =? 0 then None else option_map (cons b) (mutf8_units k r))
      else if (Z.land b 224 =? 192) then
        match r with
        | b2 :: r2 => if Z.land b2 192 =? 128
                      then option_map (cons (Z.land b 31 * 64 + Z.land b2 63)) (mutf8_units k r2)
                      else None
        | _ => None
        end
      else if (Z.land b 240 =? 224) then
        match r with
        | b2 :: b3 :: r3 =>
            if (Z.land b2 192 =? 128) && (Z.land b3 192 =? 128)
            then option_map (cons (Z.land b 15 * 4096 + Z.land b2 63 * 64 + Z.land b3 63)) (mutf8_units k r3)
            else None
        | _ => None
        end
      else None
    end
  end.

Definition string_bytes (s : string) : list Z :=
  map (fun c => Z.of_N (Ascii.N_of_ascii c)) (list_ascii_of_string s).

(** UTF-16 units of a constant-pool Utf8 entry as stored by the decoder. *)
Definition utf8_units (s : string) : option (list Z) :=
  let bs := string_bytes s in mutf8_units (S (length bs)) bs.

Example mutf8_nul : mutf8_units 10 [97; 192; 128; 98] = Some [97; 0; 98].
Proof. reflexivity. Qed.
Example mutf8_3 : mutf8_units 10 [226; 130; 172] = Some [8364].   (* U+20AC EURO SIGN *)
Proof. reflexivity. Qed.

(** A BootstrapMethods entry: the method handle cp index and the argument cp indices. *)
Fixpoint bootstrap_entries (n : nat) (l : bytes) : option (list (Z * list Z) * bytes) :=
  match n with
  | O => Some (nil, l)
  | S k =>
      let* (mh, l) := u2 l in let* (na, l) := u2 l in let* (args, l) := u2s (Z.to_nat na) l in
      let* (rest, l) := bootstrap_entries k l in Some ((mh, args) :: rest, l)
  end.

Definition bootstrap_methods (cf : classfile) : option (list (Z * list Z)) :=
  match find_attr "BootstrapMethods" (cf_attrs cf) with
  | None => Some nil
  | Some bs => let* (n, l) := u2 bs in let* (es, _) := bootstrap_entries (Z.to_nat n) l in Some es
  end.

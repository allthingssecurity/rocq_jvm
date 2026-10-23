(** * JVM instructions (JVMS SE 21, chapter 6), after decoding.

    The decoder ([JVM.Loader.ClassFile]) turns the bytes of a [Code]
    attribute into a list of [(pc, instr)] pairs.  Decoding already
    - resolves constant-pool indices into the constant (for [ldc]) or into
      symbolic references (class / field / method names and descriptors);
    - turns relative branch offsets into absolute byte offsets;
    - folds the short forms ([iload_0], [iconst_3], ...) and [wide] into the
      general form.
    Every opcode of JVMS chapter 6 has a constructor here (so the decoder is
    total on valid class files); which ones have a semantics yet is listed in
    [JVM.Core.Semantics] and STATUS.md.  [jsr]/[ret]/[jsr_w] are decoded
    but class files of version >= 51 (javac --release 7 and later) never
    contain them; the interpreter rejects them. *)

From Stdlib Require Import ZArith String List.
From JVM.Core Require Import Int.

(** Type tags used by typed instructions. *)
Inductive tkind : Type := KI | KL | KF | KD | KA.
(** Array element kinds ([baload] serves byte and boolean arrays). *)
Inductive akind : Type := AI | AL | AF | AD | AA | AB | AC | AS.

Inductive conv : Type :=
| I2L | I2F | I2D | L2I | L2F | L2D | F2I | F2L | F2D | D2I | D2L | D2F
| I2B | I2C | I2S.

Inductive fcmp : Type := Fcmpl | Fcmpg | Dcmpl | Dcmpg.

Inductive invoke_kind : Type := InvVirtual | InvSpecial | InvStatic | InvInterface.

(** Symbolic references, as in the constant pool. *)
Record fieldref := { fr_class : string; fr_name : string; fr_desc : string }.
Record methodref := { mr_class : string; mr_name : string; mr_desc : string;
                      mr_interface : bool }.

(** Loadable constants of [ldc]/[ldc_w]/[ldc2_w] that are not numbers. *)
Inductive ldc_const : Type :=
| LdcString (s : string)
| LdcClass (name : string)
| LdcMethodType (desc : string)
| LdcMethodHandle (kind : Z) (target : Z)  (** raw cp index of the reference *)
| LdcDynamic (bsm : Z) (name desc : string).

Definition pc := Z.

Inductive instr : Type :=
| Nop
| AconstNull
| Iconst (n : Z)            (** iconst_<i>, bipush, sipush, ldc of an Integer *)
| Lconst (n : Z)            (** lconst_<l>, ldc2_w of a Long *)
| Fconst (bits : Z)         (** fconst_<f>, ldc of a Float: IEEE 754 binary32 bits *)
| Dconst (bits : Z)         (** dconst_<d>, ldc2_w of a Double: binary64 bits *)
| Ldc (c : ldc_const)
| Load (k : tkind) (idx : Z)
| Store (k : tkind) (idx : Z)
| ALoadArr (k : akind)       (** iaload, laload, ..., saload *)
| AStoreArr (k : akind)      (** iastore, ..., sastore *)
| Pop | Pop2 | Dup | DupX1 | DupX2 | Dup2 | Dup2X1 | Dup2X2 | Swap
| IBin (op : binop)          (** iadd ... ixor, ishl/ishr/iushr *)
| LBin (op : binop)          (** ladd ... lxor, lshl/lshr/lushr (shift distance is an int) *)
| FBin (op : binop)          (** fadd fsub fmul fdiv frem *)
| DBin (op : binop)          (** dadd dsub dmul ddiv drem *)
| INeg | LNeg | FNeg | DNeg
| Iinc (idx : Z) (c : Z)
| Conv (c : conv)
| Lcmp
| FCmp (c : fcmp)
| If (c : cond) (target : pc)          (** ifeq ... ifle: compare with 0 *)
| IfIcmp (c : cond) (target : pc)
| IfAcmp (eq : bool) (target : pc)     (** if_acmpeq (true) / if_acmpne (false) *)
| IfNull (isnull : bool) (target : pc) (** ifnull (true) / ifnonnull (false) *)
| Goto (target : pc)                   (** goto and goto_w *)
| Jsr (target : pc)                    (** jsr and jsr_w *)
| Ret (idx : Z)
| Tableswitch (default : pc) (low high : Z) (targets : list pc)
| Lookupswitch (default : pc) (pairs : list (Z * pc))
| Return (k : option tkind)            (** ireturn ... areturn; [None] = return *)
| Getstatic (f : fieldref) | Putstatic (f : fieldref)
| Getfield (f : fieldref)  | Putfield (f : fieldref)
| Invoke (k : invoke_kind) (m : methodref)
| Invokedynamic (bsm_index : Z) (name desc : string)
| New (cls : string)
| Newarray (atype : Z)                 (** 4=boolean 5=char 6=float 7=double 8=byte 9=short 10=int 11=long *)
| Anewarray (cls : string)
| Arraylength
| Athrow
| Checkcast (cls : string)
| Instanceof (cls : string)
| Monitorenter | Monitorexit
| Multianewarray (cls : string) (dims : Z).

(** Exception table entry of a [Code] attribute: handler for pcs in
    [start, end_); [catch_type = None] catches everything ([finally]). *)
Record handler := { h_start : pc; h_end : pc; h_pc : pc; h_catch : option string }.

Record code := {
  c_max_stack  : Z;
  c_max_locals : Z;
  c_length     : Z;                  (** code_length in bytes *)
  c_instrs     : list (pc * instr);  (** in increasing pc order *)
  c_handlers   : list handler;
}.

Record method := {
  m_name   : string;
  m_desc   : string;
  m_access : Z;             (** access_flags *)
  m_code   : option code;   (** [None] for abstract / native methods *)
}.

Definition ACC_STATIC : Z := 8.
Definition is_static (m : method) : bool := Z.testbit (m_access m) 3.

(** [fetch l p len] returns the instruction at byte offset [p] and the
    offset of the next instruction (the fall-through successor), which is the
    pc of the next list element, or [len] after the last instruction. *)
Fixpoint fetch (l : list (pc * instr)) (p : pc) (len : Z) : option (instr * pc) :=
  match l with
  | nil => None
  | (q, i) :: r =>
      if Z.eqb q p
      then Some (i, match r with (q', _) :: _ => q' | nil => len end)
      else fetch r p len
  end.

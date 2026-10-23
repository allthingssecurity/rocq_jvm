(** * Single-method small-step interpreter (Phase 1: int/long core).

    One call of [step] executes one instruction of the current method, per
    JVMS SE 21 chapter 6.  Instructions without a semantics yet return
    [Stuck "unsupported ..."]; a stuck run never produces a result, so no
    theorem of the form [run ... = RValue _] can hold for such code.
    Type mismatches on the operand stack or in locals (which the bytecode
    verifier excludes for valid class files) are also [Stuck].

    Phase 1 scope: int and long values, operand stack (including every form
    of dup/pop/swap), locals (with the category-2 two-slot layout), all
    int/long arithmetic, shifts, conversions and comparisons, all branches,
    [tableswitch]/[lookupswitch], [goto], returns, reference constants
    [aconst_null] and reference comparisons.  VM-thrown exceptions
    (ArithmeticException) end the method abruptly when no handler covers the
    pc; if a handler would catch it, the run is [Stuck] until Phase 2 adds
    the heap (the handler needs the exception object). *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

(** ** Values *)
Inductive value : Type :=
| VInt (z : Z)
| VLong (z : Z)
| VFloat (bits : Z)
| VDouble (bits : Z)
| VNull
| VRef (loc : Z)
| VTop.                 (** unusable local slot / upper half of a long or double *)

Definition cat2 (v : value) : bool :=
  match v with VLong _ | VDouble _ => true | _ => false end.

Definition slots (v : value) : Z := if cat2 v then 2 else 1.

Definition is_ref (v : value) : bool :=
  match v with VNull | VRef _ => true | _ => false end.

Definition ref_eq (a b : value) : bool :=
  match a, b with
  | VNull, VNull => true
  | VRef x, VRef y => Z.eqb x y
  | _, _ => false
  end.

(** ** Frames *)
Record frame := mkframe { f_pc : pc; f_stack : list value; f_locals : list value }.

Definition stack_slots (s : list value) : Z := fold_right (fun v n => slots v + n) 0 s.

(** Locals: list indexed from 0. *)
(** Indexing by [Z] directly (rather than through [Z.to_nat]) keeps
    symbolic execution with [cbn] simple. Negative indices find nothing. *)
Fixpoint nth_z {A} (l : list A) (i : Z) : option A :=
  match l with
  | nil => None
  | x :: r => if i =? 0 then Some x else nth_z r (i - 1)
  end.

Definition get_local (l : list value) (i : Z) : option value := nth_z l i.

Fixpoint set_nth (l : list value) (n : Z) (v : value) : option (list value) :=
  match l with
  | nil => None
  | x :: r => if n =? 0 then Some (v :: r) else option_map (cons x) (set_nth r (n - 1) v)
  end.

(** Storing into slot [i] (JVMS 2.6.1): a long/double occupies [i] and [i+1];
    if slot [i-1] held a long/double, that value becomes unusable. *)
Definition store_local (l : list value) (i : Z) (v : value) : option (list value) :=
  if i <? 0 then None else
  let l1 := match get_local l (i - 1) with
            | Some w => if cat2 w then set_nth l (i - 1) VTop else Some l
            | None => Some l
            end in
  match l1 with
  | None => None
  | Some l1 =>
    match set_nth l1 i v with
    | None => None
    | Some l2 => if cat2 v then set_nth l2 (i + 1) VTop else Some l2
    end
  end.

(** ** Outcome of one step *)
Inductive outcome : Type :=
| Normal (f : frame)
| Done (v : option value)        (** method returned (value after return-type narrowing) *)
| Throw (cls : string)           (** VM-thrown exception, internal class name *)
| Stuck (why : string).

Definition ArithmeticException := "java/lang/ArithmeticException"%string.

(** Narrowing of the [ireturn] operand by the method's return type
    (JVMS 6.5 ireturn, since Java SE 9). *)
Definition narrow_ret (rt : option jtype) (z : Z) : Z :=
  match rt with
  | Some TBool => Z.land z 1
  | Some TByte => i2b z
  | Some TChar => i2c z
  | Some TShort => i2s z
  | _ => z
  end.

Definition kind_ok (k : tkind) (v : value) : bool :=
  match k, v with
  | KI, VInt _ | KL, VLong _ | KF, VFloat _ | KD, VDouble _ => true
  | KA, (VNull | VRef _) => true
  | _, _ => false
  end.

Definition ret_ok (rt : option jtype) (k : option tkind) : bool :=
  match rt, k with
  | None, None => true
  | Some (TBool | TByte | TChar | TShort | TInt), Some KI => true
  | Some TLong, Some KL => true
  | Some TFloat, Some KF => true
  | Some TDouble, Some KD => true
  | Some (TRef _ | TArr _), Some KA => true
  | _, _ => false
  end.

Definition conv_int (c : conv) (v : value) : option value :=
  match c, v with
  | I2L, VInt a => Some (VLong (i2l a))
  | L2I, VLong a => Some (VInt (l2i a))
  | I2B, VInt a => Some (VInt (i2b a))
  | I2C, VInt a => Some (VInt (i2c a))
  | I2S, VInt a => Some (VInt (i2s a))
  | _, _ => None
  end.

Fixpoint lookup_pairs (k : Z) (ps : list (Z * pc)) : option pc :=
  match ps with
  | nil => None
  | (m, t) :: r => if Z.eqb k m then Some t else lookup_pairs k r
  end.

Definition switch_target (i : instr) (k : Z) : option pc :=
  match i with
  | Tableswitch d lo hi ts =>
      if (k <? lo) || (hi <? k) then Some d
      else nth_z ts (k - lo)
  | Lookupswitch d ps =>
      match lookup_pairs k ps with Some t => Some t | None => Some d end
  | _ => None
  end.

(** The stack manipulation instructions, in all their JVMS forms
    (head of the list = top of the stack = "value1" in JVMS). *)
Definition stackop (i : instr) (s : list value) : option (list value) :=
  match i, s with
  | Pop, v1 :: r => if cat2 v1 then None else Some r
  | Pop2, v1 :: r => if cat2 v1 then Some r else
                     match r with v2 :: r' => if cat2 v2 then None else Some r' | _ => None end
  | Dup, v1 :: r => if cat2 v1 then None else Some (v1 :: v1 :: r)
  | DupX1, v1 :: v2 :: r => if cat2 v1 || cat2 v2 then None else Some (v1 :: v2 :: v1 :: r)
  | DupX2, v1 :: v2 :: r =>
      if cat2 v1 then None
      else if cat2 v2 then Some (v1 :: v2 :: v1 :: r)                 (* form 2 *)
      else match r with
           | v3 :: r' => if cat2 v3 then None else Some (v1 :: v2 :: v3 :: v1 :: r') (* form 1 *)
           | _ => None
           end
  | Dup2, v1 :: r =>
      if cat2 v1 then Some (v1 :: v1 :: r)                            (* form 2 *)
      else match r with
           | v2 :: r' => if cat2 v2 then None else Some (v1 :: v2 :: v1 :: v2 :: r') (* form 1 *)
           | _ => None
           end
  | Dup2X1, v1 :: v2 :: r =>
      if cat2 v1 then (if cat2 v2 then None else Some (v1 :: v2 :: v1 :: r))   (* form 2 *)
      else if cat2 v2 then None
      else match r with
           | v3 :: r' => if cat2 v3 then None else Some (v1 :: v2 :: v3 :: v1 :: v2 :: r') (* form 1 *)
           | _ => None
           end
  | Dup2X2, v1 :: v2 :: r =>
      if cat2 v1 then
        if cat2 v2 then Some (v1 :: v2 :: v1 :: r)                    (* form 4 *)
        else match r with
             | v3 :: r' => if cat2 v3 then None else Some (v1 :: v2 :: v3 :: v1 :: r') (* form 2 *)
             | _ => None
             end
      else if cat2 v2 then None
      else match r with
           | v3 :: r' =>
               if cat2 v3 then Some (v1 :: v2 :: v3 :: v1 :: v2 :: r') (* form 3 *)
               else match r' with
                    | v4 :: r'' => if cat2 v4 then None
                                   else Some (v1 :: v2 :: v3 :: v4 :: v1 :: v2 :: r'') (* form 1 *)
                    | _ => None
                    end
           | _ => None
           end
  | Swap, v1 :: v2 :: r => if cat2 v1 || cat2 v2 then None else Some (v2 :: v1 :: r)
  | _, _ => None
  end.

Definition is_stackop (i : instr) : bool :=
  match i with Pop | Pop2 | Dup | DupX1 | DupX2 | Dup2 | Dup2X1 | Dup2X2 | Swap => true | _ => false end.

(** ** One step *)
Definition step (c : code) (rt : option jtype) (f : frame) : outcome :=
  match fetch (c_instrs c) (f_pc f) (c_length c) with
  | None => Stuck "no instruction at pc"
  | Some (i, nx) =>
    let st := f_stack f in
    let lv := f_locals f in
    let go s := Normal (mkframe nx s lv) in
    let jump t s := Normal (mkframe t s lv) in
    if is_stackop i then
      match stackop i st with Some s => go s | None => Stuck "stack shape" end
    else
    match i, st with
    | Nop, _ => go st
    | AconstNull, _ => go (VNull :: st)
    | Iconst n, _ => go (VInt n :: st)
    | Lconst n, _ => go (VLong n :: st)
    | Load k n, _ =>
        match get_local lv n with
        | Some v => if kind_ok k v then go (v :: st) else Stuck "load: wrong local type"
        | None => Stuck "load: bad index"
        end
    | Store k n, v :: r =>
        if kind_ok k v then
          match store_local lv n v with
          | Some lv' => Normal (mkframe nx r lv')
          | None => Stuck "store: bad index"
          end
        else Stuck "store: wrong operand type"
    | IBin op, VInt b :: VInt a :: r =>
        match op with
        | Add | Sub | Mul | Div | Rem | Shl | Shr | Ushr | And | Or | Xor =>
          match iarith op a b with
          | Some z => go (VInt z :: r)
          | None => Throw ArithmeticException
          end
        end
    | LBin op, VInt b :: VLong a :: r =>
        match op with
        | Shl | Shr | Ushr =>
            match larith op a b with Some z => go (VLong z :: r) | None => Stuck "lshift" end
        | _ => Stuck "long op: wrong operand types"
        end
    | LBin op, VLong b :: VLong a :: r =>
        match op with
        | Shl | Shr | Ushr => Stuck "long shift: distance must be int"
        | _ =>
          match larith op a b with
          | Some z => go (VLong z :: r)
          | None => Throw ArithmeticException
          end
        end
    | INeg, VInt a :: r => go (VInt (ineg a) :: r)
    | LNeg, VLong a :: r => go (VLong (lneg a) :: r)
    | Iinc n k, _ =>
        match get_local lv n with
        | Some (VInt a) =>
            match store_local lv n (VInt (iinc a k)) with
            | Some lv' => Normal (mkframe nx st lv')
            | None => Stuck "iinc: bad index"
            end
        | _ => Stuck "iinc: local not int"
        end
    | Conv cv, v :: r =>
        match conv_int cv v with
        | Some w => go (w :: r)
        | None => Stuck "conversion unsupported or wrong operand"
        end
    | Lcmp, VLong b :: VLong a :: r => go (VInt (lcmp a b) :: r)
    | If cnd t, VInt a :: r => if cond_holds cnd a 0 then jump t r else go r
    | IfIcmp cnd t, VInt b :: VInt a :: r => if cond_holds cnd a b then jump t r else go r
    | IfAcmp eq t, b :: a :: r =>
        if is_ref a && is_ref b then
          if Bool.eqb (ref_eq a b) eq then jump t r else go r
        else Stuck "if_acmp: not references"
    | IfNull isn t, a :: r =>
        if is_ref a then
          if Bool.eqb (ref_eq a VNull) isn then jump t r else go r
        else Stuck "ifnull: not a reference"
    | Goto t, _ => jump t st
    | (Tableswitch _ _ _ _ | Lookupswitch _ _), VInt k :: r =>
        match switch_target i k with
        | Some t => jump t r
        | None => Stuck "switch: bad table"
        end
    | Return None, _ => if ret_ok rt None then Done None else Stuck "return: wrong kind"
    | Return (Some k), v :: _ =>
        if ret_ok rt (Some k) && kind_ok k v then
          match v with
          | VInt z => Done (Some (VInt (narrow_ret rt z)))
          | _ => Done (Some v)
          end
        else Stuck "return: wrong kind"
    | _, _ => Stuck "unsupported instruction or operand stack mismatch"
    end
  end.

(** ** Exception dispatch for VM-thrown exceptions (Phase 1). *)
(** Superclasses of the exceptions the Phase 1 core can throw. *)
Definition builtin_supers (cls : string) : list string :=
  if String.eqb cls ArithmeticException then
    [ArithmeticException; "java/lang/RuntimeException"; "java/lang/Exception";
     "java/lang/Throwable"]%string
  else [cls].

Definition handler_matches (cls : string) (p : pc) (h : handler) : bool :=
  (h_start h <=? p) && (p <? h_end h) &&
  match h_catch h with
  | None => true
  | Some c => existsb (String.eqb c) (builtin_supers cls)
  end.

(** ** Runs *)
Inductive result : Type :=
| RValue (v : option value)
| RExc (cls : string)
| RStuck (why : string)
| ROutOfFuel.

Fixpoint run (fuel : nat) (c : code) (rt : option jtype) (f : frame) : result :=
  match fuel with
  | O => ROutOfFuel
  | S n =>
    match step c rt f with
    | Normal f' =>
        if stack_slots (f_stack f') <=? c_max_stack c then run n c rt f'
        else RStuck "operand stack overflow (max_stack)"
    | Done v => RValue v
    | Throw cls =>
        if existsb (handler_matches cls (f_pc f)) (c_handlers c)
        then RStuck "exception handler needs the heap (Phase 2)"
        else RExc cls
    | Stuck why => RStuck why
    end
  end.

(** Fuel monotonicity: once a run finishes, more fuel gives the same result. *)
Lemma run_mono : forall n c rt f r,
  run n c rt f = r -> r <> ROutOfFuel -> forall m, (n <= m)%nat -> run m c rt f = r.
Proof.
  induction n as [|n IH]; intros c rt f r H Hr m Hm.
  - simpl in H. subst. congruence.
  - destruct m as [|m]; [lia|]. simpl in *.
    destruct (step c rt f) as [f0| | |]; auto.
    destruct (stack_slots (f_stack f0) <=? c_max_stack c); auto.
    eapply IH; eauto; lia.
Qed.

(** ** Method entry *)
Definition arg_ok (t : jtype) (v : value) : bool :=
  match t, v with
  | (TBool | TByte | TChar | TShort | TInt), VInt z => in_rangeb 32 z
  | TLong, VLong z => in_rangeb 64 z
  | TFloat, VFloat _ | TDouble, VDouble _ => true
  | (TRef _ | TArr _), (VNull | VRef _) => true
  | _, _ => false
  end.

(** Lay out arguments in locals: category-2 values take two slots. *)
Fixpoint layout (vs : list value) : list value :=
  match vs with
  | nil => nil
  | v :: r => if cat2 v then v :: VTop :: layout r else v :: layout r
  end.

Definition init_frame (c : code) (vs : list value) : option frame :=
  let l := layout vs in
  let n := Z.of_nat (length l) in
  if c_max_locals c <? n then None
  else Some (mkframe 0 nil (l ++ repeat VTop (Z.to_nat (c_max_locals c - n)))).

(** Invoke a static method on argument values, with [fuel] steps. *)
Definition invoke_static (fuel : nat) (m : method) (args : list value) : result :=
  match m_code m, parse_mdesc (m_desc m) with
  | Some c, Some (ps, rt) =>
      if negb (is_static m) then RStuck "not a static method" else
      if negb (Nat.eqb (length ps) (length args)) then RStuck "arity" else
      if negb (forallb (fun p => arg_ok (fst p) (snd p)) (combine ps args)) then RStuck "argument types"
      else match init_frame c args with
           | Some f => run fuel c rt f
           | None => RStuck "max_locals too small for arguments"
           end
  | None, _ => RStuck "no code (abstract or native)"
  | _, None => RStuck "bad descriptor"
  end.

Lemma invoke_static_mono : forall n m args r,
  invoke_static n m args = r -> r <> ROutOfFuel ->
  forall n', (n <= n')%nat -> invoke_static n' m args = r.
Proof.
  intros n m args r H Hr n' Hn. unfold invoke_static in *.
  destruct (m_code m), (parse_mdesc (m_desc m)) as [[ps rt]|]; auto.
  destruct (negb (is_static m)); auto.
  destruct (negb (Nat.eqb (length ps) (length args))); auto.
  destruct (negb (forallb _ _)); auto.
  destruct (init_frame c args); auto.
  eapply run_mono; eauto.
Qed.

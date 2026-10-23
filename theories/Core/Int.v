(** * JVM integral arithmetic (JVMS SE 21, chapter 2.3 and chapter 6).

    Values of type [int] and [long] are represented as mathematical integers
    [Z] that are kept in the signed two's-complement range of their width:
    [int]  in [-2^31, 2^31),  [long] in [-2^63, 2^63).
    Every operation computes the exact mathematical result and then wraps it
    with [wrap n], which is "reduce modulo 2^n and reinterpret as signed".
    This is precisely the JVMS rule "the result is the low-order n bits of
    the true mathematical result, in two's-complement format".

    Division and remainder round toward zero ([Z.quot], [Z.rem]); a zero
    divisor yields [None] (the interpreter turns it into an
    [ArithmeticException]).  [Integer.MIN_VALUE / -1] overflows to
    [Integer.MIN_VALUE] and [Integer.MIN_VALUE % -1] is [0], as required by
    JVMS 6.5 idiv/irem (likewise for long).

    Shift distances are masked: low 5 bits for int shifts, low 6 bits for
    long shifts (JVMS 6.5 ishl/ishr/iushr/lshl/lshr/lushr). *)

From Stdlib Require Import ZArith Lia.
Open Scope bool_scope.
Open Scope Z_scope.

(** ** Wrapping to a signed n-bit range *)

Definition wrap (n : Z) (z : Z) : Z :=
  let m := z mod 2 ^ n in
  if m <? 2 ^ (n - 1) then m else m - 2 ^ n.

Definition wrap32 := wrap 32.
Definition wrap64 := wrap 64.
Definition wrap16 := wrap 16.
Definition wrap8  := wrap 8.

Definition INT_MIN : Z := - 2 ^ 31.
Definition INT_MAX : Z := 2 ^ 31 - 1.
Definition LONG_MIN : Z := - 2 ^ 63.
Definition LONG_MAX : Z := 2 ^ 63 - 1.

Definition in_range (n z : Z) : Prop := - 2 ^ (n - 1) <= z < 2 ^ (n - 1).
Definition in_int  := in_range 32.
Definition in_long := in_range 64.

Definition in_rangeb (n z : Z) : bool := (- 2 ^ (n - 1) <=? z) && (z <? 2 ^ (n - 1)).

Lemma wrap_range : forall n z, 0 < n -> in_range n (wrap n z).
Proof.
  intros n z Hn. unfold wrap, in_range.
  assert (H2n : 2 ^ n = 2 * 2 ^ (n - 1)).
  { replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.pow_succ_r; lia. }
  assert (Hpos : 0 < 2 ^ (n - 1)) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.mod_pos_bound z (2 ^ n)) as Hb.
  destruct (z mod 2 ^ n <? 2 ^ (n - 1)) eqn:E;
    [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma wrap_id : forall n z, 0 < n -> in_range n z -> wrap n z = z.
Proof.
  intros n z Hn [Hlo Hhi]. unfold wrap.
  assert (H2n : 2 ^ n = 2 * 2 ^ (n - 1)).
  { replace n with (Z.succ (n - 1)) at 1 by lia. rewrite Z.pow_succ_r; lia. }
  assert (Hpos : 0 < 2 ^ (n - 1)) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.le_gt_cases 0 z) as [Hz | Hz].
  - rewrite Z.mod_small by lia.
    replace (z <? 2 ^ (n - 1)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - assert (Hm : z mod 2 ^ n = z + 2 ^ n).
    { rewrite <- (Z.mod_small (z + 2 ^ n) (2 ^ n)) by lia.
      rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia.
      rewrite Z.add_0_r. reflexivity. }
    rewrite Hm. replace (z + 2 ^ n <? 2 ^ (n - 1)) with false by (symmetry; apply Z.ltb_ge; lia).
    lia.
Qed.

Lemma wrap32_range : forall z, in_int (wrap32 z).
Proof. intros; apply wrap_range; lia. Qed.
Lemma wrap64_range : forall z, in_long (wrap64 z).
Proof. intros; apply wrap_range; lia. Qed.
Lemma wrap32_id : forall z, in_int z -> wrap32 z = z.
Proof. intros; apply wrap_id; auto; lia. Qed.
Lemma wrap64_id : forall z, in_long z -> wrap64 z = z.
Proof. intros; apply wrap_id; auto; lia. Qed.

Lemma in_rangeb_spec : forall n z, in_rangeb n z = true <-> in_range n z.
Proof.
  intros. unfold in_rangeb, in_range. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto.
Qed.

(** ** Binary operators shared by [int] and [long] (JVMS 6.5) *)

Inductive binop : Type :=
| Add | Sub | Mul | Div | Rem | Shl | Shr | Ushr | And | Or | Xor.

(** Generic n-bit operation; [None] means "ArithmeticException: / by zero".
    For shifts the second operand is the (int) shift distance, masked to the
    low [log2 n] bits: [n - 1] is 31 or 63, i.e. the mask 0x1f or 0x3f. *)
Definition arith (n : Z) (op : binop) (a b : Z) : option Z :=
  match op with
  | Add => Some (wrap n (a + b))
  | Sub => Some (wrap n (a - b))
  | Mul => Some (wrap n (a * b))
  | Div => if b =? 0 then None else Some (wrap n (Z.quot a b))
  | Rem => if b =? 0 then None else Some (wrap n (Z.rem a b))
  | Shl => Some (wrap n (Z.shiftl a (Z.land b (n - 1))))
  | Shr => Some (wrap n (Z.shiftr a (Z.land b (n - 1))))
  | Ushr => Some (wrap n (Z.shiftr (a mod 2 ^ n) (Z.land b (n - 1))))
  | And => Some (wrap n (Z.land a b))
  | Or  => Some (wrap n (Z.lor a b))
  | Xor => Some (wrap n (Z.lxor a b))
  end.

Definition iarith := arith 32.
Definition larith := arith 64.

Definition ineg (a : Z) : Z := wrap32 (- a).
Definition lneg (a : Z) : Z := wrap64 (- a).

(** [iinc]: the constant is a sign-extended byte or (with [wide]) short. *)
Definition iinc (a c : Z) : Z := wrap32 (a + c).

(** ** Conversions (JVMS 6.5 i2l, l2i, i2b, i2c, i2s) *)
Definition i2l (a : Z) : Z := a.
Definition l2i (a : Z) : Z := wrap32 a.
Definition i2b (a : Z) : Z := wrap8 a.
Definition i2c (a : Z) : Z := a mod 2 ^ 16.
Definition i2s (a : Z) : Z := wrap16 a.

(** [lcmp] (JVMS 6.5): 1, 0 or -1. *)
Definition lcmp (a b : Z) : Z :=
  match Z.compare a b with Gt => 1 | Eq => 0 | Lt => -1 end.

(** ** Conditions of the [if<cond>] and [if_icmp<cond>] instructions *)
Inductive cond : Type := CEq | CNe | CLt | CGe | CGt | CLe.

Definition cond_holds (c : cond) (a b : Z) : bool :=
  match c with
  | CEq => a =? b
  | CNe => negb (a =? b)
  | CLt => a <? b
  | CGe => b <=? a
  | CGt => b <? a
  | CLe => a <=? b
  end.

(** ** Range lemmas: every operation yields a value of its width *)

Lemma arith_range : forall n op a b r, 0 < n -> arith n op a b = Some r -> in_range n r.
Proof.
  intros n op a b r Hn H; destruct op; simpl in H;
  repeat match type of H with
         | context [if ?c then _ else _] => destruct c
         end;
  inversion H; subst; apply wrap_range; auto.
Qed.

Lemma iarith_range : forall op a b r, iarith op a b = Some r -> in_int r.
Proof. intros; eapply arith_range; eauto; lia. Qed.
Lemma larith_range : forall op a b r, larith op a b = Some r -> in_long r.
Proof. intros; eapply arith_range; eauto; lia. Qed.

Lemma i2c_range : forall a, in_int (i2c a).
Proof.
  intros a. unfold i2c, in_int, in_range.
  pose proof (Z.mod_pos_bound a (2 ^ 16)). simpl in *. lia.
Qed.

Lemma lcmp_range : forall a b, in_int (lcmp a b).
Proof. intros; unfold lcmp, in_int, in_range; destruct (Z.compare a b); simpl; lia. Qed.

Lemma in_int_in_long : forall z, in_int z -> in_long z.
Proof. unfold in_int, in_long, in_range; simpl; lia. Qed.

(** Sanity checks of the corner cases named in the JVMS (checked by computation). *)
Example idiv_min_minus1 : iarith Div INT_MIN (-1) = Some INT_MIN. Proof. reflexivity. Qed.
Example irem_min_minus1 : iarith Rem INT_MIN (-1) = Some 0. Proof. reflexivity. Qed.
Example idiv_zero : iarith Div 7 0 = None. Proof. reflexivity. Qed.
Example idiv_trunc : iarith Div (-7) 2 = Some (-3). Proof. reflexivity. Qed.
Example irem_sign : iarith Rem (-7) 2 = Some (-1). Proof. reflexivity. Qed.
Example ishl_mask : iarith Shl 1 33 = Some 2. Proof. reflexivity. Qed.
Example iushr_neg : iarith Ushr (-1) 28 = Some 15. Proof. reflexivity. Qed.
Example ishr_neg : iarith Shr (-16) 2 = Some (-4). Proof. reflexivity. Qed.
Example iadd_wrap : iarith Add INT_MAX 1 = Some INT_MIN. Proof. reflexivity. Qed.
Example ldiv_min_minus1 : larith Div LONG_MIN (-1) = Some LONG_MIN. Proof. reflexivity. Qed.
Example lshl_mask : larith Shl 1 65 = Some 2. Proof. reflexivity. Qed.
Example lushr_neg : larith Ushr (-1) 60 = Some 15. Proof. reflexivity. Qed.
Example i2b_ex : i2b 200 = -56. Proof. reflexivity. Qed.
Example i2c_ex : i2c (-1) = 65535. Proof. reflexivity. Qed.
Example i2s_ex : i2s 40000 = -25536. Proof. reflexivity. Qed.
Example l2i_ex : l2i (2 ^ 32 + 5) = 5. Proof. reflexivity. Qed.

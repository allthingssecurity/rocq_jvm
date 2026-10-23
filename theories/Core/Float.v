(** * JVM floating-point arithmetic (JVMS SE 21, chapters 2.3.2, 2.8 and 6.5).

    Values of type [float] and [double] are represented by their IEEE 754
    bit patterns, as mathematical integers [Z] in the unsigned range of the
    format: binary32 values in [0, 2^32), binary64 values in [0, 2^64).
    (Inputs outside that range are reduced to their low 32 / 64 bits.)

    Since Java SE 17 (JEP 306) every floating-point operation is "strict":
    there is a single value set and every operation rounds its exact result
    once, to nearest, ties to even, with gradual underflow and overflow to
    infinity (JVMS 2.8).  That is what this file implements, for a generic
    binary format [fmt] instantiated to binary32 and binary64:

    - an operand is decoded to [NaN], [Inf s] or [Fin s m e], the latter
      meaning the exact rational (-1)^s * m * 2^e (with [m >= 0]);
    - the exact result is computed as an integer times a power of two
      (division: a quotient with enough extra bits plus a sticky bit);
    - a single function [round] produces the result bit pattern.

    NaN results: the JVMS does not specify NaN payloads; every operation
    here returns the canonical quiet NaN (0x7fc00000 / 0x7ff8000000000000),
    except [fneg]/[dneg], which flip the sign bit of their operand whatever
    it is.  Clients that compare against a real JVM must canonicalise NaNs
    on the JVM side (Float.floatToIntBits / Double.doubleToLongBits).

    Results of conversions to [int]/[long] and of comparisons follow the
    signed [Z] convention of [JVM.Core.Int]. *)

From Stdlib Require Import ZArith Lia Bool.
From JVM.Core Require Import Int.
Open Scope bool_scope.
Open Scope Z_scope.

(** ** Formats *)

Record fmt : Type := { mbits : Z;  (** stored significand (fraction) bits *)
                       ebits : Z } (** exponent bits *).

Definition binary32 : fmt := {| mbits := 23; ebits := 8 |}.
Definition binary64 : fmt := {| mbits := 52; ebits := 11 |}.

(** [pow2 n] is [2 ^ n] for [n >= 0], computed by shifting. *)
Definition pow2 (n : Z) : Z := Z.shiftl 1 n.

Definition width (f : fmt) : Z := mbits f + ebits f + 1.
Definition bias (f : fmt) : Z := pow2 (ebits f - 1) - 1.
(** The all-ones biased exponent (infinities and NaNs). *)
Definition emax_biased (f : fmt) : Z := pow2 (ebits f) - 1.
(** Exponent of the unit in the last place of subnormals (and of the
    smallest normal binade): -149 for binary32, -1074 for binary64. *)
Definition emin_ulp (f : fmt) : Z := 1 - bias f - mbits f.

(** ** Decoding *)

Definition norm (f : fmt) (x : Z) : Z := Z.land x (Z.ones (width f)).
Definition sign_bit (f : fmt) (x : Z) : bool := Z.testbit x (width f - 1).
Definition biased_exp (f : fmt) (x : Z) : Z :=
  Z.land (Z.shiftr x (mbits f)) (Z.ones (ebits f)).
Definition fraction (f : fmt) (x : Z) : Z := Z.land x (Z.ones (mbits f)).

Inductive fval : Type :=
| NaN
| Inf (s : bool)
| Fin (s : bool) (m e : Z).  (** (-1)^s * m * 2^e, [m >= 0] *)

Definition decode (f : fmt) (x : Z) : fval :=
  let s := sign_bit f x in
  let be := biased_exp f x in
  let fr := fraction f x in
  if be =? emax_biased f then (if fr =? 0 then Inf s else NaN)
  else if be =? 0 then Fin s fr (emin_ulp f)
  else Fin s (fr + pow2 (mbits f)) (be - 1 + emin_ulp f).

(** ** Classification *)

Definition is_nan (f : fmt) (x : Z) : bool :=
  (biased_exp f x =? emax_biased f) && negb (fraction f x =? 0).
Definition is_inf (f : fmt) (x : Z) : bool :=
  (biased_exp f x =? emax_biased f) && (fraction f x =? 0).
Definition is_zero (f : fmt) (x : Z) : bool :=
  (biased_exp f x =? 0) && (fraction f x =? 0).
Definition is_subnormal (f : fmt) (x : Z) : bool :=
  (biased_exp f x =? 0) && negb (fraction f x =? 0).
Definition is_normal (f : fmt) (x : Z) : bool :=
  negb (biased_exp f x =? 0) && negb (biased_exp f x =? emax_biased f).
Definition is_finite (f : fmt) (x : Z) : bool :=
  negb (biased_exp f x =? emax_biased f).

(** ** Encoding *)

Definition sign_val (f : fmt) (s : bool) : Z := if s then pow2 (width f - 1) else 0.
Definition zero_bits (f : fmt) (s : bool) : Z := sign_val f s.
Definition inf_bits (f : fmt) (s : bool) : Z := sign_val f s + emax_biased f * pow2 (mbits f).
Definition qnan (f : fmt) : Z := emax_biased f * pow2 (mbits f) + pow2 (mbits f - 1).

Definition canon (f : fmt) (x : Z) : Z := if is_nan f x then qnan f else norm f x.

(** ** Rounding *)

(** [shr_rne m k] is [m / 2^k] rounded to nearest, ties to even
    (for [m >= 0], [k > 0]). *)
Definition shr_rne (m k : Z) : Z :=
  let q := Z.shiftr m k in
  let r := m - Z.shiftl q k in
  let half := pow2 (k - 1) in
  if (half <? r) || ((r =? half) && Z.odd q) then q + 1 else q.

(** [round f s m e] is the bit pattern of the format-[f] number nearest
    to (-1)^s * m * 2^e (ties to even), for [m >= 0]: the ulp exponent [q]
    is that of a [mbits f + 1]-bit significand, but never below [emin_ulp f]
    (gradual underflow); the significand is rounded first, a carry out of
    the significand bumps [q], and an exponent beyond the largest finite
    binade gives infinity (overflow). An exact zero gives a zero of sign [s]. *)
Definition round (f : fmt) (s : bool) (m e : Z) : Z :=
  if m <=? 0 then zero_bits f s else
  let q0 := Z.max (Z.log2 m + e - mbits f) (emin_ulp f) in
  let mq0 := if q0 <=? e then Z.shiftl m (e - q0) else shr_rne m (q0 - e) in
  let '(mq, q) := if mq0 =? pow2 (mbits f + 1) then (pow2 (mbits f), q0 + 1)
                  else (mq0, q0) in
  if mq <? pow2 (mbits f) then sign_val f s + mq (* subnormal, or zero *)
  else
    let be := q - emin_ulp f + 1 in
    if emax_biased f <=? be then inf_bits f s
    else sign_val f s + be * pow2 (mbits f) + (mq - pow2 (mbits f)).

(** ** Arithmetic *)

Definition neg (f : fmt) (x : Z) : Z := Z.lxor x (pow2 (width f - 1)).

Definition signed (s : bool) (m : Z) : Z := if s then - m else m.

Definition add (f : fmt) (x y : Z) : Z :=
  match decode f x, decode f y with
  | NaN, _ | _, NaN => qnan f
  | Inf sx, Inf sy => if Bool.eqb sx sy then inf_bits f sx else qnan f
  | Inf sx, Fin _ _ _ => inf_bits f sx
  | Fin _ _ _, Inf sy => inf_bits f sy
  | Fin sx mx ex, Fin sy my ey =>
      let e := Z.min ex ey in
      let t := signed sx (Z.shiftl mx (ex - e)) + signed sy (Z.shiftl my (ey - e)) in
      (* an exact zero sum is +0, except (-0) + (-0) = -0 (round to nearest) *)
      if t =? 0 then zero_bits f (sx && sy)
      else round f (t <? 0) (Z.abs t) e
  end.

Definition sub (f : fmt) (x y : Z) : Z := add f x (neg f y).

Definition mul (f : fmt) (x y : Z) : Z :=
  match decode f x, decode f y with
  | NaN, _ | _, NaN => qnan f
  | Inf sx, Inf sy => inf_bits f (xorb sx sy)
  | Inf sx, Fin sy my _ => if my =? 0 then qnan f else inf_bits f (xorb sx sy)
  | Fin sx mx _, Inf sy => if mx =? 0 then qnan f else inf_bits f (xorb sx sy)
  | Fin sx mx ex, Fin sy my ey => round f (xorb sx sy) (mx * my) (ex + ey)
  end.

(** Division: [mx * 2^k / my] has at least [mbits f + 6] bits (as
    [mx >= 1] and [my < 2^(mbits f + 1)]), so after appending a sticky bit
    for a non-zero remainder the rounding of [2q + sticky] at scale
    [2^(ex-ey-k-1)] is the rounding of the exact quotient. *)
Definition div (f : fmt) (x y : Z) : Z :=
  match decode f x, decode f y with
  | NaN, _ | _, NaN => qnan f
  | Inf _, Inf _ => qnan f
  | Inf sx, Fin sy _ _ => inf_bits f (xorb sx sy)
  | Fin sx _ _, Inf sy => zero_bits f (xorb sx sy)
  | Fin sx mx ex, Fin sy my ey =>
      if my =? 0 then (if mx =? 0 then qnan f else inf_bits f (xorb sx sy))
      else
        let k := 2 * mbits f + 6 in
        let '(q, r) := Z.div_eucl (Z.shiftl mx k) my in
        round f (xorb sx sy) (2 * q + (if r =? 0 then 0 else 1)) (ex - ey - k - 1)
  end.

(** [pow2mod d m = 2^d mod m] by square-and-multiply (for [d >= 0]). *)
Fixpoint pow2mod_pos (p : positive) (m : Z) : Z :=
  match p with
  | xH => 2 mod m
  | xO p' => let r := pow2mod_pos p' m in (r * r) mod m
  | xI p' => let r := pow2mod_pos p' m in (2 * (r * r)) mod m
  end.

Definition pow2mod (d m : Z) : Z :=
  match d with Zpos p => pow2mod_pos p m | _ => 1 mod m end.

(** [frem]/[drem] (JVMS 6.5): the truncating remainder of C's [fmod], not
    IEEE 754 [remainder]: result = x - y * trunc(x / y), computed exactly;
    it has the sign of the dividend (also when it is zero). *)
Definition rem (f : fmt) (x y : Z) : Z :=
  match decode f x, decode f y with
  | NaN, _ | _, NaN => qnan f
  | Inf _, _ => qnan f
  | Fin _ _ _, Inf _ => norm f x
  | Fin sx mx ex, Fin _ my ey =>
      if my =? 0 then qnan f
      else if mx =? 0 then norm f x
      else if ey <=? ex
           then round f sx (((mx mod my) * pow2mod (ex - ey) my) mod my) ey
           else round f sx (mx mod Z.shiftl my (ey - ex)) ex
  end.

(** ** Conversions *)

Definition of_int (f : fmt) (z : Z) : Z :=
  if z =? 0 then zero_bits f false else round f (z <? 0) (Z.abs z) 0.

Definition convert (f1 f2 : fmt) (x : Z) : Z :=
  match decode f1 x with
  | NaN => qnan f2
  | Inf s => inf_bits f2 s
  | Fin s m e => round f2 s m e
  end.

Definition clamp (lo hi z : Z) : Z := Z.max lo (Z.min hi z).

(** f2i/f2l/d2i/d2l (JVMS 6.5): NaN gives 0, otherwise round toward zero
    and saturate to the range of the target type. *)
Definition to_int (f : fmt) (lo hi : Z) (x : Z) : Z :=
  match decode f x with
  | NaN => 0
  | Inf s => if s then lo else hi
  | Fin s m e =>
      let t := if 0 <=? e then Z.shiftl m e else Z.shiftr m (- e) in
      clamp lo hi (signed s t)
  end.

(** ** Comparison (fcmpl/fcmpg/dcmpl/dcmpg, JVMS 6.5)

    For non-NaN bit patterns the magnitude bits order the magnitudes
    (including infinity), so a signed key orders the values, with +0 and -0
    both mapped to 0.  [g] selects the NaN result: [true] = 1 (fcmpg),
    [false] = -1 (fcmpl). *)
Definition cmp_key (f : fmt) (x : Z) : Z :=
  let a := Z.land x (Z.ones (width f - 1)) in
  if sign_bit f x then - a else a.

Definition cmp (f : fmt) (g : bool) (x y : Z) : Z :=
  if is_nan f x || is_nan f y then (if g then 1 else -1)
  else match Z.compare (cmp_key f x) (cmp_key f y) with
       | Lt => -1 | Eq => 0 | Gt => 1
       end.

(** ** The JVM instructions *)

Definition QNAN32 : Z := qnan binary32.  (* 0x7fc00000 *)
Definition QNAN64 : Z := qnan binary64.  (* 0x7ff8000000000000 *)

Definition is_nan32 := is_nan binary32.
Definition is_nan64 := is_nan binary64.
Definition canon32 := canon binary32.
Definition canon64 := canon binary64.

Definition fadd32 : Z -> Z -> Z := add binary32.
Definition fsub32 : Z -> Z -> Z := sub binary32.
Definition fmul32 : Z -> Z -> Z := mul binary32.
Definition fdiv32 : Z -> Z -> Z := div binary32.
Definition frem32 : Z -> Z -> Z := rem binary32.
Definition fneg32 : Z -> Z := neg binary32.

Definition dadd64 : Z -> Z -> Z := add binary64.
Definition dsub64 : Z -> Z -> Z := sub binary64.
Definition dmul64 : Z -> Z -> Z := mul binary64.
Definition ddiv64 : Z -> Z -> Z := div binary64.
Definition drem64 : Z -> Z -> Z := rem binary64.
Definition dneg64 : Z -> Z := neg binary64.

Definition i2f : Z -> Z := of_int binary32.
Definition i2d : Z -> Z := of_int binary64.
Definition l2f : Z -> Z := of_int binary32.
Definition l2d : Z -> Z := of_int binary64.
Definition f2d : Z -> Z := convert binary32 binary64.
Definition d2f : Z -> Z := convert binary64 binary32.
Definition f2i : Z -> Z := to_int binary32 INT_MIN INT_MAX.
Definition f2l : Z -> Z := to_int binary32 LONG_MIN LONG_MAX.
Definition d2i : Z -> Z := to_int binary64 INT_MIN INT_MAX.
Definition d2l : Z -> Z := to_int binary64 LONG_MIN LONG_MAX.

Definition fcmp32 (g : bool) : Z -> Z -> Z := cmp binary32 g.
Definition dcmp64 (g : bool) : Z -> Z -> Z := cmp binary64 g.
Definition fcmpl : Z -> Z -> Z := fcmp32 false.
Definition fcmpg : Z -> Z -> Z := fcmp32 true.
Definition dcmpl : Z -> Z -> Z := dcmp64 false.
Definition dcmpg : Z -> Z -> Z := dcmp64 true.

(** ** Properties *)

Lemma neg_involutive : forall f x, neg f (neg f x) = x.
Proof.
  intros f x. unfold neg. rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
  reflexivity.
Qed.

Lemma fneg32_involutive : forall x, fneg32 (fneg32 x) = x.
Proof. intros; apply neg_involutive. Qed.
Lemma dneg64_involutive : forall x, dneg64 (dneg64 x) = x.
Proof. intros; apply neg_involutive. Qed.

Lemma cmp_lg_agree : forall f x y,
  is_nan f x = false -> is_nan f y = false -> cmp f true x y = cmp f false x y.
Proof. intros f x y Hx Hy. unfold cmp. rewrite Hx, Hy. reflexivity. Qed.

Lemma fcmpl_fcmpg_agree : forall x y,
  is_nan32 x = false -> is_nan32 y = false -> fcmpl x y = fcmpg x y.
Proof. intros; symmetry; apply cmp_lg_agree; auto. Qed.
Lemma dcmpl_dcmpg_agree : forall x y,
  is_nan64 x = false -> is_nan64 y = false -> dcmpl x y = dcmpg x y.
Proof. intros; symmetry; apply cmp_lg_agree; auto. Qed.

Lemma cmp_nan : forall f g x y,
  is_nan f x = true \/ is_nan f y = true -> cmp f g x y = if g then 1 else -1.
Proof.
  intros f g x y [H | H]; unfold cmp; rewrite H; [reflexivity|].
  rewrite orb_true_r; reflexivity.
Qed.

Lemma cmp_range : forall f g x y, cmp f g x y = -1 \/ cmp f g x y = 0 \/ cmp f g x y = 1.
Proof.
  intros. unfold cmp. destruct (is_nan f x || is_nan f y); [destruct g; auto|].
  destruct (Z.compare _ _); auto.
Qed.

(** Swapping the operands of [fcmpl] gives the negation of [fcmpg]. *)
Lemma cmp_antisym : forall f g x y, cmp f g x y = - cmp f (negb g) y x.
Proof.
  intros. unfold cmp. rewrite orb_comm.
  destruct (is_nan f y || is_nan f x); [destruct g; reflexivity|].
  generalize (cmp_key f x) (cmp_key f y); intros a b.
  destruct (Z.compare_spec a b) as [H | H | H];
    [subst; rewrite Z.compare_refl
    | rewrite (proj2 (Z.compare_gt_iff b a)) by lia
    | rewrite (proj2 (Z.compare_lt_iff b a)) by lia]; reflexivity.
Qed.

Lemma cmp_refl : forall f g x, is_nan f x = false -> cmp f g x x = 0.
Proof. intros. unfold cmp. rewrite H, Z.compare_refl. reflexivity. Qed.

Lemma clamp_range : forall lo hi z, lo <= hi -> lo <= clamp lo hi z <= hi.
Proof. intros. unfold clamp. lia. Qed.

Lemma to_int_range : forall f lo hi x, lo <= 0 <= hi -> lo <= to_int f lo hi x <= hi.
Proof.
  intros f lo hi x H. unfold to_int.
  destruct (decode f x) as [| s | s m e]; [lia | destruct s; lia | apply clamp_range; lia].
Qed.

Lemma f2i_range : forall x, in_int (f2i x).
Proof.
  intros x. pose proof (to_int_range binary32 INT_MIN INT_MAX x) as H.
  unfold in_int, in_range, f2i, INT_MIN, INT_MAX in *. simpl in *. lia.
Qed.
Lemma d2i_range : forall x, in_int (d2i x).
Proof.
  intros x. pose proof (to_int_range binary64 INT_MIN INT_MAX x) as H.
  unfold in_int, in_range, d2i, INT_MIN, INT_MAX in *. simpl in *. lia.
Qed.
Lemma f2l_range : forall x, in_long (f2l x).
Proof.
  intros x. pose proof (to_int_range binary32 LONG_MIN LONG_MAX x) as H.
  unfold in_long, in_range, f2l, LONG_MIN, LONG_MAX in *. simpl in *. lia.
Qed.
Lemma d2l_range : forall x, in_long (d2l x).
Proof.
  intros x. pose proof (to_int_range binary64 LONG_MIN LONG_MAX x) as H.
  unfold in_long, in_range, d2l, LONG_MIN, LONG_MAX in *. simpl in *. lia.
Qed.

Lemma to_int_nan : forall f lo hi x, is_nan f x = true -> to_int f lo hi x = 0.
Proof.
  intros f lo hi x H. unfold to_int, decode. unfold is_nan in H.
  apply andb_true_iff in H as [H1 H2]. rewrite H1. apply negb_true_iff in H2.
  rewrite H2. reflexivity.
Qed.

(** Addition and multiplication are commutative (including signed zeros,
    infinities and NaNs, thanks to the canonical NaN). *)
Lemma add_comm : forall f x y, add f x y = add f y x.
Proof.
  intros f x y. unfold add.
  destruct (decode f x) as [| sx | sx mx ex], (decode f y) as [| sy | sy my ey];
    try reflexivity.
  - destruct sx, sy; reflexivity.
  - rewrite Z.min_comm, (Z.add_comm (signed sx _)), andb_comm. reflexivity.
Qed.

Lemma mul_comm : forall f x y, mul f x y = mul f y x.
Proof.
  intros f x y. unfold mul.
  destruct (decode f x) as [| sx | sx mx ex], (decode f y) as [| sy | sy my ey];
    try reflexivity; rewrite ?(xorb_comm sx sy), ?(Z.mul_comm mx my), ?(Z.add_comm ex ey);
    reflexivity.
Qed.

Lemma fadd32_comm : forall x y, fadd32 x y = fadd32 y x.
Proof. intros; apply add_comm. Qed.
Lemma dadd64_comm : forall x y, dadd64 x y = dadd64 y x.
Proof. intros; apply add_comm. Qed.
Lemma fmul32_comm : forall x y, fmul32 x y = fmul32 y x.
Proof. intros; apply mul_comm. Qed.
Lemma dmul64_comm : forall x y, dmul64 x y = dmul64 y x.
Proof. intros; apply mul_comm. Qed.

Lemma pow2mod_pos_spec : forall p m, m <> 0 -> pow2mod_pos p m = 2 ^ Zpos p mod m.
Proof.
  induction p as [p IH | p IH |]; intros m Hm; simpl pow2mod_pos.
  - rewrite IH by auto. set (A := 2 ^ Zpos p).
    transitivity ((2 * (A * A)) mod m).
    + rewrite <- (Z.mul_mod_idemp_r 2 (A * A)) by auto.
      rewrite (Z.mul_mod A A) by auto. rewrite Z.mul_mod_idemp_r by auto. reflexivity.
    + f_equal. rewrite (Pos2Z.inj_xI p).
      replace (2 * Zpos p + 1) with (Z.succ (Zpos p + Zpos p)) by lia.
      rewrite Z.pow_succ_r, Z.pow_add_r by lia. reflexivity.
  - rewrite IH by auto. rewrite <- Z.mul_mod by auto. f_equal.
    rewrite (Pos2Z.inj_xO p). replace (2 * Zpos p) with (Zpos p + Zpos p) by lia.
    rewrite Z.pow_add_r by lia. reflexivity.
  - reflexivity.
Qed.

Lemma pow2mod_spec : forall d m, 0 <= d -> m <> 0 -> pow2mod d m = 2 ^ d mod m.
Proof.
  intros d m Hd Hm. destruct d as [| p | p]; simpl.
  - reflexivity.
  - apply pow2mod_pos_spec; auto.
  - lia.
Qed.

(** ** Every result is a bit pattern of its format *)

Definition valid_fmt (f : fmt) : Prop := 1 <= mbits f /\ 2 <= ebits f.
Definition in_fmt (f : fmt) (x : Z) : Prop := 0 <= x < 2 ^ width f.

Lemma pow2_spec : forall n, pow2 n = 2 ^ n.
Proof. intros; apply Z.shiftl_1_l. Qed.

Lemma shr_rne_bounds : forall m k, 0 <= m -> 0 < k -> 0 <= shr_rne m k <= m / 2 ^ k + 1.
Proof.
  intros m k Hm Hk. unfold shr_rne. cbv zeta. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 <= m / 2 ^ k) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  destruct (_ || _); lia.
Qed.

Section Range.
Variable f : fmt.
Hypothesis Hf : valid_fmt f.

Let P := 2 ^ mbits f.
Let Q := 2 ^ ebits f.

Lemma width_pow : 2 ^ width f = 2 * Q * P /\ 2 ^ (width f - 1) = Q * P.
Proof.
  destruct Hf. unfold width, P, Q.
  assert (E : 2 ^ (mbits f + ebits f + 1 - 1) = 2 ^ ebits f * 2 ^ mbits f).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  split; [|exact E].
  replace (mbits f + ebits f + 1) with (Z.succ (mbits f + ebits f + 1 - 1)) by lia.
  rewrite Z.pow_succ_r, E by lia. ring.
Qed.

Lemma P_ge2 : 2 <= P.
Proof.
  destruct Hf. unfold P. replace 2 with (2 ^ 1) at 1 by reflexivity.
  apply Z.pow_le_mono_r; lia.
Qed.
Lemma Q_ge4 : 4 <= Q.
Proof.
  destruct Hf. unfold Q. replace 4 with (2 ^ 2) at 1 by reflexivity.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma sign_val_range : forall s, sign_val f s = 0 \/ sign_val f s = Q * P.
Proof.
  intros []; unfold sign_val; [right | left]; auto.
  rewrite pow2_spec. apply width_pow.
Qed.

Lemma zero_bits_range : forall s, in_fmt f (zero_bits f s).
Proof.
  intros s. unfold in_fmt, zero_bits. pose proof width_pow. pose proof P_ge2. pose proof Q_ge4.
  destruct (sign_val_range s); nia.
Qed.

Lemma emax_biased_eq : emax_biased f = Q - 1.
Proof. unfold emax_biased. rewrite pow2_spec. reflexivity. Qed.

Lemma inf_bits_range : forall s, in_fmt f (inf_bits f s).
Proof.
  intros s. unfold in_fmt, inf_bits. rewrite emax_biased_eq, pow2_spec. fold P.
  pose proof width_pow. pose proof P_ge2. pose proof Q_ge4.
  destruct (sign_val_range s); nia.
Qed.

Lemma qnan_range : in_fmt f (qnan f).
Proof.
  unfold in_fmt, qnan. rewrite emax_biased_eq, !pow2_spec. fold P.
  assert (2 ^ (mbits f - 1) * 2 = P).
  { unfold P. destruct Hf. rewrite Z.mul_comm, <- Z.pow_succ_r by lia. f_equal. lia. }
  pose proof width_pow. pose proof P_ge2. pose proof Q_ge4. nia.
Qed.

Lemma norm_range : forall x, in_fmt f (norm f x).
Proof.
  intros x. unfold in_fmt, norm. destruct Hf.
  rewrite Z.land_ones by (unfold width; lia). apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; unfold width; lia.
Qed.

Lemma round_range : forall s m e, in_fmt f (round f s m e).
Proof.
  intros s m e. unfold round.
  destruct (m <=? 0) eqn:Hm0; [apply zero_bits_range|]. apply Z.leb_gt in Hm0.
  pose proof (Z.log2_spec m Hm0) as [Hlo Hhi]. pose proof (Z.log2_nonneg m).
  set (n := Z.log2 m) in *.
  set (q0 := Z.max (n + e - mbits f) (emin_ulp f)).
  assert (Hq0 : n + e - mbits f <= q0) by apply Z.le_max_l.
  rewrite !pow2_spec.
  assert (HP1 : 2 ^ (mbits f + 1) = 2 * P).
  { unfold P. destruct Hf. rewrite Z.pow_add_r, Z.pow_1_r by lia. ring. }
  rewrite HP1.
  set (mq0 := if q0 <=? e then Z.shiftl m (e - q0) else shr_rne m (q0 - e)).
  assert (Hmq0 : 0 <= mq0 <= 2 * P).
  { unfold mq0. destruct (q0 <=? e) eqn:He.
    - apply Z.leb_le in He. rewrite Z.shiftl_mul_pow2 by lia.
      assert (m * 2 ^ (e - q0) < 2 ^ Z.succ n * 2 ^ (e - q0)).
      { apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg|]; lia. }
      rewrite <- Z.pow_add_r in H0 by lia.
      assert (2 ^ (Z.succ n + (e - q0)) <= 2 * P).
      { rewrite <- HP1. apply Z.pow_le_mono_r; lia. }
      assert (0 <= m * 2 ^ (e - q0)) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
      lia.
    - apply Z.leb_gt in He. pose proof (shr_rne_bounds m (q0 - e)) as Hb.
      assert (m / 2 ^ (q0 - e) < 2 * P).
      { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
        rewrite <- HP1, <- Z.pow_add_r by (destruct Hf; lia).
        apply Z.lt_le_trans with (2 ^ Z.succ n); auto.
        apply Z.pow_le_mono_r; lia. }
      lia. }
  clearbody mq0.
  assert (Hq0e : emin_ulp f <= q0) by apply Z.le_max_r.
  clearbody q0.
  pose proof width_pow as [Hw1 Hw2]. pose proof P_ge2. pose proof Q_ge4.
  destruct (mq0 =? 2 * P) eqn:Hc; [apply Z.eqb_eq in Hc | apply Z.eqb_neq in Hc];
  fold P.
  - destruct (P <? P) eqn:Hs; [apply Z.ltb_lt in Hs; lia|].
    destruct (emax_biased f <=? q0 + 1 - emin_ulp f + 1) eqn:Ho; [apply inf_bits_range|].
    apply Z.leb_gt in Ho. rewrite emax_biased_eq in Ho. unfold in_fmt.
    destruct (sign_val_range s); nia.
  - destruct (mq0 <? P) eqn:Hs.
    + apply Z.ltb_lt in Hs. unfold in_fmt. destruct (sign_val_range s); nia.
    + apply Z.ltb_ge in Hs.
      destruct (emax_biased f <=? q0 - emin_ulp f + 1) eqn:Ho; [apply inf_bits_range|].
      apply Z.leb_gt in Ho. rewrite emax_biased_eq in Ho. unfold in_fmt.
      destruct (sign_val_range s); nia.
Qed.

Local Ltac range_tac :=
  repeat match goal with
         | |- context [match ?x with _ => _ end] => destruct x
         end;
  first [ apply qnan_range | apply inf_bits_range | apply zero_bits_range
        | apply round_range | apply norm_range ].

Lemma add_range : forall x y, in_fmt f (add f x y).
Proof. intros. unfold add. range_tac. Qed.
Lemma sub_range : forall x y, in_fmt f (sub f x y).
Proof. intros. apply add_range. Qed.
Lemma mul_range : forall x y, in_fmt f (mul f x y).
Proof. intros. unfold mul. range_tac. Qed.
Lemma div_range : forall x y, in_fmt f (div f x y).
Proof. intros. unfold div. range_tac. Qed.
Lemma rem_range : forall x y, in_fmt f (rem f x y).
Proof. intros. unfold rem. range_tac. Qed.
Lemma of_int_range : forall z, in_fmt f (of_int f z).
Proof. intros. unfold of_int. range_tac. Qed.
Lemma convert_range : forall f0 x, in_fmt f (convert f0 f x).
Proof. intros. unfold convert. range_tac. Qed.
Lemma canon_range : forall x, in_fmt f (canon f x).
Proof. intros. unfold canon. range_tac. Qed.

Lemma neg_range : forall x, in_fmt f x -> in_fmt f (neg f x).
Proof.
  intros x [H0 H1]. unfold in_fmt, neg. rewrite pow2_spec.
  pose proof width_pow as [Hw1 Hw2]. pose proof P_ge2. pose proof Q_ge4.
  assert (0 <= Z.lxor x (2 ^ (width f - 1))) by (apply Z.lxor_nonneg; split; lia).
  split; auto.
  destruct (Z.eq_dec (Z.lxor x (2 ^ (width f - 1))) 0) as [E | E]; [lia|].
  apply Z.log2_lt_pow2; [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec x 0); [subst; simpl; destruct Hf; unfold width; lia|].
    apply Z.log2_lt_pow2; lia.
  - rewrite Z.log2_pow2; [lia|]. destruct Hf; unfold width; lia.
Qed.
End Range.

Lemma valid_binary32 : valid_fmt binary32.
Proof. split; simpl; lia. Qed.
Lemma valid_binary64 : valid_fmt binary64.
Proof. split; simpl; lia. Qed.

Definition in_float (x : Z) : Prop := 0 <= x < 2 ^ 32.
Definition in_double (x : Z) : Prop := 0 <= x < 2 ^ 64.

Lemma fadd32_range : forall x y, in_float (fadd32 x y).
Proof. intros; exact (add_range binary32 valid_binary32 x y). Qed.
Lemma fsub32_range : forall x y, in_float (fsub32 x y).
Proof. intros; exact (sub_range binary32 valid_binary32 x y). Qed.
Lemma fmul32_range : forall x y, in_float (fmul32 x y).
Proof. intros; exact (mul_range binary32 valid_binary32 x y). Qed.
Lemma fdiv32_range : forall x y, in_float (fdiv32 x y).
Proof. intros; exact (div_range binary32 valid_binary32 x y). Qed.
Lemma frem32_range : forall x y, in_float (frem32 x y).
Proof. intros; exact (rem_range binary32 valid_binary32 x y). Qed.
Lemma fneg32_range : forall x, in_float x -> in_float (fneg32 x).
Proof. intros; exact (neg_range binary32 valid_binary32 x H). Qed.
Lemma dadd64_range : forall x y, in_double (dadd64 x y).
Proof. intros; exact (add_range binary64 valid_binary64 x y). Qed.
Lemma dsub64_range : forall x y, in_double (dsub64 x y).
Proof. intros; exact (sub_range binary64 valid_binary64 x y). Qed.
Lemma dmul64_range : forall x y, in_double (dmul64 x y).
Proof. intros; exact (mul_range binary64 valid_binary64 x y). Qed.
Lemma ddiv64_range : forall x y, in_double (ddiv64 x y).
Proof. intros; exact (div_range binary64 valid_binary64 x y). Qed.
Lemma drem64_range : forall x y, in_double (drem64 x y).
Proof. intros; exact (rem_range binary64 valid_binary64 x y). Qed.
Lemma dneg64_range : forall x, in_double x -> in_double (dneg64 x).
Proof. intros; exact (neg_range binary64 valid_binary64 x H). Qed.
Lemma i2f_range : forall z, in_float (i2f z).
Proof. intros; exact (of_int_range binary32 valid_binary32 z). Qed.
Lemma l2f_range : forall z, in_float (l2f z).
Proof. intros; exact (of_int_range binary32 valid_binary32 z). Qed.
Lemma i2d_range : forall z, in_double (i2d z).
Proof. intros; exact (of_int_range binary64 valid_binary64 z). Qed.
Lemma l2d_range : forall z, in_double (l2d z).
Proof. intros; exact (of_int_range binary64 valid_binary64 z). Qed.
Lemma f2d_range : forall x, in_double (f2d x).
Proof. intros; exact (convert_range binary64 valid_binary64 binary32 x). Qed.
Lemma d2f_range : forall x, in_float (d2f x).
Proof. intros; exact (convert_range binary32 valid_binary32 binary64 x). Qed.

(** ** Corner cases (checked by computation; the expected bit patterns were
    obtained from HotSpot 21) *)

Definition FMIN_VALUE : Z := 1.            (* Float.MIN_VALUE *)
Definition FMIN_NORMAL : Z := 8388608.     (* 0x00800000 *)
Definition FMAX_VALUE : Z := 2139095039.   (* 0x7f7fffff *)
Definition FPOS_INF : Z := 2139095040.     (* 0x7f800000 *)
Definition FNEG_INF : Z := 4286578688.     (* 0xff800000 *)
Definition FNEG_ZERO : Z := 2147483648.    (* 0x80000000 *)
Definition FONE : Z := 1065353216.         (* 0x3f800000 *)
Definition FTWO : Z := 1073741824.         (* 0x40000000 *)

(* 0.1f + 0.2f == 0.3f: 0x3dcccccd + 0x3e4ccccd = 0x3e99999a *)
Example fadd_01_02 : fadd32 1036831949 1045220557 = 1050253722. Proof. reflexivity. Qed.
(* 0.1 + 0.2 = 0x3fd3333333333334 (not 0.3) *)
Example dadd_01_02 :
  dadd64 4591870180066957722 4596373779694328218 = 4599075939470750516.
Proof. reflexivity. Qed.
(* 1/3 *)
Example fdiv_1_3 : fdiv32 FONE 1077936128 = 1051372203. Proof. reflexivity. Qed.
Example ddiv_1_3 : ddiv64 4607182418800017408 4613937818241073152 = 4599676419421066581.
Proof. reflexivity. Qed.
(* 1/0 = +inf, -1/0 = -inf, 0/0 = NaN, 1/-0 = -inf *)
Example fdiv_1_0 : fdiv32 FONE 0 = FPOS_INF. Proof. reflexivity. Qed.
Example fdiv_m1_0 : fdiv32 (fneg32 FONE) 0 = FNEG_INF. Proof. reflexivity. Qed.
Example fdiv_0_0 : fdiv32 0 0 = QNAN32. Proof. reflexivity. Qed.
Example fdiv_1_m0 : fdiv32 FONE FNEG_ZERO = FNEG_INF. Proof. reflexivity. Qed.
Example ddiv_0_0 : ddiv64 0 0 = QNAN64. Proof. reflexivity. Qed.
Example qnan_values : QNAN32 = 2143289344 /\ QNAN64 = 9221120237041090560.
Proof. split; reflexivity. Qed.
(* inf - inf = NaN, inf * 0 = NaN *)
Example fsub_inf_inf : fsub32 FPOS_INF FPOS_INF = QNAN32. Proof. reflexivity. Qed.
Example fmul_inf_0 : fmul32 FPOS_INF 0 = QNAN32. Proof. reflexivity. Qed.
(* signed zeros: x + (-x) = +0, (-0) + (-0) = -0, (-0) + 0 = +0, -0 * 1 = -0 *)
Example fadd_cancel : fadd32 FONE (fneg32 FONE) = 0. Proof. reflexivity. Qed.
Example fadd_m0_m0 : fadd32 FNEG_ZERO FNEG_ZERO = FNEG_ZERO. Proof. reflexivity. Qed.
Example fadd_m0_0 : fadd32 FNEG_ZERO 0 = 0. Proof. reflexivity. Qed.
Example fsub_0_0 : fsub32 0 0 = 0. Proof. reflexivity. Qed.
Example fmul_m0_1 : fmul32 FNEG_ZERO FONE = FNEG_ZERO. Proof. reflexivity. Qed.
(* subnormals: MIN_VALUE/2 = 0 (tie to even), 1.5*MIN_VALUE = 2*MIN_VALUE
   (tie to even), 3*MIN_VALUE/2 = 2*MIN_VALUE, MIN_NORMAL - MIN_VALUE =
   0x007fffff, MIN_VALUE + MIN_VALUE = 2*MIN_VALUE *)
Example fdiv_min_2 : fdiv32 FMIN_VALUE FTWO = 0. Proof. reflexivity. Qed.
Example fmul_min_15 : fmul32 FMIN_VALUE 1069547520 = 2. Proof. reflexivity. Qed.
Example fdiv_3min_2 : fdiv32 3 FTWO = 2. Proof. reflexivity. Qed.
Example fsub_minnorm_min : fsub32 FMIN_NORMAL FMIN_VALUE = 8388607. Proof. reflexivity. Qed.
Example fadd_min_min : fadd32 FMIN_VALUE FMIN_VALUE = 2. Proof. reflexivity. Qed.
(* overflow: MAX_VALUE * 2 = +inf *)
Example fmul_max_2 : fmul32 FMAX_VALUE FTWO = FPOS_INF. Proof. reflexivity. Qed.
(* rounding ties: 2^24 + 1 = 2^24; (2^24 + 2) + 1 = 2^24 + 4 *)
Example fadd_tie_even : fadd32 1266679808 FONE = 1266679808. Proof. reflexivity. Qed.
Example fadd_tie_up : fadd32 1266679809 FONE = 1266679810. Proof. reflexivity. Qed.
Example i2f_tie_even : i2f 16777217 = 1266679808. Proof. reflexivity. Qed.
Example i2f_tie_up : i2f 16777219 = 1266679810. Proof. reflexivity. Qed.
Example l2f_max : l2f LONG_MAX = 1593835520. Proof. reflexivity. Qed.         (* 2^63 *)
Example l2d_min : l2d LONG_MIN = 14114281232179134464. Proof. reflexivity. Qed. (* -2^63 *)
Example l2d_tie : l2d 9007199254740993 = 4845873199050653696. Proof. reflexivity. Qed.
(* f2i / d2l *)
Example f2i_nan : f2i QNAN32 = 0. Proof. reflexivity. Qed.
Example f2i_huge : f2i 1621981420 = INT_MAX. Proof. reflexivity. Qed.        (* 1e20f *)
Example f2i_mhuge : f2i (fneg32 1621981420) = INT_MIN. Proof. reflexivity. Qed.
Example f2i_m15 : f2i (fneg32 1069547520) = -1. Proof. reflexivity. Qed.     (* -1.5f *)
Example d2l_minf : d2l (dneg64 (inf_bits binary64 false)) = LONG_MIN. Proof. reflexivity. Qed.
Example f2l_inf : f2l FPOS_INF = LONG_MAX. Proof. reflexivity. Qed.
(* d2f: Double.MAX_VALUE -> inf; FLOAT_MAX + half ulp -> inf (tie to even);
   just below it -> Float.MAX_VALUE; 1e-50 -> 0 *)
Example d2f_max : d2f 9218868437227405311 = FPOS_INF. Proof. reflexivity. Qed.
Example d2f_halfulp : d2f 5183643170835005440 = FPOS_INF. Proof. reflexivity. Qed.
Example d2f_below : d2f 5183643170835005439 = FMAX_VALUE. Proof. reflexivity. Qed.
Example d2f_tiny : d2f 3859002664735258655 = 0. Proof. reflexivity. Qed.     (* 1e-50 *)
Example f2d_one : f2d FONE = 4607182418800017408. Proof. reflexivity. Qed.
Example f2d_min : f2d FMIN_VALUE = 3936146074321813504. Proof. reflexivity. Qed. (* 2^-149 *)
(* fmod: 5.5 % 2 = 1.5, -5.5 % 2 = -1.5, 5.5 % -2 = 1.5, -4 % 2 = -0,
   1 % inf = 1, inf % 1 = NaN, 1 % 0 = NaN, -0 % 1 = -0 *)
Example frem_1 : frem32 1085276160 FTWO = 1069547520. Proof. reflexivity. Qed.
Example frem_2 : frem32 (fneg32 1085276160) FTWO = fneg32 1069547520. Proof. reflexivity. Qed.
Example frem_3 : frem32 1085276160 (fneg32 FTWO) = 1069547520. Proof. reflexivity. Qed.
Example frem_4 : frem32 (fneg32 1082130432) FTWO = FNEG_ZERO. Proof. reflexivity. Qed.
Example frem_5 : frem32 FONE FPOS_INF = FONE. Proof. reflexivity. Qed.
Example frem_6 : frem32 FPOS_INF FONE = QNAN32. Proof. reflexivity. Qed.
Example frem_7 : frem32 FONE 0 = QNAN32. Proof. reflexivity. Qed.
Example frem_8 : frem32 FNEG_ZERO FONE = FNEG_ZERO. Proof. reflexivity. Qed.
(* fneg flips the sign of a NaN too *)
Example fneg_nan : fneg32 QNAN32 = 4290772992. Proof. reflexivity. Qed.     (* 0xffc00000 *)
(* comparisons *)
Example fcmpl_nan : fcmpl QNAN32 FONE = -1. Proof. reflexivity. Qed.
Example fcmpg_nan : fcmpg QNAN32 FONE = 1. Proof. reflexivity. Qed.
Example fcmp_zeros : fcmpl 0 FNEG_ZERO = 0. Proof. reflexivity. Qed.
Example fcmp_inf : fcmpg FNEG_INF FMAX_VALUE = -1. Proof. reflexivity. Qed.
Example dcmp_neg : dcmpl (dneg64 4607182418800017408) 0 = -1. Proof. reflexivity. Qed.

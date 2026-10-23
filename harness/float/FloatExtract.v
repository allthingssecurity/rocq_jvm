(** Extraction of [JVM.Core.Float] for the float/double differential test.

    [Z] and [positive] keep their Rocq inductive representation: no OCaml
    machine arithmetic is trusted by the model side of the comparison.

    The file also defines two deliberately wrong variants of [round]
    (used only by the canary runs, never by the model):
    - mode 1: ties rounded away from zero instead of to even;
    - mode 2: flush-to-zero, i.e. no gradual underflow (any result whose
      rounded value is below the smallest normal becomes a signed zero). *)

From Stdlib Require Import ZArith Bool.
From Stdlib Require Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From JVM.Core Require Import Float.
Open Scope Z_scope.

Definition shr_away (m k : Z) : Z :=
  let q := Z.shiftr m k in
  let r := m - Z.shiftl q k in
  if pow2 (k - 1) <=? r then q + 1 else q.

Definition round_mut (mode : Z) (f : fmt) (s : bool) (m e : Z) : Z :=
  if m <=? 0 then zero_bits f s else
  let q0 := Z.max (Z.log2 m + e - mbits f) (emin_ulp f) in
  let mq0 := if q0 <=? e then Z.shiftl m (e - q0)
             else if mode =? 1 then shr_away m (q0 - e) else shr_rne m (q0 - e) in
  let '(mq, q) := if mq0 =? pow2 (mbits f + 1) then (pow2 (mbits f), q0 + 1)
                  else (mq0, q0) in
  if mq <? pow2 (mbits f) then (if mode =? 2 then zero_bits f s else sign_val f s + mq)
  else
    let be := q - emin_ulp f + 1 in
    if emax_biased f <=? be then inf_bits f s
    else sign_val f s + be * pow2 (mbits f) + (mq - pow2 (mbits f)).

Definition add_mut (mode : Z) (f : fmt) (x y : Z) : Z :=
  match decode f x, decode f y with
  | NaN, _ | _, NaN => qnan f
  | Inf sx, Inf sy => if Bool.eqb sx sy then inf_bits f sx else qnan f
  | Inf sx, Fin _ _ _ => inf_bits f sx
  | Fin _ _ _, Inf sy => inf_bits f sy
  | Fin sx mx ex, Fin sy my ey =>
      let e := Z.min ex ey in
      let t := signed sx (Z.shiftl mx (ex - e)) + signed sy (Z.shiftl my (ey - e)) in
      if t =? 0 then zero_bits f (sx && sy)
      else round_mut mode f (t <? 0) (Z.abs t) e
  end.

Definition mul_mut (mode : Z) (f : fmt) (x y : Z) : Z :=
  match decode f x, decode f y with
  | NaN, _ | _, NaN => qnan f
  | Inf sx, Inf sy => inf_bits f (xorb sx sy)
  | Inf sx, Fin sy my _ => if my =? 0 then qnan f else inf_bits f (xorb sx sy)
  | Fin sx mx _, Inf sy => if mx =? 0 then qnan f else inf_bits f (xorb sx sy)
  | Fin sx mx ex, Fin sy my ey => round_mut mode f (xorb sx sy) (mx * my) (ex + ey)
  end.

(** Mode 0 is the model itself (checked by conversion). *)
Lemma add_mut0 : forall f x y, add_mut 0 f x y = add f x y.
Proof. reflexivity. Qed.
Lemma mul_mut0 : forall f x y, mul_mut 0 f x y = mul f x y.
Proof. reflexivity. Qed.

Extraction Language OCaml.
Extraction "float_model.ml"
  binary32 binary64 canon32 canon64
  fadd32 fsub32 fmul32 fdiv32 frem32 fneg32
  dadd64 dsub64 dmul64 ddiv64 drem64 dneg64
  i2f i2d l2f l2d f2d d2f f2i f2l d2i d2l
  fcmpl fcmpg dcmpl dcmpg
  add_mut mul_mut.

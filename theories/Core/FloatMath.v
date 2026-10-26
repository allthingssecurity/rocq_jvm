(** * java.lang.Math / StrictMath on float and double (JDK 21)

    The methods whose results the Java SE specification fixes exactly: abs, max, min,
    signum, copySign, floor, ceil, rint, round, sqrt (correctly rounded), fma (one
    rounding), ulp, nextUp, nextDown, nextAfter, scalb, getExponent, IEEEremainder,
    toRadians/toDegrees (one multiplication by the JDK's constants), and pow where the
    specification fixes the result (its special cases, and integer arguments whose exact
    power is a double). Everything else (pow otherwise, exp, log, the trigonometric
    functions: HotSpot's intrinsics) is left to the caller as "no claim" (None).

    Conventions as in Float.v: bit patterns as Z, NaN results canonical (the JDK's Java
    code returns an argument NaN in some cases: there the argument is returned). *)

From Stdlib Require Import ZArith Bool.
From JVM.Core Require Import Float.
Open Scope Z_scope.

Definition sgn_mask (f : fmt) : Z := pow2 (width f - 1).
Definition mag (f : fmt) (x : Z) : Z := Z.land (norm f x) (sgn_mask f - 1).

(** Math.abs: the sign bit cleared (JDK 18+: also for NaN). *)
Definition fabs (f : fmt) (x : Z) : Z := mag f x.

Definition is_negzero (f : fmt) (x : Z) : bool := norm f x =? sgn_mask f.
Definition is_poszero (f : fmt) (x : Z) : bool := norm f x =? 0.

(** a < b, a <= b on numbers (false with a NaN). *)
Definition flt (f : fmt) (a b : Z) : bool := cmp f true a b =? -1.
Definition fle (f : fmt) (a b : Z) : bool := negb (is_nan f a) && negb (is_nan f b) && negb (cmp f true a b =? 1).
Definition fge (f : fmt) (a b : Z) : bool := fle f b a.
Definition feq (f : fmt) (a b : Z) : bool := negb (is_nan f a) && negb (is_nan f b) && (cmp f true a b =? 0).

(** Math.max / Math.min (the JDK's Java code). *)
Definition fmax (f : fmt) (a b : Z) : Z :=
  if is_nan f a then a
  else if is_zero f a && is_zero f b && is_negzero f a then b
  else if fge f a b then a else b.
Definition fmin (f : fmt) (a b : Z) : Z :=
  if is_nan f a then a
  else if is_zero f a && is_zero f b && is_negzero f b then b
  else if fle f a b then a else b.

Definition one (f : fmt) : Z := bias f * pow2 (mbits f).

(** Math.copySign: the magnitude of [m] with the sign bit of [s] (raw, NaN signs included). *)
Definition fcopysign (f : fmt) (m s : Z) : Z := Z.lor (mag f m) (Z.land (norm f s) (sgn_mask f)).
(** StrictMath.copySign: a NaN sign counts as positive. *)
Definition fcopysign_strict (f : fmt) (m s : Z) : Z := if is_nan f s then mag f m else fcopysign f m s.

Definition fsignum (f : fmt) (x : Z) : Z :=
  if is_zero f x || is_nan f x then x else fcopysign f (one f) x.

(** An integral value of sign [s] and magnitude [n] (exact). *)
Definition of_mag (f : fmt) (s : bool) (n : Z) : Z := if n =? 0 then zero_bits f s else round f s n 0.

(** floor (k = -1), ceil (k = 1), rint (k = 0). *)
Definition fround_int (f : fmt) (k : Z) (x : Z) : Z :=
  match decode f x with
  | Fin s m e =>
      if 0 <=? e then norm f x
      else
        let q := Z.shiftr m (- e) in
        let r := m - Z.shiftl q (- e) in
        let n := if k =? 0 then shr_rne m (- e)
                 else if (k =? -1) then (if s then (if r =? 0 then q else q + 1) else q)
                 else (if s then q else (if r =? 0 then q else q + 1)) in
        of_mag f s n
  | _ => norm f x
  end.

(** Math.round: floor(x + 1/2) exactly, NaN 0, clamped to [lo, hi]. *)
Definition fround (f : fmt) (lo hi : Z) (x : Z) : Z :=
  match decode f x with
  | NaN => 0
  | Inf s => if s then lo else hi
  | Fin s m e =>
      let t := if s then - m else m in
      let v := if 0 <=? e then Z.shiftl t e else Z.div (t + pow2 (- e - 1)) (pow2 (- e)) in
      Z.max lo (Z.min hi v)
  end.

(** Math.sqrt: correctly rounded; sqrt(-0) = -0, negative or NaN: NaN. *)
Definition fsqrt (f : fmt) (x : Z) : Z :=
  match decode f x with
  | NaN => qnan f
  | Inf s => if s then qnan f else norm f x
  | Fin s m e =>
      if m =? 0 then norm f x else if s then qnan f else
      let '(m1, e1) := if Z.odd e then (2 * m, e - 1) else (m, e) in
      let k := mbits f + 4 in
      let m2 := Z.shiftl m1 (2 * k) in
      let r := Z.sqrt m2 in
      round f false (2 * r + (if r * r =? m2 then 0 else 1)) (e1 / 2 - k - 1)
  end.

(** Math.fma: a * b + c with one rounding. *)
Definition ffma (f : fmt) (a b c : Z) : Z :=
  match decode f a, decode f b, decode f c with
  | NaN, _, _ | _, NaN, _ | _, _, NaN => qnan f
  | Inf _, Fin _ mb _, _ => if mb =? 0 then qnan f else
      let sp := xorb (sign_bit f a) (sign_bit f b) in
      match decode f c with Inf sc => if Bool.eqb sc sp then inf_bits f sp else qnan f | _ => inf_bits f sp end
  | Fin _ ma _, Inf _, _ => if ma =? 0 then qnan f else
      let sp := xorb (sign_bit f a) (sign_bit f b) in
      match decode f c with Inf sc => if Bool.eqb sc sp then inf_bits f sp else qnan f | _ => inf_bits f sp end
  | Inf _, Inf _, _ =>
      let sp := xorb (sign_bit f a) (sign_bit f b) in
      match decode f c with Inf sc => if Bool.eqb sc sp then inf_bits f sp else qnan f | _ => inf_bits f sp end
  | Fin sa ma ea, Fin sb mb eb, Inf sc => inf_bits f sc
  | Fin sa ma ea, Fin sb mb eb, Fin sc mc ec =>
      let sp := xorb sa sb in
      let ep := ea + eb in
      let e := Z.min ep ec in
      let t := signed sp (Z.shiftl (ma * mb) (ep - e)) + signed sc (Z.shiftl mc (ec - e)) in
      if t =? 0 then
        (if (ma * mb =? 0) && (mc =? 0) then zero_bits f (sp && sc) else zero_bits f false)
      else round f (t <? 0) (Z.abs t) e
  end.

Definition max_bits (f : fmt) : Z := (emax_biased f - 1) * pow2 (mbits f) + (pow2 (mbits f) - 1).

(** Math.ulp *)
Definition fulp (f : fmt) (x : Z) : Z :=
  if is_nan f x || is_inf f x then mag f x
  else let be := biased_exp f x in
       let q := (if be =? 0 then 1 else be) - 1 + emin_ulp f in
       round f false 1 q.

(** Math.nextUp / nextDown (an argument NaN is returned) *)
Definition fnext_up (f : fmt) (x : Z) : Z :=
  let x := norm f x in
  if is_nan f x || (x =? inf_bits f false) then x
  else if is_zero f x then 1
  else if sign_bit f x then x - 1 else x + 1.
Definition fnext_down (f : fmt) (x : Z) : Z :=
  let x := norm f x in
  if is_nan f x || (x =? inf_bits f true) then x
  else if is_zero f x then sgn_mask f + 1
  else if sign_bit f x then x + 1 else x - 1.

(** Math.nextAfter(start, direction) for a direction already in the start's format, or
    compared as given by [lt]/[gt]/[eq] (float start, double direction). *)
Definition fnext_after (f : fmt) (start : Z) (gt lt eq : bool) (dir_as_start : Z) (nan : bool) : Z :=
  let x := norm f start in
  if gt then (if is_zero f x then sgn_mask f + 1 else if sign_bit f x then x + 1 else x - 1)
  else if lt then (let y := if is_negzero f x then 0 else x in if sign_bit f y then y - 1 else y + 1)
  else if eq then dir_as_start
  else qnan f.

(** Math.scalb(d, n): d * 2^n rounded once. *)
Definition fscalb (f : fmt) (x n : Z) : Z :=
  match decode f x with
  | Fin s m e => if m =? 0 then norm f x else
                 let n' := Z.max (-4000) (Z.min 4000 n) in round f s m (e + n')
  | _ => norm f x
  end.

(** Math.getExponent *)
Definition fget_exponent (f : fmt) (x : Z) : Z := biased_exp f x - bias f.

(** Math.IEEEremainder: x - n*y, n the integer nearest x/y (ties even); exact. *)
Definition fremainder (f : fmt) (x y : Z) : Z :=
  match decode f x, decode f y with
  | NaN, _ | _, NaN => qnan f
  | Inf _, _ => qnan f
  | Fin _ _ _, Inf _ => norm f x
  | Fin sx mx ex, Fin sy my ey =>
      if my =? 0 then qnan f else if mx =? 0 then norm f x else
      let e := Z.min ex ey in
      let a := Z.shiftl mx (ex - e) in
      let b := Z.shiftl my (ey - e) in
      let q := a / b in
      let r := a - q * b in
      let n := if (2 * r <? b) then q else if (b <? 2 * r) then q + 1 else (if Z.even q then q else q + 1) in
      let res := a - n * b in
      if res =? 0 then zero_bits f sx
      else round f (xorb sx (res <? 0)) (Z.abs res) e
  end.

(** Is the double [x] a finite integer (and odd)? *)
Definition int_of (f : fmt) (x : Z) : option Z :=
  match decode f x with
  | Fin s m e => if 0 <=? e then Some (signed s (Z.shiftl m e))
                 else if Z.land m (pow2 (- e) - 1) =? 0 then Some (signed s (Z.shiftr m (- e))) else None
  | _ => None
  end.

(** The exact value (-1)^s * m * 2^e as a double, if representable. *)
Definition exact (f : fmt) (s : bool) (m e : Z) : option Z :=
  if m =? 0 then Some (zero_bits f s) else
  let r := round f s m e in
  match decode f r with
  | Fin _ m' e' => if (e' <=? e) && (Z.shiftl m (e - e') =? m') then Some r
                   else if (e <? e') && (Z.shiftl m' (e' - e) =? m) then Some r else None
  | _ => None
  end.

(** Math.pow where the specification fixes the result; None otherwise. *)
Definition fpow (f : fmt) (x y : Z) : option Z :=
  let pinf := inf_bits f false in
  let ninf := inf_bits f true in
  let odd_int := match int_of f y with Some n => Z.odd n | None => false end in
  let ax := mag f x in
  let gt1 := flt f (one f) ax in
  let lt1 := flt f ax (one f) in
  if is_zero f y then Some (one f)
  else if norm f y =? one f then Some (norm f x)
  else if is_nan f y then Some (qnan f)
  else if is_nan f x then Some (qnan f)
  else if is_inf f y then
    if (gt1 && negb (sign_bit f y)) || (lt1 && sign_bit f y) then Some pinf
    else if (gt1 && sign_bit f y) || (lt1 && negb (sign_bit f y)) then Some (zero_bits f false)
    else Some (qnan f)
  else if is_poszero f x then Some (if sign_bit f y then pinf else zero_bits f false)
  else if norm f x =? pinf then Some (if sign_bit f y then zero_bits f false else pinf)
  else if is_negzero f x then
    Some (if negb (sign_bit f y) then (if odd_int then zero_bits f true else zero_bits f false)
          else (if odd_int then ninf else pinf))
  else if norm f x =? ninf then
    Some (if sign_bit f y then (if odd_int then zero_bits f true else zero_bits f false)
          else (if odd_int then ninf else pinf))
  else
    match int_of f y with
    | None => if sign_bit f x then Some (qnan f) else None
    | Some n =>
        match int_of f x, decode f x with
        | Some _, Fin s m e =>
            (* x = ±m0 * 2^e0 with m0 odd: x^n is a double only if m0 = 1 or m0^n < 2^(mbits+1) *)
            let k := Z.log2 (Z.land m (- m)) in
            let m0 := Z.shiftr m k in
            let e0 := e + k in
            let sg := s && Z.odd n in
            if m0 =? 1 then (if (n * e0 <? -5000) || (5000 <? n * e0) then None else exact f sg 1 (e0 * n))
            else if (n <? 0) || (64 <? n) then None
            else exact f sg (Z.pow m0 n) (e0 * n)
        | _, _ => None
        end
    end.

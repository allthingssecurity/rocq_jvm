(** * Decimal conversion of float and double (JDK 21)

    [to_dec f x]: the string of [Double.toString] / [Float.toString] (also
    String.valueOf, StringBuilder.append and string concatenation), as the JDK 19+
    javadoc of Double.toString(double) specifies it: the decimal of the rounding
    interval of [x] with the fewest digits (when that is one digit, decimals of one or
    two digits compete), closest to [x], ties to the even significand; plain notation
    for 10^-3 <= |d| < 10^7, otherwise computerized scientific notation.

    [parse f u]: Double.parseDouble / Float.parseFloat (and valueOf) of the UTF-16
    units [u], as jdk.internal.math.FloatingDecimal.readJavaFormatString and
    parseHexString accept them (trim, sign, NaN, Infinity, decimal digits with at most
    one point, an exponent, a final f/F/d/D, hexadecimal significands with a binary
    exponent) with the JDK's NumberFormatException messages; the value is the exact
    decimal (or hexadecimal) number rounded once to the format (round to nearest, ties to
    even), as the JDK computes it.

    Everything is exact integer arithmetic on [Z]. *)

From Stdlib Require Import ZArith List Bool String Ascii.
From JVM.Core Require Import Float.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope Z_scope.

Definition pow10 (n : Z) : Z := Z.pow 10 n.

(** 10^k <= a/b (a, b > 0). *)
Definition le_pow10 (k a b : Z) : bool :=
  if 0 <=? k then pow10 k * b <=? a else b <=? a * pow10 (- k).

Fixpoint adj_down (fuel : nat) (k a b : Z) : Z :=
  match fuel with O => k | S f => if le_pow10 k a b then k else adj_down f (k - 1) a b end.
Fixpoint adj_up (fuel : nat) (k a b : Z) : Z :=
  match fuel with O => k | S f => if le_pow10 (k + 1) a b then adj_up f (k + 1) a b else k end.

(** The largest k with 10^k <= a/b. *)
Definition flog10 (a b : Z) : Z :=
  let k0 := ((Z.log2 a - Z.log2 b) * 30103) / 100000 in
  adj_up 8 (adj_down 8 (k0 + 1) a b) a b.

Definition cdiv (a b : Z) : Z := - ((- a) / b).

(** Decimal digits of n > 0 (most significant first). *)
Fixpoint digits_rev (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => nil
  | S f => if n <=? 0 then nil else (n mod 10) :: digits_rev f (n / 10)
  end.
Definition digits (n : Z) : list Z := rev (digits_rev 400 n).
Definition ndigits (n : Z) : Z := if n <=? 0 then 0 else flog10 n 1 + 1.

Fixpoint strip0 (fuel : nat) (s i : Z) : Z * Z :=
  match fuel with
  | O => (s, i)
  | S f => if (0 <? s) && (s mod 10 =? 0) then strip0 f (s / 10) (i + 1) else (s, i)
  end.

(** ** Selection of the decimal *)

(** The rounding interval of M*2^E as numerators over a common denominator [d]:
    (low, high, value, d, endpoints included). *)
Definition interval (f : fmt) (x : Z) : option (Z * Z * Z * Z * bool) :=
  match decode f x with
  | Fin _ m e =>
      if m <=? 0 then None else
      let boundary := (fraction f x =? 0) && (1 <? biased_exp f x) in
      let l4 := 4 * m - (if boundary then 1 else 2) in
      let u4 := 4 * m + 2 in
      let incl := Z.even m in
      if 0 <=? e - 2 then Some (l4 * pow2 (e - 2), u4 * pow2 (e - 2), 4 * m * pow2 (e - 2), 1, incl)
      else Some (l4, u4, 4 * m, pow2 (2 - e), incl)
  | _ => None
  end.

(** The integers s with s * 10^i in the interval. *)
Definition srange (lo hi d : Z) (incl : bool) (i : Z) : Z * Z :=
  let '(a, a', b) := if 0 <=? i then (lo, hi, d * pow10 i) else (lo * pow10 (- i), hi * pow10 (- i), d) in
  let smin := if incl then cdiv a b else a / b + 1 in
  let smax := if incl then a' / b else cdiv a' b - 1 in
  (smin, smax).

Fixpoint find_imax (fuel : nat) (lo hi d : Z) (incl : bool) (i : Z) : option Z :=
  match fuel with
  | O => None
  | S f => let '(a, b) := srange lo hi d incl i in
           if a <=? b then Some i else find_imax f lo hi d incl (i - 1)
  end.

Fixpoint zrange (fuel : nat) (a b : Z) : list Z :=
  match fuel with O => nil | S f => if b <? a then nil else a :: zrange f (a + 1) b end.

(** The decimals of at most [pl] digits in the interval, from exponent [i] down. *)
Fixpoint cands (fuel : nat) (lo hi d : Z) (incl : bool) (pl i : Z) : list (Z * Z) :=
  match fuel with
  | O => nil
  | S f =>
      let '(a, b) := srange lo hi d incl i in
      if pow10 pl <=? a then nil
      else app (map (fun s => (s, i)) (zrange 200 a (Z.min b (pow10 pl - 1)))) (cands f lo hi d incl pl (i - 1))
  end.

(** |s * 10^i - v/d| * d * 10^g, an integer for i + g >= 0. *)
Definition dist (v d g : Z) (c : Z * Z) : Z :=
  Z.abs (fst c * pow10 (snd c + g) * d - v * pow10 g).

Definition even_sig (c : Z * Z) : bool := Z.even (fst (strip0 400 (fst c) (snd c))).

Definition closest (v d g : Z) (l : list (Z * Z)) : option (Z * Z) :=
  fold_left (fun acc c => match acc with
                          | None => Some c
                          | Some b => let db := dist v d g b in let dc := dist v d g c in
                                      if dc <? db then Some c
                                      else if (dc =? db) && even_sig c && negb (even_sig b) then Some c
                                      else acc
                          end) l None.

(** The selected decimal (s, i) of a positive finite [x], s not a multiple of 10. *)
Definition select (f : fmt) (x : Z) : option (Z * Z) :=
  match interval f x with
  | None => None
  | Some (lo, hi, v, d, incl) =>
      match find_imax 60 lo hi d incl (flog10 hi d) with
      | None => None
      | Some im =>
          let '(a, _) := srange lo hi d incl im in
          let p := ndigits a in
          let pl := Z.max p 2 in
          let cs := cands 8 lo hi d incl pl im in
          let low := fold_left (fun m c => Z.min m (snd c)) cs im in
          match closest v d (Z.max 0 (- low)) cs with
          | Some (s, i) => Some (strip0 400 s i)
          | None => None
          end
      end
  end.

(** ** Formatting *)

Definition dchar (k : Z) : Z := 48 + k.
Definition units_of_digits (l : list Z) : list Z := map dchar l.

Definition int_units (n : Z) : list Z :=
  if n =? 0 then [48] else if n <? 0 then 45 :: units_of_digits (digits (- n)) else units_of_digits (digits n).

Definition zeros (n : Z) : list Z := repeat 48 (Z.to_nat n).

Definition format (s i : Z) : list Z :=
  let ds := units_of_digits (digits s) in
  let n := Z.of_nat (List.length ds) in
  let e := n + i - 1 in
  if (-3 <=? e) && (e <? 0) then app [48; 46] (app (zeros (- (n + i))) ds)
  else if (0 <=? e) && (e <? 7) then
    if 0 <=? i then app ds (app (zeros i) [46; 48])
    else app (firstn (Z.to_nat (n + i)) ds) (46 :: skipn (Z.to_nat (n + i)) ds)
  else
    match ds with
    | [d1] => app [d1; 46; 48; 69] (int_units e)
    | d1 :: r => app (d1 :: 46 :: r) (69 :: int_units e)
    | nil => nil
    end.

Fixpoint ascii (s : string) : list Z :=
  match s with EmptyString => nil | String c r => Z.of_nat (nat_of_ascii c) :: ascii r end.

(** Double.toString / Float.toString; None only for an impossible decode. *)
Definition to_dec (f : fmt) (x : Z) : option (list Z) :=
  let x := norm f x in
  if is_nan f x then Some (ascii "NaN")
  else if is_inf f x then Some (if sign_bit f x then ascii "-Infinity" else ascii "Infinity")
  else if is_zero f x then Some (if sign_bit f x then ascii "-0.0" else ascii "0.0")
  else
    let ax := if sign_bit f x then neg f x else x in
    match select f ax with
    | Some (s, i) => let u := format s i in Some (if sign_bit f x then 45 :: u else u)
    | None => None
    end.

(** Double.toHexString / Float.toHexString: "0x1." (normal) or "0x0." (subnormal) and the
    52-bit significand field as 13 hex digits with the trailing zeros dropped (at least one digit
    kept), then "p" and the unbiased exponent (-1022 / -126 for subnormals). A float's 23-bit field
    is the top of the 52-bit one (the JDK widens it to double, scaling subnormals). *)
Fixpoint hex_digits (n : nat) (v : Z) (acc : list Z) : list Z :=
  match n with
  | O => acc
  | S n' => let d := Z.land v 15 in
            hex_digits n' (Z.shiftr v 4) ((if d <? 10 then 48 + d else 87 + d) :: acc)
  end.

Fixpoint drop_lead_zeros (l : list Z) : list Z :=
  match l with d :: r => if d =? 48 then drop_lead_zeros r else l | nil => nil end.

Definition to_hex (f : fmt) (x : Z) : list Z :=
  let x := norm f x in
  if is_nan f x then ascii "NaN"
  else if is_inf f x then (if sign_bit f x then ascii "-Infinity" else ascii "Infinity")
  else
    let sg := if sign_bit f x then [45] else nil in
    if is_zero f x then app sg (ascii "0x0.0p0")
    else
      let field := Z.shiftl (fraction f x) (52 - mbits f) in
      let ds := match rev (drop_lead_zeros (rev (hex_digits 13 field nil))) with nil => [48] | r => r end in
      let sub := is_subnormal f x in
      let e := if sub then 1 - bias f else biased_exp f x - bias f in
      app sg (app (ascii (if sub then "0x0." else "0x1.")) (app ds (112 :: int_units e))).

Definition dtoa (x : Z) : option (list Z) := to_dec binary64 x.
Definition ftoa (x : Z) : option (list Z) := to_dec binary32 x.

(** ** Parsing *)

(** The value (-1)^neg * c * 10^q rounded to the format. *)
Definition round_dec (f : fmt) (neg : bool) (c q : Z) : Z :=
  if c <=? 0 then zero_bits f neg else
  let n10 := q + ndigits c - 1 in
  if 400 <=? n10 then inf_bits f neg
  else if n10 <=? -400 then zero_bits f neg
  else if 0 <=? q then round f neg (c * pow10 q) 0
  else
    let den := pow10 (- q) in
    let k := Z.max 0 (mbits f + 4 + Z.log2 den - Z.log2 c) in
    let '(qq, r) := Z.div_eucl (Z.shiftl c k) den in
    round f neg (2 * qq + (if r =? 0 then 0 else 1)) (- k - 1).

(** The value (-1)^neg * h * 2^e rounded to the format (h >= 0). *)
Definition round_bin (f : fmt) (neg : bool) (h e : Z) : Z :=
  if h <=? 0 then zero_bits f neg else
  let top := Z.log2 h + e in
  if 4000 <=? top then inf_bits f neg
  else if top <=? -4000 then zero_bits f neg
  else round f neg h e.

Inductive presult := PVal (bits : Z) | PErr (msg : list Z).

Definition is_ws (c : Z) : bool := c <=? 32.
Fixpoint drop_ws (l : list Z) : list Z := match l with c :: r => if is_ws c then drop_ws r else l | nil => nil end.
Definition trim (l : list Z) : list Z := rev (drop_ws (rev (drop_ws l))).

Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition hexval (c : Z) : option Z :=
  if is_digit c then Some (c - 48)
  else if (97 <=? c) && (c <=? 102) then Some (c - 87)
  else if (65 <=? c) && (c <=? 70) then Some (c - 55)
  else None.

Definition for_input (u : list Z) : presult :=
  PErr (app (ascii "For input string: """) (app u [34])).

Fixpoint list_eqb (a b : list Z) : bool :=
  match a, b with nil, nil => true | x :: r, y :: r' => (x =? y) && list_eqb r r' | _, _ => false end.

Fixpoint span_hex (l : list Z) : list Z * list Z :=
  match l with
  | c :: r => match hexval c with Some _ => let '(a, b) := span_hex r in (c :: a, b) | None => (nil, l) end
  | nil => (nil, nil)
  end.
Fixpoint span_dec (l : list Z) : list Z * list Z :=
  match l with
  | c :: r => if is_digit c then let '(a, b) := span_dec r in (c :: a, b) else (nil, l)
  | nil => (nil, nil)
  end.

Definition hex_int (l : list Z) : Z := fold_left (fun acc c => match hexval c with Some v => acc * 16 + v | None => acc end) l 0.
Definition dec_int (l : list Z) : Z := fold_left (fun acc c => acc * 10 + (c - 48)) l 0.

(** An optional sign: (negative, rest). *)
Definition sign_of (l : list Z) : bool * list Z :=
  match l with
  | c :: r => if c =? 45 then (true, r) else if c =? 43 then (false, r) else (false, l)
  | nil => (false, nil)
  end.

Definition is_suffix (c : Z) : bool := (c =? 102) || (c =? 70) || (c =? 100) || (c =? 68).

(** parseHexString: ([-+])?0[xX](hex+ .? | hex* . hex+)[pP]([-+])?digit+[fFdD]? *)
Definition parse_hex (f : fmt) (u : list Z) : presult :=
  let '(neg, r0) := sign_of u in
  match r0 with
  | z :: x :: r1 =>
      if negb (z =? 48) || negb ((x =? 120) || (x =? 88)) then for_input u else
      let '(ip, r2) := span_hex r1 in
      let '(fp, hasdot, r3) := match r2 with
                               | c :: r => if c =? 46 then let '(a, b) := span_hex r in (a, true, b) else (nil, false, r2)
                               | nil => (nil, false, r2)
                               end in
      if (Nat.eqb (List.length ip) 0) && (negb hasdot || Nat.eqb (List.length fp) 0) then for_input u else
      match r3 with
      | pc :: r4 =>
          if negb ((pc =? 112) || (pc =? 80)) then for_input u else
          let '(eneg, r5) := sign_of r4 in
          let '(ed, r6) := span_dec r5 in
          let okend := match r6 with nil => true | [c] => is_suffix c | _ => false end in
          if Nat.eqb (List.length ed) 0 || negb okend then for_input u else
          let h := hex_int (app ip fp) in
          if h =? 0 then PVal (zero_bits f neg) else
          let ev := dec_int ed in
          if 2147483647 <? ev then PVal (if eneg then zero_bits f neg else inf_bits f neg)
          else PVal (round_bin f neg h ((if eneg then - ev else ev) - 4 * Z.of_nat (List.length fp)))
      | nil => for_input u
      end
  | _ => for_input u
  end.

(** readJavaFormatString after the sign: leading zeros and points, then digits. *)
Fixpoint lead_zeros (l : list Z) (nlz : Z) (dec : option Z) (pos : Z) : option (Z * option Z * Z * list Z) :=
  match l with
  | c :: r =>
      if c =? 48 then lead_zeros r (nlz + 1) dec (pos + 1)
      else if c =? 46 then match dec with Some _ => None | None => lead_zeros r nlz (Some pos) (pos + 1) end
      else Some (nlz, dec, pos, l)
  | nil => Some (nlz, dec, pos, l)
  end.

(** digits (reversed), number of digits, trailing zeros, decimal point, position, rest; None:
    multiple points. *)
Fixpoint dig_loop (l : list Z) (ds : list Z) (nd ntz : Z) (dec : option Z) (pos : Z)
  : option (list Z * Z * Z * option Z * Z * list Z) :=
  match l with
  | c :: r =>
      if (49 <=? c) && (c <=? 57) then dig_loop r (c :: ds) (nd + 1) 0 dec (pos + 1)
      else if c =? 48 then dig_loop r (c :: ds) (nd + 1) (ntz + 1) dec (pos + 1)
      else if c =? 46 then match dec with Some _ => None | None => dig_loop r ds nd ntz (Some pos) (pos + 1) end
      else Some (ds, nd, ntz, dec, pos, l)
  | nil => Some (ds, nd, ntz, dec, pos, nil)
  end.

Definition multiple_points : presult := PErr (ascii "multiple points").

Definition parse (f : fmt) (u0 : list Z) : presult :=
  let u := trim u0 in
  match u with
  | nil => PErr (ascii "empty String")
  | c0 :: _ =>
    let '(neg, sign, r) := if c0 =? 45 then (true, true, tl u) else if c0 =? 43 then (false, true, tl u) else (false, false, u) in
    let off := if sign then 1 else 0 in
    match r with
    | nil => for_input u
    | c :: _ =>
      if c =? 78 then (if list_eqb r (ascii "NaN") then PVal (qnan f) else for_input u)
      else if c =? 73 then (if list_eqb r (ascii "Infinity") then PVal (inf_bits f neg) else for_input u)
      else if (c =? 48) && match r with _ :: x :: _ => (x =? 120) || (x =? 88) | _ => false end then parse_hex f u
      else
      match lead_zeros r 0 None off with
      | None => multiple_points
      | Some (nlz, dec, pos, r1) =>
        match dig_loop r1 nil 0 0 dec pos with
        | None => multiple_points
        | Some (dsr, nd0, ntz, dec', _, r2) =>
          let nd := nd0 - ntz in
          let iszero := nd =? 0 in
          if iszero && (nlz =? 0) then for_input u else
          let decexp := match dec' with Some p => p - off - nlz | None => nd + ntz end in
          let sig := dec_int (firstn (Z.to_nat nd) (rev dsr)) in
          let fin (e : Z) (rest : list Z) :=
              match rest with
              | nil => if iszero then PVal (zero_bits f neg) else PVal (round_dec f neg sig (e - nd))
              | [s] => if is_suffix s then (if iszero then PVal (zero_bits f neg) else PVal (round_dec f neg sig (e - nd)))
                       else for_input u
              | _ => for_input u
              end in
          match r2 with
          | ec :: r3 =>
              if (ec =? 101) || (ec =? 69) then
                match r3 with
                | nil => for_input u
                | _ =>
                  let '(eneg, r4) := sign_of r3 in
                  let es := if eneg then -1 else 1 in
                  let '(ed, r5) := span_dec r4 in
                  if Nat.eqb (List.length ed) 0 then for_input u
                  else fin (decexp + es * dec_int ed) r5
                end
              else fin decexp r2
          | nil => fin decexp nil
          end
        end
      end
    end
  end.

Definition parse_double (u : list Z) : presult := parse binary64 u.
Definition parse_float (u : list Z) : presult := parse binary32 u.

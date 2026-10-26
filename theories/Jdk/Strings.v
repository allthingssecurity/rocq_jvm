(** * java.lang.String, StringBuilder, Character and Integer/Long text functions
    as pure functions on UTF-16 code-unit lists (JDK 21 semantics).

    A Java string is its sequence of UTF-16 code units ([list Z], each unit in
    [0, 65535]).  Each function here follows the JDK 21 source
    (java.base/java/lang/String.java, StringLatin1.java, StringUTF16.java,
    Integer.java, Long.java) including the clamping rules of the index
    arguments.  Exceptions are returned as [inl cls] (internal class name).

    Unicode tables are NOT built in: case mapping, digit values and the
    character classes are parameters ([uenv]); a theorem about code that uses
    them holds for every table satisfying the stated assumptions (usually
    only the ASCII facts in [uenv_ascii]).  The differential harness
    instantiates them with the tables of the real JDK. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int.
Import ListNotations.
Open Scope bool_scope.
Open Scope Z_scope.

Definition units := list Z.

(** ** Unicode environment *)
Record uenv := {
  u_upper : Z -> Z;        (** Character.toUpperCase(int codePoint) *)
  u_lower : Z -> Z;        (** Character.toLowerCase(int codePoint) *)
  u_digit : Z -> Z -> Z;   (** Character.digit(int codePoint, int radix), -1 if none *)
  u_is_whitespace : Z -> bool;  (** Character.isWhitespace(int) *)
  u_is_letter : Z -> bool;      (** Character.isLetter(int) *)
  u_is_digit : Z -> bool;       (** Character.isDigit(int) *)
  u_is_upper : Z -> bool;       (** Character.isUpperCase(int) *)
  u_is_lower : Z -> bool;       (** Character.isLowerCase(int) *)
}.

(** More of the JDK's Character data, read through [u_digit] at radix codes the JDK never uses
    (so that existing environments stay valid): 1000 = Character.getType, 1001 = property bits
    (1 isJavaIdentifierStart, 2 isJavaIdentifierPart, 4 isUnicodeIdentifierStart,
    8 isUnicodeIdentifierPart, 16 isIdentifierIgnorable, 32 isAlphabetic, 64 isIdeographic,
    128 isSpaceChar, 256 isTitleCase, 512 isDefined, 1024 isMirrored, 2048 Character.toUpperCaseEx
    differs from toUpperCase), 1002 = getNumericValue,
    1003 = the UTF-16 units of String.toUpperCase of the code point when special casing expands
    it (packed u1 + u2*2^16 + u3*2^32 + n*2^48), else -1. *)
Definition u_type (e : uenv) (c : Z) : Z := u_digit e c 1000.
Definition u_props (e : uenv) (c : Z) : Z := u_digit e c 1001.
Definition u_numeric (e : uenv) (c : Z) : Z := u_digit e c 1002.
Definition u_prop (e : uenv) (c bit : Z) : bool := Z.testbit (u_props e c) bit.
Definition u_upperx (e : uenv) (c : Z) : option (list Z) :=
  let x := u_digit e c 1003 in
  if x <? 2 ^ 48 then None   (* no expansion (also for environments that leave the code alone) *)
  else let n := Z.shiftr x 48 in
       Some (firstn (Z.to_nat n) [Z.land x 65535; Z.land (Z.shiftr x 16) 65535; Z.land (Z.shiftr x 32) 65535]).

(** ** String.toUpperCase / toLowerCase (default locale not tr/az/lt: the JDK then needs no
    context except for the final sigma, which is not modelled) *)
Definition utf16_of (cp : Z) : list Z :=
  if cp <? 65536 then [cp] else [Z.shiftr (cp - 65536) 10 + 55296; Z.land (cp - 65536) 1023 + 56320].

Fixpoint case_map (f : Z -> list Z) (a : list Z) : list Z :=
  match a with
  | nil => nil
  | c :: r =>
      if (55296 <=? c) && (c <=? 56319) then
        match r with
        | d :: r' => if (56320 <=? d) && (d <=? 57343)
                     then app (f (Z.shiftl (c - 55296) 10 + (d - 56320) + 65536)) (case_map f r')
                     else c :: case_map f r
        | nil => [c]
        end
      else if (56320 <=? c) && (c <=? 57343) then c :: case_map f r
      else app (f c) (case_map f r)
  end.

Definition upper_units (e : uenv) (a : list Z) : list Z :=
  case_map (fun cp => match u_upperx e cp with Some l => l | None => utf16_of (u_upper e cp) end) a.

(** None: the string has a GREEK CAPITAL LETTER SIGMA (its lower case depends on word boundaries). *)
Definition lower_units (e : uenv) (a : list Z) : option (list Z) :=
  if existsb (fun c => c =? 931) a then None
  else Some (case_map (fun cp => if cp =? 304 then [105; 775] else utf16_of (u_lower e cp)) a).

(** What every JDK satisfies on ASCII (checked against the real tables by the harness). *)
Definition ascii_upper (c : Z) : Z := if (97 <=? c) && (c <=? 122) then c - 32 else c.
Definition ascii_lower (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.
Definition uenv_ascii (e : uenv) : Prop :=
  forall c, 0 <= c < 128 -> u_upper e c = ascii_upper c /\ u_lower e c = ascii_lower c.

(** ** Basic *)
Fixpoint nth_unit (s : units) (i : Z) : option Z :=
  match s with
  | nil => None
  | c :: r => if i =? 0 then Some c else nth_unit r (i - 1)
  end.

Definition slen (s : units) : Z := Z.of_nat (length s).

(** [String.hashCode]: s[0]*31^(n-1) + ... + s[n-1], int arithmetic. *)
Definition str_hash (s : units) : Z := fold_left (fun h c => wrap32 (31 * h + c)) s 0.

Fixpoint units_eqb (a b : units) : bool :=
  match a, b with
  | nil, nil => true
  | x :: a', y :: b' => (x =? y) && units_eqb a' b'
  | _, _ => false
  end.

Lemma units_eqb_spec : forall a b, units_eqb a b = true <-> a = b.
Proof.
  induction a as [|x a IH]; destruct b as [|y b]; simpl; split; intros H; try congruence; auto.
  - apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply IH in H2. subst; auto.
  - inversion H; subst. apply andb_true_iff; split; [apply Z.eqb_refl | apply IH; auto].
Qed.

Definition SIOOBE := "java/lang/StringIndexOutOfBoundsException"%string.
Definition NFE := "java/lang/NumberFormatException"%string.

(** charAt: StringIndexOutOfBoundsException outside [0, length). *)
Definition char_at (s : units) (i : Z) : string + Z :=
  match nth_unit s i with Some c => inr c | None => inl SIOOBE end.

Definition sublist (s : units) (b e : Z) : units :=
  firstn (Z.to_nat (e - b)) (skipn (Z.to_nat b) s).

(** substring(b, e): SIOOBE if b < 0, b > e or e > length. *)
Definition substring2 (s : units) (b e : Z) : string + units :=
  if (b <? 0) || (e <? b) || (slen s <? e) then inl SIOOBE else inr (sublist s b e).

(** ** Searching *)
Definition MIN_SUPPLEMENTARY : Z := 65536.
Definition is_high_surrogate (c : Z) : bool := (55296 <=? c) && (c <=? 56319).
Definition is_low_surrogate (c : Z) : bool := (56320 <=? c) && (c <=? 57343).
Definition is_surrogate (c : Z) : bool := (55296 <=? c) && (c <=? 57343).
Definition valid_code_point (cp : Z) : bool := (0 <=? cp) && (cp <=? 1114111).
Definition high_of (cp : Z) : Z := (cp - 65536) / 1024 + 55296.
Definition low_of (cp : Z) : Z := (cp - 65536) mod 1024 + 56320.
Definition to_code_point (hi lo : Z) : Z := (hi - 55296) * 1024 + (lo - 56320) + 65536.

Fixpoint index_from (p : units -> bool) (s : units) (i : Z) : Z :=
  match s with
  | nil => -1
  | _ :: r => if p s then i else index_from p r (i + 1)
  end.

(** indexOf(int ch, int fromIndex) *)
Definition index_of_char (s : units) (ch from : Z) : Z :=
  let from := Z.max from 0 in
  if slen s <=? from then -1 else
  let pred :=
    if ch <? MIN_SUPPLEMENTARY then (fun t => match t with c :: _ => c =? ch | nil => false end)
    else if valid_code_point ch then
      (fun t => match t with c :: d :: _ => (c =? high_of ch) && (d =? low_of ch) | _ => false end)
    else (fun _ => false) in
  index_from pred (skipn (Z.to_nat from) s) from.

Fixpoint is_prefix (p s : units) : bool :=
  match p, s with
  | nil, _ => true
  | x :: p', y :: s' => (x =? y) && is_prefix p' s'
  | _ :: _, nil => false
  end.

(** indexOf(String str, int fromIndex) (String.indexOf(byte[], byte, int, String, int)) *)
Definition index_of_str (s t : units) (from : Z) : Z :=
  let n := slen s in let m := slen t in
  if n <=? from then (if m =? 0 then n else -1) else
  let from := Z.max from 0 in
  if m =? 0 then from else
  if n <? m then -1 else
  index_from (is_prefix t) (skipn (Z.to_nat from) s) from.

(** lastIndexOf(String str, int fromIndex) *)
Definition last_index_of_str (s t : units) (from : Z) : Z :=
  let n := slen s in let m := slen t in
  let right := n - m in
  let from := Z.min from right in
  if from <? 0 then -1 else
  if m =? 0 then from else
  (* largest i <= from with t a prefix of s[i..] *)
  fold_left (fun acc i => if is_prefix t (skipn (Z.to_nat i) s) then i else acc)
            (map Z.of_nat (seq 0 (S (Z.to_nat from)))) (-1).

(** lastIndexOf(int ch, int fromIndex) *)
Definition last_index_of_char (s : units) (ch from : Z) : Z :=
  let from := Z.min from (slen s - 1) in
  if from <? 0 then -1 else
  let at_i i :=
    if ch <? MIN_SUPPLEMENTARY then match nth_unit s i with Some c => c =? ch | None => false end
    else if valid_code_point ch then
      match nth_unit s i, nth_unit s (i + 1) with
      | Some c, Some d => (c =? high_of ch) && (d =? low_of ch)
      | _, _ => false
      end
    else false in
  fold_left (fun acc i => if at_i i then i else acc) (map Z.of_nat (seq 0 (S (Z.to_nat from)))) (-1).

(** startsWith(prefix, toffset) *)
Definition starts_with (s p : units) (off : Z) : bool :=
  if (off <? 0) || (slen s - slen p <? off) then false
  else is_prefix p (skipn (Z.to_nat off) s).

Definition ends_with (s p : units) : bool := starts_with s p (slen s - slen p).

(** compareTo *)
Fixpoint compare_units (a b : units) : Z :=
  match a, b with
  | x :: a', y :: b' => if x =? y then compare_units a' b' else x - y
  | _, _ => slen a - slen b
  end.

(** ** Case-insensitive equality (String.equalsIgnoreCase, JDK 21) *)
Definition is_latin1 (s : units) : bool := forallb (fun c => c <? 256) s.

(** CharacterDataLatin1.equalsIgnoreCase(byte, byte) *)
Definition latin1_eq_ci (b1 b2 : Z) : bool :=
  (b1 =? b2) ||
  (let up := Z.land b1 223 in
   (65 <=? up) && ((up <=? 90) || ((192 <=? up) && (up <=? 222) && negb (up =? 215)))
   && (up =? Z.land b2 223)).

(** StringUTF16.compareCodePointCI = 0 *)
Definition cp_eq_ci (e : uenv) (cp1 cp2 : Z) : bool :=
  let u1 := u_upper e cp1 in let u2 := u_upper e cp2 in
  (u1 =? u2) || (u_lower e u1 =? u_lower e u2).

(** StringUTF16.compareToCIImpl(...) = 0 for strings of equal length, as a
    walk over the two unit lists with the "codePointIncluding" rule. [pa],[pb]
    are the previous units (for a low surrogate at the current position). *)
Fixpoint utf16_eq_ci (e : uenv) (fuel : nat) (pa pb : option Z) (a b : units) : bool :=
  match fuel with
  | O => false
  | S k =>
    match a, b with
    | nil, _ | _, nil => true
    | c1 :: a', c2 :: b' =>
      if (c1 =? c2) || cp_eq_ci e c1 c2 then utf16_eq_ci e k (Some c1) (Some c2) a' b' else
      let incl (prev : option Z) (c : Z) (rest : units) : Z * bool :=
          (* code point including the unit, and whether the next unit is consumed *)
          if negb (is_surrogate c) then (c, false)
          else if is_low_surrogate c then
            match prev with
            | Some h => if is_high_surrogate h then (to_code_point h c, false) else (c, false)
            | None => (c, false)
            end
          else match rest with
               | l :: _ => if is_low_surrogate l then (to_code_point c l, true) else (c, false)
               | nil => (c, false)
               end in
      let (cp1, skip1) := incl pa c1 a' in
      let (cp2, skip2) := incl pb c2 b' in
      if negb (cp_eq_ci e cp1 cp2) then false else
      let a'' := if skip1 then tl a' else a' in
      let b'' := if skip2 then tl b' else b' in
      let pa' := if skip1 then hd_error a' else Some c1 in
      let pb' := if skip2 then hd_error b' else Some c2 in
      utf16_eq_ci e k pa' pb' a'' b''
    end
  end.

(** StringLatin1.regionMatchesCI_UTF16 (one side Latin-1, the other UTF-16) *)
Fixpoint mixed_eq_ci (e : uenv) (a b : units) : bool :=
  match a, b with
  | c1 :: a', c2 :: b' =>
      ((c1 =? c2) || (let u1 := u_upper e c1 in let u2 := u_upper e c2 in
                      (u1 =? u2) || (u_lower e u1 =? u_lower e u2)))
      && mixed_eq_ci e a' b'
  | _, _ => true
  end.

Fixpoint latin1_eqs (a b : units) : bool :=
  match a, b with
  | c1 :: a', c2 :: b' => latin1_eq_ci c1 c2 && latin1_eqs a' b'
  | _, _ => true
  end.

(** equalsIgnoreCase on two non-null strings (reference identity is checked
    by the caller and implies equal units anyway). *)
Definition equals_ignore_case (e : uenv) (a b : units) : bool :=
  (slen a =? slen b) &&
  (match is_latin1 a, is_latin1 b with
   | true, true => latin1_eqs a b
   | true, false => mixed_eq_ci e a b
   | false, true => mixed_eq_ci e b a
   | false, false => utf16_eq_ci e (S (length a)) None None a b
   end).

(** ** Simple transformations *)
(** trim(): strip units <= ' ' at both ends; [None] = unchanged (returns this). *)
Definition trim (s : units) : option units :=
  let drop := fix drop (l : units) := match l with c :: r => if c <=? 32 then drop r else l | nil => nil end in
  let t := rev (drop (rev (drop s))) in
  if Nat.eqb (length t) (length s) then None else Some t.

Definition replace_char (s : units) (o n : Z) : units := map (fun c => if c =? o then n else c) s.

(** ** Decimal conversion (Integer.toString / Long.toString / parseInt) *)
Fixpoint digits_rev (fuel : nat) (n : Z) : units :=
  match fuel with
  | O => nil
  | S k => (48 + n mod 10) :: (if n <? 10 then nil else digits_rev k (n / 10))
  end.

Definition z_to_units (z : Z) : units :=
  if z <? 0 then 45 :: rev (digits_rev 25 (- z)) else rev (digits_rev 25 z).

Definition bool_units (b : bool) : units :=
  if b then [116; 114; 117; 101] else [102; 97; 108; 115; 101].
Definition null_units : units := [110; 117; 108; 108].

(** Integer.parseInt(s, 10) / Long.parseLong: sign, then >= 1 digit with
    Character.digit(c, 10) >= 0, value within [lo, hi]. *)
Definition parse_dec (e : uenv) (lo hi : Z) (s : units) : string + Z :=
  let (neg, ds) := match s with
                   | 45 :: r => (true, r)
                   | 43 :: r => (false, r)
                   | _ => (false, s)
                   end in
  match ds with
  | nil => inl NFE
  | _ =>
    let v := fold_left (fun acc c => match acc with
                                     | None => None
                                     | Some n => let d := u_digit e c 10 in
                                                 if (d <? 0) || (9 <? d) then None
                                                 else if hi * 2 <? n then Some n   (* keep small, still out of range *)
                                                 else Some (n * 10 + d)
                                     end) ds (Some 0) in
    match v with
    | None => inl NFE
    | Some n => let r := if neg then - n else n in
                if (r <? lo) || (hi <? r) then inl NFE else inr r
    end
  end.

(** ** Examples (checked by computation) *)
Example hash_ex : str_hash [97; 98; 99] = 96354.  (* "abc".hashCode() *)
Proof. reflexivity. Qed.
Example idx_ex : index_of_str [97; 98; 97; 98] [98] 2 = 3.
Proof. reflexivity. Qed.
Example idx_empty : index_of_str [97] [] 5 = 1.
Proof. reflexivity. Qed.
Example last_ex : last_index_of_str [97; 98; 97; 98] [97; 98] 10 = 2.
Proof. reflexivity. Qed.
Example z_ex : z_to_units (-2147483648) = [45; 50; 49; 52; 55; 52; 56; 51; 54; 52; 56].
Proof. reflexivity. Qed.
Example latin1_ci : latin1_eq_ci 228 196 = true.   (* a-umlaut / A-umlaut *)
Proof. reflexivity. Qed.

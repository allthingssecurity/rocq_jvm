(** * Models of the JDK methods that Camel code calls (Phase 4).

    Each entry is a specification of one JDK 21 method, written from its
    source in java.base and checked by the differential harness against the
    real JDK.  This file is part of the trust base: TRUST.md lists every
    modelled method ("axiomatised natives and JDK models").

    Methods whose behaviour depends on the platform or configuration take it
    from [jenv]: the Unicode tables ([Strings.uenv]) and which slf4j levels are
    enabled.  A method that would call back into arbitrary bytecode
    (toString/equals/hashCode of a loaded class) is [MStuckModel]. *)

From Stdlib Require Import ZArith String Ascii List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics JdkTables Machine.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings.
Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.
Open Scope Z_scope.

Record jenv := {
  j_u : uenv;
  j_log_enabled : string -> bool;   (** "isDebugEnabled" etc. of slf4j loggers *)
}.

(** ** Helpers *)
Definition str_of (s : mstate) (v : value) : option (list Z) :=
  match v with
  | VRef l => match ms_heap s l with Some (OStr u) => Some u | _ => None end
  | _ => None
  end.

Definition set_heap (s : mstate) (l : Z) (o : object) : mstate :=
  {| ms_heap := upd (ms_heap s) l o; ms_next := ms_next s; ms_statics := ms_statics s;
     ms_inited := ms_inited s; ms_locks := ms_locks s; ms_frames := ms_frames s |}.

Definition option_bind {A B} (o : option A) (f : A -> option B) : option B := match o with Some a => f a | None => None end.

Definition ret_new (s : mstate) (o : object) : model_result :=
  let (l, s') := alloc s o in MOk (Some (VRef l)) s'.
Definition ret_lit (s : mstate) (u : list Z) : model_result :=
  let (l, s') := intern s (OStr u) in MOk (Some (VRef l)) s'.
Definition ret_int (s : mstate) (z : Z) : model_result := MOk (Some (VInt z)) s.
Definition ret_bool (s : mstate) (b : bool) : model_result := MOk (Some (VInt (if b then 1 else 0))) s.

Definition slen_v (l : list value) : Z := Z.of_nat (length l).
Definition value_eqb (a b : value) : bool :=
  match a, b with
  | VInt x, VInt y | VLong x, VLong y | VFloat x, VFloat y | VDouble x, VDouble y | VRef x, VRef y => Z.eqb x y
  | VNull, VNull => true
  | _, _ => false
  end.
Definition IAE := "java/lang/IllegalArgumentException".

Definition is_builtin_throwable (c : string) : bool :=
  match subclass nil 16 c "java/lang/Throwable" with Some true => true | _ => false end.

(** ** Boxing (java.lang.Integer/Long/Short/Byte/Character/Boolean).
    valueOf uses the caches required by the JLS 5.1.7 / the JDK: Integer, Long,
    Short in [-128, 127], Byte always, Character in [0, 127], Boolean.TRUE/FALSE.
    A box is an object with one field "value". *)
Definition box_obj (cls : string) (v : value) : object := OObj cls [("value", v)].

Definition box_cached (cls : string) (z : Z) : bool :=
  if String.eqb cls "java/lang/Character" then (0 <=? z) && (z <=? 127)
  else if String.eqb cls "java/lang/Boolean" || String.eqb cls "java/lang/Byte" then true
  else (-128 <=? z) && (z <=? 127).

Definition box (s : mstate) (cls : string) (v : value) : Z * mstate :=
  let z := match v with VInt z | VLong z => z | _ => 0 end in
  if box_cached cls z then
    let key := "#box:" ++ cls ++ ":" ++ intern_key (OStr (z_units z)) in
    match assoc key (ms_statics s) with
    | Some (VRef l) => (l, s)
    | _ => let (l, s1) := alloc s (box_obj cls v) in
           (l, {| ms_heap := ms_heap s1; ms_next := ms_next s1; ms_statics := (key, VRef l) :: ms_statics s1;
                  ms_inited := ms_inited s1; ms_locks := ms_locks s1; ms_frames := ms_frames s1 |})
    end
  else alloc s (box_obj cls v).

Definition box_value (s : mstate) (cls : string) (v : value) : option value :=
  match v with
  | VRef l => match ms_heap s l with
              | Some (OObj c [("value", w)]) => if String.eqb c cls then Some w else None
              | _ => None
              end
  | _ => None
  end.

Definition prim_desc (cls : string) : string :=
  if String.eqb cls "java/lang/Integer" then "I" else if String.eqb cls "java/lang/Long" then "J"
  else if String.eqb cls "java/lang/Short" then "S" else if String.eqb cls "java/lang/Byte" then "B"
  else if String.eqb cls "java/lang/Character" then "C" else if String.eqb cls "java/lang/Boolean" then "Z" else "?".

Definition is_box_class (cls : string) : bool := negb (String.eqb (prim_desc cls) "?").

Definition box_model (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  let pd := prim_desc cls in
  if String.eqb name "valueOf" && String.eqb desc ("(" ++ pd ++ ")L" ++ cls ++ ";") then
    match args with [v] => let (l, s') := box s cls v in MOk (Some (VRef l)) s' | _ => MStuckModel "valueOf" end
  else if String.eqb name "<get>TRUE" && String.eqb cls "java/lang/Boolean" then
    let (l, s') := box s cls (VInt 1) in MOk (Some (VRef l)) s'
  else if String.eqb name "<get>FALSE" && String.eqb cls "java/lang/Boolean" then
    let (l, s') := box s cls (VInt 0) in MOk (Some (VRef l)) s'
  else
  match args with
  | this :: more =>
    match box_value s cls this with
    | None => MNoModel
    | Some w =>
      let z := match w with VInt z | VLong z => z | _ => 0 end in
      let key := name ++ desc in
      if String.eqb key "intValue()I" then ret_int s (wrap32 z)
      else if String.eqb key "longValue()J" then MOk (Some (VLong z)) s
      else if String.eqb key "shortValue()S" then ret_int s (i2s z)
      else if String.eqb key "byteValue()B" then ret_int s (i2b z)
      else if String.eqb key "charValue()C" || String.eqb key "booleanValue()Z" then MOk (Some w) s
      else if String.eqb key "hashCode()I" then
        if String.eqb cls "java/lang/Long" then ret_int s (wrap32 (Z.lxor z (Z.shiftr (z mod 2 ^ 64) 32)))
        else if String.eqb cls "java/lang/Boolean" then ret_int s (if z =? 0 then 1237 else 1231)
        else ret_int s z
      else if String.eqb key "equals(Ljava/lang/Object;)Z" then
        match more with
        | [o] => ret_bool s (match box_value s cls o with Some w' => value_eqb w w' | None => false end)
        | _ => MStuckModel "equals"
        end
      else if String.eqb key "toString()Ljava/lang/String;" then
        if String.eqb cls "java/lang/Character" then ret_new s (OStr [z])
        else if String.eqb cls "java/lang/Boolean" then ret_lit s (bool_units (negb (z =? 0)))
        else ret_new s (OStr (z_units z))
      else if String.eqb name "compareTo" then
        match more with
        | [VNull] => MThrow NPE
        | [o] => match box_value s cls o with
                 | Some (VInt z' | VLong z') =>
                     if String.eqb cls "java/lang/Boolean" then ret_int s (z - z')
                     else if String.eqb cls "java/lang/Character" || String.eqb cls "java/lang/Short"
                             || String.eqb cls "java/lang/Byte" then ret_int s (z - z')
                     else ret_int s (lcmp z z')
                 | _ => MStuckModel "compareTo"
                 end
        | _ => MStuckModel "compareTo"
        end
      else MNoModel
    end
  | nil => MNoModel
  end.

(** ** java.lang.String *)
(** ** More String methods (JDK 21): repeat, isBlank, strip*, toUpperCase/toLowerCase of ASCII
    strings, replace(CharSequence, CharSequence), split on one literal character (the JDK's fast
    path; a real regular expression is STUCK), join of an array, compareToIgnoreCase of Latin-1
    strings. Results that the JDK returns as [this] or as the literal "" are those objects. *)
Definition empty_str (s : mstate) : Z * mstate := intern s (OStr nil).

Definition throw_with_msg (s : mstate) (cls : string) (u : list Z) : model_result :=
  let (m, s1) := alloc s (OStr u) in
  let (l, s2) := alloc s1 (OObj cls [("detailMessage", VRef m)]) in MThrowObj l s2.

(** A substring as String.substring returns it: [this], "", or a new String. *)
Definition seg (s : mstate) (this : value) (a : units) (b e : Z) : value * mstate :=
  if (b =? 0) && (e =? slen a) then (this, s)
  else if b =? e then let (l, s') := empty_str s in (VRef l, s')
  else let (l, s') := alloc s (OStr (sublist a b e)) in (VRef l, s').

Fixpoint repeat_units (a : units) (n : nat) : units := match n with O => nil | S k => app a (repeat_units a k) end.

Fixpoint drop_ws (u : uenv) (a : units) : units :=
  match a with c :: r => if u_is_whitespace u c then drop_ws u r else a | nil => nil end.

Definition split_meta : units := ascii_units ".$|()[{^?*+\".

Definition is_alnum (c : Z) : bool := ((48 <=? c) && (c <=? 57)) || ((97 <=? c) && (c <=? 122)) || ((65 <=? c) && (c <=? 90)).

(** The character of String.split's fast path, if the regex qualifies. *)
Definition split_char (r : units) : option Z :=
  match r with
  | [c] => if existsb (Z.eqb c) split_meta || is_surrogate c then None else Some c
  | [92; c] => if is_alnum c || is_surrogate c then None else Some c
  | _ => None
  end.

(** The segments of the fast path ([limit] as in the JDK). *)
Fixpoint split_go (fuel : nat) (a : units) (ch : Z) (off : Z) (limit : Z) (acc : list (Z * Z)) : list (Z * Z) * Z :=
  match fuel with
  | O => (rev acc, off)
  | S f =>
    let nxt := index_of_char a ch off in
    if nxt =? -1 then (rev acc, off)
    else if (limit <=? 0) || (Z.of_nat (length acc) <? limit - 1) then split_go f a ch (nxt + 1) limit ((off, nxt) :: acc)
    else (rev ((off, slen a) :: acc), slen a)
  end.

Fixpoint drop_empty_front (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | (b, e) :: r => if b =? e then drop_empty_front r else l
  | nil => nil
  end.
Definition drop_trailing_empty (l : list (Z * Z)) : list (Z * Z) := rev (drop_empty_front (rev l)).

Definition mk_segs (s : mstate) (this : value) (a : units) (l : list (Z * Z)) : list value * mstate :=
  fold_left (fun acc be => let (v, s1) := seg (snd acc) this a (fst be) (snd be) in (app (fst acc) [v], s1)) l (nil, s).

Definition do_split (s : mstate) (this : value) (a : units) (ch : Z) (limit : Z) : model_result :=
  let (segs, off) := split_go (S (length a)) a ch 0 limit nil in
  if off =? 0 then ret_new s (OArr (TRef "java/lang/String") [this])
  else
    let segs' := if (limit <=? 0) || (Z.of_nat (length segs) <? limit) then app segs [(off, slen a)] else segs in
    let segs'' := if limit =? 0 then drop_trailing_empty segs' else segs' in
    let (vs, s1) := mk_segs s this a segs'' in
    ret_new s1 (OArr (TRef "java/lang/String") vs).

(** replace(target, replacement) of Strings. *)
Fixpoint replace_go (fuel : nat) (a t r : units) : units :=
  match fuel with
  | O => a
  | S f => match a with
           | nil => nil
           | c :: rest => if is_prefix t a then app r (replace_go f (skipn (length t) a) t r) else c :: replace_go f rest t r
           end
  end.
Fixpoint intersperse_all (a r : units) : units :=
  match a with nil => r | c :: rest => app r (c :: intersperse_all rest r) end.

Definition string_model2 (e : jenv) (name desc : string) (this : value) (a : units) (rest : list value) (s : mstate) : model_result :=
  let u := j_u e in
  let key := name ++ desc in
  if String.eqb key "repeat(I)Ljava/lang/String;" then
    match rest with
    | [VInt n] =>
        if n <? 0 then throw_with_msg s "java/lang/IllegalArgumentException" (app (ascii_units "count is negative: ") (z_units n))
        else if n =? 1 then MOk (Some this) s
        else if (n =? 0) || Nat.eqb (length a) 0 then let (l, s') := empty_str s in MOk (Some (VRef l)) s'
        else if MAX_ARRAY <? slen a * n then MStuckModel "repeat: beyond the model bound"
        else ret_new s (OStr (repeat_units a (Z.to_nat n)))
    | _ => MStuckModel "repeat"
    end
  else if String.eqb key "isBlank()Z" then ret_bool s (forallb (u_is_whitespace u) a)
  else if String.eqb key "strip()Ljava/lang/String;" || String.eqb key "stripLeading()Ljava/lang/String;"
          || String.eqb key "stripTrailing()Ljava/lang/String;" then
    let l1 := if String.eqb name "stripTrailing" then a else drop_ws u a in
    let r := if String.eqb name "stripLeading" then l1 else rev (drop_ws u (rev l1)) in
    if Nat.eqb (length r) (length a) then MOk (Some this) s
    else if Nat.eqb (length r) 0 then let (l, s') := empty_str s in MOk (Some (VRef l)) s'
    else ret_new s (OStr r)
  else if String.eqb key "toUpperCase()Ljava/lang/String;" || String.eqb key "toLowerCase()Ljava/lang/String;" then
    (* ASCII only: other characters depend on the special casing rules and the locale *)
    if forallb (fun c => c <? 128) a then
      let r := map (if String.eqb name "toUpperCase" then ascii_upper else ascii_lower) a in
      if units_eqb r a then MOk (Some this) s else ret_new s (OStr r)
    else MStuckModel "toUpperCase/toLowerCase of a non-ASCII string (locale, special casing)"
  else if String.eqb key "replace(Ljava/lang/CharSequence;Ljava/lang/CharSequence;)Ljava/lang/String;" then
    match rest with
    | [VNull; _] | [_; VNull] => MThrow NPE
    | [tv; rv] =>
        match str_of s tv, str_of s rv with
        | Some t, Some r =>
            match t with
            | nil => ret_new s (OStr (intersperse_all a r))
            | _ => let res := replace_go (S (length a)) a t r in
                   if Z.eqb (index_of_str a t 0) (-1) then MOk (Some this) s else ret_new s (OStr res)
            end
        | _, _ => MStuckModel "replace: CharSequence that is not a String"
        end
    | _ => MStuckModel "replace"
    end
  else if String.eqb key "split(Ljava/lang/String;)[Ljava/lang/String;" || String.eqb key "split(Ljava/lang/String;I)[Ljava/lang/String;" then
    match rest with
    | VNull :: _ => MThrow NPE
    | rv :: lim =>
        match str_of s rv, lim with
        | Some r, ([] | [VInt _]) =>
            let limit := match lim with [VInt z] => z | _ => 0 end in
            match split_char r with
            | Some ch => do_split s this a ch limit
            | None => MStuckModel "split: a regular expression (only the one-character fast path is modelled)"
            end
        | _, _ => MStuckModel "split"
        end
    | _ => MStuckModel "split"
    end
  else if String.eqb key "compareToIgnoreCase(Ljava/lang/String;)I" then
    match rest with
    | [VNull] => MThrow NPE
    | [v] => match str_of s v with
             | Some b =>
                 if is_latin1 a && is_latin1 b then
                   let fix go (x y : units) : Z :=
                     match x, y with
                     | c1 :: r1, c2 :: r2 =>
                         if c1 =? c2 then go r1 r2 else
                         let d1 := u_upper u c1 in let d2 := u_upper u c2 in
                         if d1 =? d2 then go r1 r2 else
                         let f1 := u_lower u d1 in let f2 := u_lower u d2 in
                         if f1 =? f2 then go r1 r2 else f1 - f2
                     | _, _ => slen x - slen y
                     end in
                   ret_int s (go a b)
                 else MStuckModel "compareToIgnoreCase of non-Latin-1 strings"
             | None => MStuckModel "compareToIgnoreCase"
             end
    | _ => MStuckModel "compareToIgnoreCase"
    end
  else MNoModel.

(** String.join(CharSequence, CharSequence...) with String (or null) elements. *)
Definition string_join (s : mstate) (args : list value) : model_result :=
  match args with
  | [VNull; _] | [_; VNull] => MThrow NPE
  | [dv; VRef arr] =>
      match str_of s dv, ms_heap s arr with
      | Some d, Some (OArr _ es) =>
          let parts := map (fun v => match v with VNull => Some null_units | _ => str_of s v end) es in
          if forallb (fun o => match o with Some _ => true | None => false end) parts then
            let us := map (fun o => match o with Some x => x | None => nil end) parts in
            let res := match us with
                       | nil => nil
                       | x :: r => app x (fold_right (fun y acc => app d (app y acc)) nil r)
                       end in
            ret_new s (OStr res)
          else MStuckModel "join: an element that is not a String"
      | _, _ => MStuckModel "join"
      end
  | _ => MStuckModel "join"
  end.

Definition string_model (e : jenv) (name desc : string) (args : list value) (s : mstate) : model_result :=
  let u := j_u e in
  match args with
  | nil => MNoModel
  | this :: rest =>
  match str_of s this with
  | None => MNoModel
  | Some a =>
    match string_model2 e name desc this a rest s with MNoModel =>
    let key := name ++ desc in
    if String.eqb key "length()I" then ret_int s (slen a)
    else if String.eqb key "isEmpty()Z" then ret_bool s (Nat.eqb (length a) 0)
    else if String.eqb key "hashCode()I" then ret_int s (str_hash a)
    else if String.eqb key "toString()Ljava/lang/String;" then MOk (Some this) s
    else if String.eqb key "intern()Ljava/lang/String;" then ret_lit s a
    else if String.eqb key "charAt(I)C" then
      match rest with
      | [VInt i] => match char_at a i with inr c => ret_int s c | inl x => MThrow x end
      | _ => MStuckModel "charAt args"
      end
    else if String.eqb key "equals(Ljava/lang/Object;)Z" then
      match rest with
      | [VNull] => ret_bool s false
      | [v] => match str_of s v with Some b => ret_bool s (units_eqb a b) | None => ret_bool s false end
      | _ => MStuckModel "equals args"
      end
    else if String.eqb key "equalsIgnoreCase(Ljava/lang/String;)Z" then
      match rest with
      | [VNull] => ret_bool s false
      | [v] => match str_of s v with Some b => ret_bool s (equals_ignore_case u a b) | None => MStuckModel "eqIC" end
      | _ => MStuckModel "equalsIgnoreCase args"
      end
    else if String.eqb key "compareTo(Ljava/lang/String;)I" then
      match rest with
      | [VNull] => MThrow NPE
      | [v] => match str_of s v with Some b => ret_int s (compare_units a b) | None => MStuckModel "compareTo" end
      | _ => MStuckModel "compareTo args"
      end
    else if String.eqb key "indexOf(I)I" then
      match rest with [VInt c] => ret_int s (index_of_char a c 0) | _ => MStuckModel "indexOf" end
    else if String.eqb key "indexOf(II)I" then
      match rest with [VInt c; VInt f] => ret_int s (index_of_char a c f) | _ => MStuckModel "indexOf" end
    else if String.eqb key "lastIndexOf(I)I" then
      match rest with [VInt c] => ret_int s (last_index_of_char a c (slen a - 1)) | _ => MStuckModel "lastIndexOf" end
    else if String.eqb key "lastIndexOf(II)I" then
      match rest with [VInt c; VInt f] => ret_int s (last_index_of_char a c f) | _ => MStuckModel "lastIndexOf" end
    else if String.eqb key "indexOf(Ljava/lang/String;)I" || String.eqb key "indexOf(Ljava/lang/String;I)I"
            || String.eqb key "lastIndexOf(Ljava/lang/String;)I" || String.eqb key "lastIndexOf(Ljava/lang/String;I)I"
            || String.eqb key "contains(Ljava/lang/CharSequence;)Z" || String.eqb key "startsWith(Ljava/lang/String;)Z"
            || String.eqb key "startsWith(Ljava/lang/String;I)Z" || String.eqb key "endsWith(Ljava/lang/String;)Z"
            || String.eqb key "concat(Ljava/lang/String;)Ljava/lang/String;" then
      match rest with
      | VNull :: more =>
        (* startsWith(prefix, toffset) returns false for toffset < 0 before reading prefix *)
        match more with
        | [VInt i] => if String.eqb name "startsWith" && (i <? 0) then ret_bool s false else MThrow NPE
        | _ => MThrow NPE
        end
      | v :: more =>
        match str_of s v with
        | None => MStuckModel "String argument is not a String (CharSequence callback)"
        | Some b =>
          match more with
          | nil =>
            if String.eqb name "indexOf" then ret_int s (index_of_str a b 0)
            else if String.eqb name "lastIndexOf" then ret_int s (last_index_of_str a b (slen a))
            else if String.eqb name "contains" then ret_bool s (0 <=? index_of_str a b 0)
            else if String.eqb name "startsWith" then ret_bool s (starts_with a b 0)
            else if String.eqb name "endsWith" then ret_bool s (ends_with a b)
            else (* concat *)
              if Nat.eqb (length b) 0 then MOk (Some this) s
              else if Nat.eqb (length a) 0 then MOk (Some v) s
              else ret_new s (OStr (app a b))
          | [VInt i] =>
            if String.eqb name "indexOf" then ret_int s (index_of_str a b i)
            else if String.eqb name "lastIndexOf" then ret_int s (last_index_of_str a b i)
            else ret_bool s (starts_with a b i)
          | _ => MStuckModel "string search args"
          end
        end
      | nil => MStuckModel "string search args"
      end
    else if String.eqb key "substring(I)Ljava/lang/String;" || String.eqb key "substring(II)Ljava/lang/String;" then
      let be := match rest with
                | [VInt b] => Some (b, slen a)
                | [VInt b; VInt e] => Some (b, e)
                | _ => None
                end in
      match be with
      | None => MStuckModel "substring args"
      | Some (b, en) =>
        match substring2 a b en with
        | inl x => MThrow x
        | inr r => if (b =? 0) && (en =? slen a) then MOk (Some this) s
                   else if Nat.eqb (length r) 0 then ret_lit s nil
                   else ret_new s (OStr r)
        end
      end
    else if String.eqb key "trim()Ljava/lang/String;" then
      match trim a with
      | None => MOk (Some this) s
      | Some t => if Nat.eqb (length t) 0 then ret_lit s nil else ret_new s (OStr t)
      end
    else if String.eqb key "replace(CC)Ljava/lang/String;" then
      match rest with
      | [VInt o; VInt n] =>
          if (o =? n) || negb (existsb (Z.eqb o) a) then MOk (Some this) s
          else ret_new s (OStr (replace_char a o n))
      | _ => MStuckModel "replace args"
      end
    else if String.eqb key "toCharArray()[C" then ret_new s (OArr TChar (map VInt a))
    else MNoModel
    | r => r
    end
  end
  end.

Definition ITE := "java/lang/reflect/InvocationTargetException".

Fixpoint number (l : list instr) (k : Z) : list (pc * instr) :=
  match l with nil => nil | i :: r => (k, i) :: number r (k + 1) end.

(** [pre], then [body] (an exception there is wrapped in InvocationTargetException when
    [wrap]), then [post]; the locals are [vs] plus one temporary. *)
Definition model_code (vs : list value) (pre body post : list instr) (wrap : bool) : code :=
  let nl := fold_left (fun n v => n + slots v) vs 0 in
  let b0 := Z.of_nat (length pre) in
  let b1 := b0 + Z.of_nat (length body) in
  let hp := b1 + Z.of_nat (length post) in
  let handler := [Store KA nl; New ITE; Dup; Load KA nl;
                  Invoke InvSpecial {| mr_class := ITE; mr_name := "<init>"; mr_desc := "(Ljava/lang/Throwable;)V"; mr_interface := false |};
                  Athrow] in
  {| c_max_stack := 2 * nl + 8; c_max_locals := nl + 1;
     c_length := hp + (if wrap then Z.of_nat (length handler) else 0);
     c_instrs := number (app pre (app body (app post (if wrap then handler else nil)))) 0;
     c_handlers := if wrap then [{| h_start := b0; h_end := b1; h_pc := hp; h_catch := Some "java/lang/Throwable" |}] else nil |}.

(** static String.valueOf(...) *)
Definition string_static (name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := name ++ desc in
  if String.eqb key "join(Ljava/lang/CharSequence;[Ljava/lang/CharSequence;)Ljava/lang/String;" then string_join s args else
  if String.eqb key "valueOf(I)Ljava/lang/String;" then
    match args with [VInt z] => ret_new s (OStr (z_units z)) | _ => MStuckModel "valueOf" end
  else if String.eqb key "valueOf(J)Ljava/lang/String;" then
    match args with [VLong z] => ret_new s (OStr (z_units z)) | _ => MStuckModel "valueOf" end
  else if String.eqb key "valueOf(C)Ljava/lang/String;" then
    match args with [VInt c] => ret_new s (OStr [c]) | _ => MStuckModel "valueOf" end
  else if String.eqb key "valueOf(Z)Ljava/lang/String;" then
    match args with [VInt b] => ret_lit s (bool_units (negb (b =? 0))) | _ => MStuckModel "valueOf" end
  else if String.eqb key "valueOf(Ljava/lang/Object;)Ljava/lang/String;" then
    match args with
    | [VNull] => ret_lit s null_units
    | [v] => match str_of s v with
             | Some _ => MOk (Some v) s
             | None => match v with
                       | VRef l => match option_bind (ms_heap s l) box_string with
                                   | Some u => ret_new s (OStr u)
                                   | None =>
                                       (* obj.toString(), run as bytecode (virtual dispatch) *)
                                       MFrame None (model_code [v] nil
                                         [Load KA 0; Invoke InvVirtual {| mr_class := "java/lang/Object"; mr_name := "toString";
                                                                         mr_desc := "()Ljava/lang/String;"; mr_interface := false |}]
                                         [Return (Some KA)] false) [v] (Some (TRef "java/lang/String")) s
                                   end
                       | _ => MStuckModel "valueOf(Object)"
                       end
             end
    | _ => MStuckModel "valueOf"
    end
  else MNoModel.

(** ** java.lang.StringBuilder *)
Definition sb_of (s : mstate) (v : value) : option (Z * list Z) :=
  match v with
  | VRef l => match ms_heap s l with Some (OSb u) => Some (l, u) | _ => None end
  | _ => None
  end.

Definition append_units (s : mstate) (t : string) (v : value) : option (list Z) :=
  if String.eqb t "(Ljava/lang/String;)Ljava/lang/StringBuilder;"
     || String.eqb t "(Ljava/lang/Object;)Ljava/lang/StringBuilder;"
     || String.eqb t "(Ljava/lang/CharSequence;)Ljava/lang/StringBuilder;" then
    match v with VNull => Some null_units | _ => str_of s v end
  else match v with
       | VInt z => if String.eqb t "(I)Ljava/lang/StringBuilder;" then Some (z_units z)
                   else if String.eqb t "(C)Ljava/lang/StringBuilder;" then Some [z]
                   else if String.eqb t "(Z)Ljava/lang/StringBuilder;" then Some (bool_units (negb (z =? 0)))
                   else None
       | VLong z => if String.eqb t "(J)Ljava/lang/StringBuilder;" then Some (z_units z) else None
       | _ => None
       end.

Definition sb_model (name desc : string) (args : list value) (s : mstate) : model_result :=
  match args with
  | nil => MNoModel
  | this :: rest =>
  if String.eqb name "<init>" then
    match this with
    | VRef l =>
      if String.eqb desc "()V" then MOk None (set_heap s l (OSb nil))
      else if String.eqb desc "(I)V" then
        match rest with
        | [VInt n] => if n <? 0 then MThrow "java/lang/NegativeArraySizeException"
                      else if MAX_ARRAY <? n then MStuckModel "StringBuilder capacity beyond the model bound"
                      else MOk None (set_heap s l (OSb nil))
        | _ => MStuckModel "StringBuilder(int)"
        end
      else if String.eqb desc "(Ljava/lang/String;)V" then
        match rest with
        | [VNull] => MThrow NPE
        | [v] => match str_of s v with Some u => MOk None (set_heap s l (OSb u)) | None => MStuckModel "SB(String)" end
        | _ => MStuckModel "StringBuilder(String)"
        end
      else MNoModel
    | _ => MStuckModel "StringBuilder.<init> receiver"
    end
  else
  match sb_of s this with
  | None => MNoModel
  | Some (l, u) =>
    if String.eqb name "append" then
      match rest with
      | [v] => match append_units s desc v with
               | Some w => MOk (Some this) (set_heap s l (OSb (app u w)))
               | None =>
                   if String.eqb desc "(Ljava/lang/Object;)Ljava/lang/StringBuilder;" then
                     (* append(String.valueOf(obj)): toString() runs as bytecode *)
                     MFrame None (model_code [this; v] nil
                       [Load KA 0; Load KA 1;
                        Invoke InvStatic {| mr_class := "java/lang/String"; mr_name := "valueOf";
                                            mr_desc := "(Ljava/lang/Object;)Ljava/lang/String;"; mr_interface := false |};
                        Invoke InvVirtual {| mr_class := "java/lang/StringBuilder"; mr_name := "append";
                                             mr_desc := "(Ljava/lang/String;)Ljava/lang/StringBuilder;"; mr_interface := false |}]
                       [Return (Some KA)] false) [this; v] (Some (TRef "java/lang/StringBuilder")) s
                   else MStuckModel ("StringBuilder.append" ++ desc ++ ": not modelled for this argument")
               end
      | _ => MStuckModel "append args"
      end
    else if String.eqb name "toString" && String.eqb desc "()Ljava/lang/String;" then ret_new s (OStr u)
    else if String.eqb name "length" && String.eqb desc "()I" then ret_int s (slen u)
    else if String.eqb name "charAt" && String.eqb desc "(I)C" then
      match rest with
      | [VInt i] => match char_at u i with inr c => ret_int s c | inl x => MThrow x end
      | _ => MStuckModel "charAt"
      end
    else if String.eqb name "setLength" && String.eqb desc "(I)V" then
      match rest with
      | [VInt n] => if n <? 0 then MThrow SIOOBE
                    else MOk None (set_heap s l (OSb (if n <=? slen u then firstn (Z.to_nat n) u
                                                      else app u (repeat 0 (Z.to_nat (n - slen u))))))
      | _ => MStuckModel "setLength"
      end
    else if String.eqb name "deleteCharAt" && String.eqb desc "(I)Ljava/lang/StringBuilder;" then
      match rest with
      | [VInt i] => if (i <? 0) || (slen u <=? i) then MThrow SIOOBE
                    else MOk (Some this) (set_heap s l (OSb (app (firstn (Z.to_nat i) u) (skipn (Z.to_nat (i + 1)) u))))
      | _ => MStuckModel "deleteCharAt"
      end
    else if String.eqb name "insert" && String.eqb desc "(ILjava/lang/String;)Ljava/lang/StringBuilder;" then
      match rest with
      | [VInt i; v] =>
          let w := match v with VNull => Some null_units | _ => str_of s v end in
          match w with
          | None => MStuckModel "insert"
          | Some w => if (i <? 0) || (slen u <? i) then MThrow SIOOBE
                      else MOk (Some this) (set_heap s l (OSb (app (firstn (Z.to_nat i) u) (app w (skipn (Z.to_nat i) u)))))
          end
      | _ => MStuckModel "insert"
      end
    else MNoModel
  end
  end.

(** ** java.lang.Character, Integer, Long, Math *)
Definition char_model (e : jenv) (name desc : string) (args : list value) (s : mstate) : model_result :=
  let u := j_u e in
  match args with
  | [VInt c] =>
    let key := name ++ desc in
    if String.eqb key "toUpperCase(C)C" then ret_int s (i2c (u_upper u c))
    else if String.eqb key "toLowerCase(C)C" then ret_int s (i2c (u_lower u c))
    else if String.eqb key "toUpperCase(I)I" then ret_int s (u_upper u c)
    else if String.eqb key "toLowerCase(I)I" then ret_int s (u_lower u c)
    else if String.eqb key "isDigit(C)Z" || String.eqb key "isDigit(I)Z" then ret_bool s (u_is_digit u c)
    else if String.eqb key "isLetter(C)Z" || String.eqb key "isLetter(I)Z" then ret_bool s (u_is_letter u c)
    else if String.eqb key "isLetterOrDigit(C)Z" || String.eqb key "isLetterOrDigit(I)Z" then
      ret_bool s (u_is_letter u c || u_is_digit u c)
    else if String.eqb key "isWhitespace(C)Z" || String.eqb key "isWhitespace(I)Z" then ret_bool s (u_is_whitespace u c)
    else if String.eqb key "isUpperCase(C)Z" || String.eqb key "isUpperCase(I)Z" then ret_bool s (u_is_upper u c)
    else if String.eqb key "isLowerCase(C)Z" || String.eqb key "isLowerCase(I)Z" then ret_bool s (u_is_lower u c)
    else if String.eqb key "isHighSurrogate(C)Z" then ret_bool s (is_high_surrogate c)
    else if String.eqb key "isLowSurrogate(C)Z" then ret_bool s (is_low_surrogate c)
    else MNoModel
  | [VInt c; VInt r] =>
    if String.eqb name "digit" && (String.eqb desc "(CI)I" || String.eqb desc "(II)I") then ret_int s (u_digit u c r)
    else MNoModel
  | _ => MNoModel
  end.

(** Integer/Long bit operations (two's complement on 32/64 bits). *)
Definition unsigned (w : Z) (a : Z) : Z := Z.modulo a (2 ^ w).
Fixpoint popcount (fuel : nat) (a : Z) : Z :=
  match fuel with O => 0 | S f => if (a =? 0)%Z then 0 else Z.modulo a 2 + popcount f (Z.div a 2) end.
Definition nlz (w : Z) (a : Z) : Z := let u := unsigned w a in if (u =? 0)%Z then w else w - 1 - Z.log2 u.
Definition ntz (w : Z) (a : Z) : Z :=
  let u := unsigned w a in if (u =? 0)%Z then w else Z.log2 (Z.land u (- u)).
Definition highest (w : Z) (a : Z) : Z :=
  let u := unsigned w a in if (u =? 0)%Z then 0 else (if (w =? 32)%Z then wrap32 else wrap64) (2 ^ Z.log2 u).
Definition lowest (w : Z) (a : Z) : Z :=
  let u := unsigned w a in (if (w =? 32)%Z then wrap32 else wrap64) (Z.land u (- u)).

Definition ARITH := "java/lang/ArithmeticException".

(** Math's exact and floor operations (JDK 21 semantics). *)
Definition exact32 (s : mstate) (z : Z) : model_result :=
  if ((z <? INT_MIN) || (INT_MAX <? z))%Z then MThrow ARITH else ret_int s z.
Definition exact64 (s : mstate) (z : Z) : model_result :=
  if ((z <? LONG_MIN) || (LONG_MAX <? z))%Z then MThrow ARITH else MOk (Some (VLong z)) s.

Definition num_model1 (e : jenv) (key : string) (args : list value) (s : mstate) : model_result :=
  match args with

  | [VInt a] =>
    if String.eqb key "java/lang/Integer.toString(I)Ljava/lang/String;" then ret_new s (OStr (z_units a))
    else if String.eqb key "java/lang/Math.abs(I)I" then ret_int s (wrap32 (Z.abs a))
    else if String.eqb key "java/lang/Integer.signum(I)I" then ret_int s (Z.sgn a)
    else MNoModel
  | [VLong a] =>
    if String.eqb key "java/lang/Long.toString(J)Ljava/lang/String;" then ret_new s (OStr (z_units a))
    else if String.eqb key "java/lang/Math.abs(J)J" then MOk (Some (VLong (wrap64 (Z.abs a)))) s
    else MNoModel
  | [VInt a; VInt b] =>
    if String.eqb key "java/lang/Math.max(II)I" then ret_int s (Z.max a b)
    else if String.eqb key "java/lang/Math.min(II)I" then ret_int s (Z.min a b)
    else if String.eqb key "java/lang/Integer.compare(II)I" then ret_int s (lcmp a b)
    else if String.eqb key "java/lang/Integer.max(II)I" then ret_int s (Z.max a b)
    else if String.eqb key "java/lang/Integer.min(II)I" then ret_int s (Z.min a b)
    else MNoModel
  | [VLong a; VLong b] =>
    if String.eqb key "java/lang/Math.max(JJ)J" then MOk (Some (VLong (Z.max a b))) s
    else if String.eqb key "java/lang/Math.min(JJ)J" then MOk (Some (VLong (Z.min a b))) s
    else if String.eqb key "java/lang/Long.compare(JJ)I" then ret_int s (lcmp a b)
    else MNoModel
  | [v] =>
    if String.eqb key "java/lang/Integer.parseInt(Ljava/lang/String;)I" then
      match v with
      | VNull => MThrow NFE
      | _ => match str_of s v with
             | Some u => match parse_dec (j_u e) INT_MIN INT_MAX u with inr z => ret_int s z | inl x => MThrow x end
             | None => MStuckModel "parseInt"
             end
      end
    else if String.eqb key "java/lang/Long.parseLong(Ljava/lang/String;)J" then
      match v with
      | VNull => MThrow NFE
      | _ => match str_of s v with
             | Some u => match parse_dec (j_u e) LONG_MIN LONG_MAX u with
                         | inr z => MOk (Some (VLong z)) s | inl x => MThrow x end
             | None => MStuckModel "parseLong"
             end
      end
    else MNoModel
  | _ => MNoModel
  end.


Definition num_model2 (key : string) (args : list value) (s : mstate) : model_result :=
  match args with
  | [VInt a] =>
    if String.eqb key "java/lang/Integer.bitCount(I)I" then ret_int s (popcount 40 (unsigned 32 a))
    else if String.eqb key "java/lang/Integer.numberOfLeadingZeros(I)I" then ret_int s (nlz 32 a)
    else if String.eqb key "java/lang/Integer.numberOfTrailingZeros(I)I" then ret_int s (ntz 32 a)
    else if String.eqb key "java/lang/Integer.highestOneBit(I)I" then ret_int s (highest 32 a)
    else if String.eqb key "java/lang/Integer.lowestOneBit(I)I" then ret_int s (lowest 32 a)
    else if String.eqb key "java/lang/Integer.hashCode(I)I" then ret_int s a
    else if String.eqb key "java/lang/Math.negateExact(I)I" then exact32 s (- a)
    else if String.eqb key "java/lang/Math.incrementExact(I)I" then exact32 s (a + 1)
    else if String.eqb key "java/lang/Math.decrementExact(I)I" then exact32 s (a - 1)
    else if String.eqb key "java/lang/Math.absExact(I)I" then exact32 s (Z.abs a)
    else MNoModel
  | [VLong a] =>
    if String.eqb key "java/lang/Long.bitCount(J)I" then ret_int s (popcount 80 (unsigned 64 a))
    else if String.eqb key "java/lang/Long.numberOfLeadingZeros(J)I" then ret_int s (nlz 64 a)
    else if String.eqb key "java/lang/Long.numberOfTrailingZeros(J)I" then ret_int s (ntz 64 a)
    else if String.eqb key "java/lang/Long.highestOneBit(J)J" then MOk (Some (VLong (highest 64 a))) s
    else if String.eqb key "java/lang/Long.lowestOneBit(J)J" then MOk (Some (VLong (lowest 64 a))) s
    else if String.eqb key "java/lang/Long.hashCode(J)I" then ret_int s (wrap32 (Z.lxor (unsigned 64 a) (Z.shiftr (unsigned 64 a) 32)))
    else if String.eqb key "java/lang/Long.signum(J)I" then ret_int s (Z.sgn a)
    else if String.eqb key "java/lang/Math.toIntExact(J)I" then exact32 s a
    else if String.eqb key "java/lang/Math.negateExact(J)J" then exact64 s (- a)
    else if String.eqb key "java/lang/Math.incrementExact(J)J" then exact64 s (a + 1)
    else if String.eqb key "java/lang/Math.decrementExact(J)J" then exact64 s (a - 1)
    else if String.eqb key "java/lang/Math.absExact(J)J" then exact64 s (Z.abs a)
    else MNoModel
  | [VInt a; VInt b] =>
    if String.eqb key "java/lang/Math.floorMod(II)I" then if (b =? 0)%Z then MThrow ARITH else ret_int s (Z.modulo a b)
    else if String.eqb key "java/lang/Math.floorDiv(II)I" then if (b =? 0)%Z then MThrow ARITH else ret_int s (wrap32 (Z.div a b))
    else if String.eqb key "java/lang/Math.addExact(II)I" then exact32 s (a + b)
    else if String.eqb key "java/lang/Math.subtractExact(II)I" then exact32 s (a - b)
    else if String.eqb key "java/lang/Math.multiplyExact(II)I" then exact32 s (a * b)
    else if String.eqb key "java/lang/Integer.sum(II)I" then ret_int s (wrap32 (a + b))
    else if String.eqb key "java/lang/Integer.rotateLeft(II)I" then
      let u := unsigned 32 a in let k := Z.modulo b 32 in ret_int s (wrap32 (Z.lor (Z.shiftl u k) (Z.shiftr u (32 - k))))
    else if String.eqb key "java/lang/Integer.rotateRight(II)I" then
      let u := unsigned 32 a in let k := Z.modulo b 32 in ret_int s (wrap32 (Z.lor (Z.shiftr u k) (Z.shiftl u (32 - k))))
    else MNoModel
  | [VLong a; VLong b] =>
    if String.eqb key "java/lang/Math.floorMod(JJ)J" then if (b =? 0)%Z then MThrow ARITH else MOk (Some (VLong (Z.modulo a b))) s
    else if String.eqb key "java/lang/Math.floorDiv(JJ)J" then if (b =? 0)%Z then MThrow ARITH else MOk (Some (VLong (wrap64 (Z.div a b)))) s
    else if String.eqb key "java/lang/Math.addExact(JJ)J" then exact64 s (a + b)
    else if String.eqb key "java/lang/Math.subtractExact(JJ)J" then exact64 s (a - b)
    else if String.eqb key "java/lang/Math.multiplyExact(JJ)J" then exact64 s (a * b)
    else if String.eqb key "java/lang/Long.sum(JJ)J" then MOk (Some (VLong (wrap64 (a + b)))) s
    else MNoModel
  | [VLong a; VInt b] =>
    if String.eqb key "java/lang/Math.floorMod(JI)I" then if (b =? 0)%Z then MThrow ARITH else ret_int s (Z.modulo a b)
    else if String.eqb key "java/lang/Math.floorDiv(JI)J" then if (b =? 0)%Z then MThrow ARITH else MOk (Some (VLong (wrap64 (Z.div a b)))) s
    else if String.eqb key "java/lang/Math.multiplyExact(JI)J" then exact64 s (a * b)
    else MNoModel
  | _ => MNoModel
  end.

Definition num_model (e : jenv) (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := cls ++ "." ++ name ++ desc in
  match num_model2 key args s with MNoModel => num_model1 e key args s | r => r end.


(** ** java.util.Objects *)
Definition objects_model (name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := name ++ desc in
  if String.eqb key "requireNonNull(Ljava/lang/Object;)Ljava/lang/Object;"
     || String.eqb key "requireNonNull(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/Object;" then
    match args with VNull :: _ => MThrow NPE | v :: _ => MOk (Some v) s | nil => MStuckModel "requireNonNull" end
  else if String.eqb key "equals(Ljava/lang/Object;Ljava/lang/Object;)Z" then
    match args with
    | [a; b] =>
      if ref_eq a b then ret_bool s true
      else match a with
           | VNull => ret_bool s false
           | _ => match str_of s a with
                  | Some ua => ret_bool s (match str_of s b with Some ub => units_eqb ua ub | None => false end)
                  | None =>
                      match a with
                      | VRef la => match ms_heap s la with
                                   | Some (OObj c [("value", wa)]) =>
                                       if is_box_class c then
                                         ret_bool s (match box_value s c b with Some wb => value_eqb wa wb | None => false end)
                                       else MStuckModel "Objects.equals: equals() callback"
                                   | _ => MStuckModel "Objects.equals: equals() callback"
                                   end
                      | _ => MStuckModel "Objects.equals: equals() callback"
                      end
                  end
           end
    | _ => MStuckModel "Objects.equals"
    end
  else if String.eqb key "hashCode(Ljava/lang/Object;)I" then
    match args with
    | [VNull] => ret_int s 0
    | [v] => match str_of s v with Some u => ret_int s (str_hash u) | None => MStuckModel "Objects.hashCode callback" end
    | _ => MStuckModel "Objects.hashCode"
    end
  else MNoModel.

(** ** Arrays: System.arraycopy, Arrays.fill / copyOf, clone *)
Definition arr_of (s : mstate) (v : value) : option (Z * jtype * list value) :=
  match v with
  | VRef l => match ms_heap s l with Some (OArr t es) => Some (l, t, es) | _ => None end
  | _ => None
  end.

Definition prim_type (t : jtype) : bool := match t with TRef _ | TArr _ => false | _ => true end.

(** System.arraycopy (JVMS/Javadoc): NPE for null arrays; ArrayStoreException
    when the arrays are not both of the same primitive type or both of
    reference type; IndexOutOfBounds (as ArrayIndexOutOfBoundsException) for
    bad ranges; copying as if through a temporary (overlap-safe).  For
    reference arrays whose element types differ, elements are checked one by
    one and the copy stops with ArrayStoreException at the first bad one. *)
Definition arraycopy (p : program) (args : list value) (s : mstate) : model_result :=
  match args with
  | [src; VInt sp; dst; VInt dp; VInt n] =>
    match src, dst with
    | VNull, _ | _, VNull => MThrow NPE
    | _, _ =>
      match arr_of s src, arr_of s dst with
      | Some (_, ts, es), Some (ld, td, ed) =>
        if negb (Bool.eqb (prim_type ts) (prim_type td)) then MThrow "java/lang/ArrayStoreException"
        else if prim_type ts && negb (String.eqb (type_desc ts) (type_desc td)) then MThrow "java/lang/ArrayStoreException"
        else if (sp <? 0) || (dp <? 0) || (n <? 0) || (slen_v es <? sp + n) || (slen_v ed <? dp + n)
        then MThrow "java/lang/ArrayIndexOutOfBoundsException"
        else
          let chunk := firstn (Z.to_nat n) (skipn (Z.to_nat sp) es) in
          (* reference arrays: element-wise store check *)
          let ok_prefix :=
            if prim_type ts then Some (length chunk, true) else
            fold_left (fun acc v => match acc with
                                    | Some (k, true) =>
                                        match v with
                                        | VRef r => match ms_heap s r with
                                                    | Some o => match assignable p 64 (runtime_type o)
                                                                       (match td with TArr _ => type_desc td | TRef c => c | _ => "" end) with
                                                                | Some true => Some (S k, true)
                                                                | Some false => Some (k, false)
                                                                | None => None
                                                                end
                                                    | None => None
                                                    end
                                        | _ => Some (S k, true)
                                        end
                                    | other => other
                                    end) chunk (Some (O, true)) in
          match ok_prefix with
          | None => MStuckModel "arraycopy: cannot decide element type"
          | Some (k, all_ok) =>
              let copied := firstn k chunk in
              let ed' := app (firstn (Z.to_nat dp) ed) (app copied (skipn (Z.to_nat dp + k) ed)) in
              let s' := set_heap s ld (OArr td ed') in
              if all_ok then MOk None s' else MThrow "java/lang/ArrayStoreException"
          end
      | _, _ => MThrow "java/lang/ArrayStoreException"
      end
    end
  | _ => MStuckModel "arraycopy args"
  end.

Definition range_check (len from to : Z) : option string :=
  if to <? from then Some IAE
  else if from <? 0 then Some "java/lang/ArrayIndexOutOfBoundsException"
  else if len <? to then Some "java/lang/ArrayIndexOutOfBoundsException"
  else None.

Definition arrays_model (p : program) (name desc : string) (args : list value) (s : mstate) : model_result :=
  if String.eqb name "fill" then
    let fill_range (a : value) (rng : option (Z * Z)) (v : value) :=
      match a with
      | VNull => MThrow NPE
      | _ => match arr_of s a with
             | None => MStuckModel "fill: not an array"
             | Some (l, t, es) =>
                 let (f, tt) := match rng with Some ft => ft | None => (0, slen_v es) end in
                 match range_check (slen_v es) f tt with
                 | Some x => MThrow x
                 | None =>
                   let v' := narrow_store t v in
                   if negb (value_fits t v') then MStuckModel "fill: value type" else
                   match v', t with
                   | VRef r, _ => MStuckModel "fill with a non-null reference: store check not modelled yet"
                   | _, _ =>
                     MOk None (set_heap s l (OArr t (app (firstn (Z.to_nat f) es)
                                                   (app (repeat v' (Z.to_nat (tt - f))) (skipn (Z.to_nat tt) es)))))
                   end
                 end
             end
      end in
    match args with
    | [a; v] => fill_range a None v
    | [a; VInt f; VInt t; v] => fill_range a (Some (f, t)) v
    | _ => MNoModel
    end
  else if String.eqb name "copyOf" then
    match args with
    | [a; VInt n] =>
      match a with
      | VNull => MThrow NPE
      | _ => match arr_of s a with
             | None => MStuckModel "copyOf"
             | Some (_, t, es) =>
                 if n <? 0 then MThrow "java/lang/NegativeArraySizeException"
                 else if MAX_ARRAY <? n then MStuckModel "copyOf beyond model bound"
                 else if String.eqb desc "([Ljava/lang/Object;I)[Ljava/lang/Object;"
                         || (prim_type t && String.eqb desc ("(" ++ type_desc (TArr t) ++ "I)" ++ type_desc (TArr t))) then
                   ret_new s (OArr t (if n <=? slen_v es then firstn (Z.to_nat n) es
                                      else app es (repeat (default_of t) (Z.to_nat (n - slen_v es)))))
                 else MStuckModel "copyOf variant"
             end
      end
    | _ => MNoModel
    end
  else MNoModel.

(** ** slf4j: loggers are opaque objects; enabled checks come from [jenv];
    every void Logger method has no effect on the modelled state. *)
Definition ends_with_void (d : string) : bool :=
  let n := String.length d in (2 <=? Z.of_nat n)%Z && String.eqb (substring (n - 2) 2 d) ")V".

Definition slf4j_model (e : jenv) (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  if String.eqb cls "org/slf4j/LoggerFactory" && String.eqb name "getLogger" then
    ret_new s (OObj "org/slf4j/Logger" nil)
  else if String.eqb cls "org/slf4j/Logger" then
    if String.eqb desc "()Z" then ret_bool s (j_log_enabled e name)
    else if ends_with_void desc then MOk None s
    else MNoModel
  else MNoModel.

(** ** java.lang.Enum *)
Definition enum_model (name desc : string) (args : list value) (s : mstate) : model_result :=
  match args with
  | VRef l :: rest =>
    match ms_heap s l with
    | Some (OObj c fs) =>
      if String.eqb name "<init>" && String.eqb desc "(Ljava/lang/String;I)V" then
        match rest with
        | [n; VInt o] =>
            match set_assoc (own_key "java/lang/Enum" "name" fs) n fs with
            | Some fs1 => match set_assoc (own_key "java/lang/Enum" "ordinal" fs) (VInt o) fs1 with
                          | Some fs2 => MOk None (set_heap s l (OObj c fs2))
                          | None => MStuckModel "enum fields"
                          end
            | None => MStuckModel "enum fields"
            end
        | _ => MStuckModel "Enum.<init>"
        end
      else if String.eqb name "ordinal" && String.eqb desc "()I" then
        match assoc (own_key "java/lang/Enum" "ordinal" fs) fs with Some v => MOk (Some v) s | None => MStuckModel "ordinal" end
      else if (String.eqb name "name" || String.eqb name "toString") && String.eqb desc "()Ljava/lang/String;" then
        match assoc (own_key "java/lang/Enum" "name" fs) fs with Some v => MOk (Some v) s | None => MStuckModel "name" end
      else if String.eqb name "equals" && String.eqb desc "(Ljava/lang/Object;)Z" then
        match rest with [v] => ret_bool s (ref_eq (VRef l) v) | _ => MStuckModel "equals" end
      else MNoModel
    | _ => MNoModel
    end
  | _ => MNoModel
  end.

(** ** java.lang.Class (reflection on class objects; JDK 21 behaviour)
    A class object is [OCls n] with [n] the internal name ("java/lang/String") or, for an
    array class, its descriptor ("[I", "[Ljava/lang/String;"). Class objects are interned:
    one object per class. Primitive classes ([int.class] is [Integer.TYPE]) are not modelled. *)
Definition cls_obj (s : mstate) (n : string) : Z * mstate := intern s (OCls n).

Definition class_of_type (t : jtype) : string := match t with TRef c => c | _ => type_desc t end.

Definition is_array_name (n : string) : bool := prefix "[" n.

Fixpoint after_last_go (c : Z) (u : list Z) (cur : list Z) : list Z :=
  match u with
  | nil => rev cur
  | x :: r => if (x =? c)%Z then after_last_go c r nil else after_last_go c r (x :: cur)
  end.
Definition after_last (c : Z) (u : list Z) : list Z := after_last_go c u nil.

(** A class name given as UTF-16 units, if it is ASCII. *)
Fixpoint units_string (u : list Z) : option string :=
  match u with
  | nil => Some EmptyString
  | c :: r => if ((0 <=? c) && (c <? 128))%Z
              then match units_string r with Some t => Some (String (Ascii.ascii_of_nat (Z.to_nat c)) t) | None => None end
              else None
  end.

Definition prim_name (n : string) : option (list Z) :=
  let r := fun w => Some (ascii_units w) in
  if String.eqb n "I" then r "int" else if String.eqb n "J" then r "long" else if String.eqb n "Z" then r "boolean"
  else if String.eqb n "B" then r "byte" else if String.eqb n "C" then r "char" else if String.eqb n "S" then r "short"
  else if String.eqb n "F" then r "float" else if String.eqb n "D" then r "double"
  else if String.eqb n "V" then r "void" else None.

(** getSimpleName: from the InnerClasses attribute for loaded classes (Machine.simple_name);
    for JDK classes the part after the last '/' and '$' (member classes); arrays add "[]". *)
Fixpoint simple_name_of (p : program) (fuel : nat) (n : string) : option (list Z) :=
  match fuel with
  | O => None
  | S f =>
    if is_array_name n then
      match class_type n with
      | TArr t => match simple_name_of p f (class_of_type t) with
                  | Some u => Some (app u [91; 93])%Z
                  | None => None
                  end
      | _ => None
      end
    else match prim_name n with Some u => Some u | None =>
         match find_class p n with
         | Some cf => simple_name cf
         | None => match jdk_info n with
                   | _ =>
                       (* a JDK class: top-level or member class; an anonymous or local one
                          (its last '$' part starts with a digit) is not modelled *)
                       let u := after_last 36 (after_last 46 (class_name_units n)) in
                       match u with
                       | c :: _ => if ((48 <=? c) && (c <=? 57))%Z then None else Some u
                       | nil => None
                       end
                   end
         end end
  end.

Definition builtin_iface (n : string) : bool := existsb (String.eqb n) builtin_interfaces.

Definition class_iface (p : program) (n : string) : option bool :=
  if is_array_name n then Some false
  else match class_info p n with
       | CIUnknown => if builtin_iface n then Some true
                      else match builtin_super n with Some _ => Some false | None => None end
       | ci => Some (ci_iface ci)
       end.

Definition class_super (p : program) (n : string) : option (option string) :=
  if is_array_name n then Some (Some "java/lang/Object")
  else match class_info p n with
       | CIUnknown => if builtin_iface n then Some None else builtin_super n
       | ci => if ci_iface ci then Some None else Some (ci_super ci)
       end.

Definition class_access (p : program) (n : string) : option Z :=
  match class_info p n with
  | CILoaded cf => Some (cf_access cf)
  | CIJdk j => Some (ji_access j)
  | CIUnknown => None
  end.

(** ** Reflection: java.lang.reflect.Method / Constructor / Field (JDK 21 behaviour).
    A member object is [OObj "java/lang/reflect/<Kind>" fields] with its declaring class
    ("clazz"), name and descriptor (Strings), access flags ("mods") and the setAccessible
    flag ("override"). Invocation, construction and field access run synthetic bytecode in a
    frame of its own ([MFrame]): the arguments are checked and unboxed here, the frame does
    the call (with virtual dispatch), boxes the result, and wraps an exception of the callee
    in InvocationTargetException; the class is initialised first (an initialisation error is
    not wrapped). Members of classes that are not loaded (the JDK's) are not modelled. *)

Definition REFM := "java/lang/reflect/Method".
Definition set_field_v (k : string) (v : value) (fs : list (string * value)) : list (string * value) :=
  match set_assoc k v fs with Some fs' => fs' | None => (k, v) :: fs end.

Definition REFC := "java/lang/reflect/Constructor".
Definition REFF := "java/lang/reflect/Field".
Definition IAEX := "java/lang/IllegalArgumentException".

Definition name_units (x : string) : list Z := match utf8_units x with Some u => u | None => ascii_units x end.

Definition cls_desc (n : string) : string :=
  match prim_name n with Some _ => n | None => if is_array_name n then n else "L" ++ n ++ ";" end.

Definition concat_str (l : list string) : string := fold_right String.append EmptyString l.

Definition str_field (s : mstate) (fs : list (string * value)) (k : string) : option string :=
  match assoc k fs with
  | Some v => match str_of s v with Some u => units_string u | None => None end
  | None => None
  end.
Definition int_field (fs : list (string * value)) (k : string) : option Z :=
  match assoc k fs with Some (VInt z) => Some z | _ => None end.
Definition cls_field (s : mstate) (fs : list (string * value)) (k : string) : option string :=
  match assoc k fs with
  | Some (VRef c) => match ms_heap s c with Some (OCls n) => Some n | _ => None end
  | _ => None
  end.

(** The names of the classes in a Class[] argument ([null]: none). *)
Definition class_names (s : mstate) (v : value) : option (list string) :=
  match v with
  | VNull => Some nil
  | VRef a => match ms_heap s a with
              | Some (OArr _ es) =>
                  fold_right (fun e acc => match acc, e with
                                           | Some l, VRef c => match ms_heap s c with Some (OCls n) => Some (n :: l) | _ => None end
                                           | _, _ => None
                                           end) (Some nil) es
              | _ => None
              end
  | _ => None
  end.

Definition array_elems (s : mstate) (v : value) : option (list value) :=
  match v with
  | VNull => Some nil
  | VRef a => match ms_heap s a with Some (OArr _ es) => Some es | _ => None end
  | _ => None
  end.

Definition params_desc (ns : list string) : string := "(" ++ concat_str (map cls_desc ns) ++ ")".

(** Class.getName, also of primitive classes. *)
Definition cls_name_units (n : string) : list Z := match prim_name n with Some u => u | None => class_name_units n end.

(** "C.name(p1,p2)" as in Class.methodToString (the NoSuchMethodException message). *)
Definition method_string (c : string) (name : string) (ns : list string) : list Z :=
  app (class_name_units c) (app [46] (app (name_units name)
    (app [40] (app (fold_right (fun x acc => match acc with nil => cls_name_units x | _ => app (cls_name_units x) (44 :: acc) end) nil ns) [41])))).

Definition decl_methods (cf : classfile) (name pd : string) (pub : bool) : list method :=
  filter (fun m => String.eqb (m_name m) name && prefix pd (m_desc m) && (negb pub || acc_public (m_access m))) (cf_methods cf).

(** One method among those with the same parameters: the one that is not a bridge. *)
Definition pick (ms : list method) : option (option method) :=
  match ms with
  | nil => Some None
  | [m] => Some (Some m)
  | _ => match filter (fun m => negb (Z.testbit (m_access m) 6)) ms with [m] => Some (Some m) | _ => None end
  end.

Definition object_public (name pd : string) : bool :=
  existsb (fun e => String.eqb (fst e) name && String.eqb (snd e) pd)
    [("getClass", "()"); ("hashCode", "()"); ("equals", "(Ljava/lang/Object;)"); ("toString", "()");
     ("notify", "()"); ("notifyAll", "()"); ("wait", "()"); ("wait", "(J)"); ("wait", "(JI)")].

Inductive mlook : Type := MLFound (d : string) (m : method) | MLNone | MLUnknown.

(** Class.getMethod along the superclass chain: the public methods declared by the class,
    else those of its superclass. *)
Fixpoint chain_method (p : program) (fuel : nat) (c name pd : string) : mlook :=
  match fuel with
  | O => MLUnknown
  | S f =>
    match find_class p c with
    | Some cf => match pick (decl_methods cf name pd true) with
                 | None => MLUnknown
                 | Some (Some m) => MLFound c m
                 | Some None => match cf_super cf with
                                | Some sup => if acc_interface (cf_access cf) then MLNone else chain_method p f sup name pd
                                | None => MLNone
                                end
                 end
    | None => if String.eqb c "java/lang/Object" then (if object_public name pd then MLUnknown else MLNone) else MLUnknown
    end
  end.

(** No superinterface declares the method (all loaded): then getMethod finds nothing more. *)
Definition ifaces_lack (p : program) (c name pd : string) : bool :=
  match superifaces p c with
  | Some ifs => forallb (fun i => match find_class p i with
                                 | Some cf => match decl_methods cf name pd true with nil => true | _ => false end
                                 | None => false
                                 end) ifs
  | None => false
  end.

Fixpoint decl_field_in (name : string) (l : list member) : option member :=
  match l with nil => None | m :: r => if String.eqb (mb_name m) name then Some m else decl_field_in name r end.

Inductive flook : Type := FLFound (d : string) (m : member) | FLNone | FLUnknown.

(** Class.getField: a public field of the class, of a superinterface (depth first), or of the
    superclass (JDK 21 Class.getField0). *)
Fixpoint pub_field (p : program) (fuel : nat) (c name : string) : flook :=
  match fuel with
  | O => FLUnknown
  | S f =>
    match find_class p c with
    | Some cf =>
        let rest_search :=
          match fold_left (fun acc i => match acc with FLNone => pub_field p f i name | r => r end) (cf_interfaces cf) FLNone with
          | FLNone => match cf_super cf with Some sup => pub_field p f sup name | None => FLNone end
          | r => r
          end in
        match decl_field_in name (cf_fields cf) with
        | Some m => if acc_public (mb_access m) then FLFound c m else rest_search
        | None => rest_search
        end
    | None => if String.eqb c "java/lang/Object" then FLNone else FLUnknown
    end
  end.

Definition nest_host (p : program) (c : string) : string :=
  match find_class p c with
  | Some cf => match find_attr "NestHost" (cf_attrs cf) with
               | Some bs => match u2 bs with
                            | Some (i, _) => match cp_class (cf_cp cf) i with Some h => h | None => c end
                            | None => c
                            end
               | None => c
               end
  | None => c
  end.

Definition caller_class (s : mstate) : option string :=
  match ms_frames s with top :: _ => Some (cf_class top) | nil => None end.

(** Reflection.verifyMemberAccess for a member of [d] with flags [mods], from [cur]
    ([None]: a case not modelled, e.g. a class of another package or a protected member). *)
Definition access_ok (p : program) (cur d : string) (mods : Z) : option bool :=
  if String.eqb cur d then Some true else
  match class_access p d with
  | None => None
  | Some ca =>
    let same := String.eqb (package_of cur) (package_of d) in
    if negb (acc_public ca) && negb same then None
    else if acc_public mods then Some true
    else if acc_private mods then Some (String.eqb (nest_host p cur) (nest_host p d))
    else if acc_protected mods then (if same then Some true else None)
    else Some same
  end.

(** java.lang.reflect.Modifier.toString *)
Definition modifier_units (m : Z) : list Z :=
  let words := filter (fun e => Z.testbit m (fst e))
    [(0, "public"); (2, "protected"); (1, "private"); (10, "abstract"); (3, "static"); (4, "final");
     (7, "transient"); (6, "volatile"); (5, "synchronized"); (8, "native"); (11, "strictfp"); (9, "interface")] in
  fold_right (fun e acc => match acc with nil => ascii_units (snd e) | _ => app (ascii_units (snd e)) (32 :: acc) end) nil words.

Definition class_string (p : program) (n : string) : list Z :=
  app (ascii_units (match class_iface p n with Some true => "interface " | _ => "class " end)) (class_name_units n).

Definition throw_with (s : mstate) (cls : string) (u : list Z) : model_result :=
  let (m, s1) := alloc s (OStr u) in
  let (l, s2) := alloc s1 (OObj cls [("detailMessage", VRef m)]) in MThrowObj l s2.

Definition illegal_access (p : program) (s : mstate) (cur d : string) (mods : Z) : model_result :=
  throw_with s "java/lang/IllegalAccessException"
    (app (class_string p cur) (app (ascii_units " cannot access a member of ")
      (app (class_string p d) (app (ascii_units " with modifiers ") (34 :: app (modifier_units mods) [34]))))).

(** Access check of a member: [Some r] = throw [r], [None] = allowed, or STUCK. *)
Definition check_access (p : program) (s : mstate) (fs : list (string * value)) (d : string) (mods : Z)
  : option (option model_result) :=
  match int_field fs "override" with
  | Some o => if negb (o =? 0) then Some None
              else match caller_class s with
                   | Some cur => match access_ok p cur d mods with
                                 | Some true => Some None
                                 | Some false => Some (Some (illegal_access p s cur d mods))
                                 | None => None
                                 end
                   | None => None
                   end
  | None => None
  end.

(** An argument for a parameter of type [t]: [Some (Some w)] the value, [Some None] argument
    type mismatch, [None] not modelled (float/double unboxing and widening). *)
Definition conv_arg (p : program) (s : mstate) (t : jtype) (v : value) : option (option value) :=
  match t with
  | TRef _ | TArr _ =>
      match v with
      | VNull => Some (Some VNull)
      | VRef l => match ms_heap s l with
                  | Some o => match obj_assignable p o (class_of_type t) with
                              | Some true => Some (Some v) | Some false => Some None | None => None
                              end
                  | None => None
                  end
      | _ => None
      end
  | TFloat | TDouble => None
  | _ =>
      match v with
      | VNull => Some None
      | VRef l => match ms_heap s l with
                  | Some (OObj c [("value", w)]) =>
                      if is_box_class c then
                        let bd := prim_desc c in let td := type_desc t in
                        match w with
                        | VInt z =>
                            if String.eqb bd td then Some (Some w)
                            else if String.eqb td "J" && negb (String.eqb bd "Z") then Some (Some (VLong z))
                            else if String.eqb td "I" && (String.eqb bd "S" || String.eqb bd "B" || String.eqb bd "C") then Some (Some w)
                            else if String.eqb td "S" && String.eqb bd "B" then Some (Some w)
                            else Some None
                        | VLong _ => if String.eqb bd td then Some (Some w) else Some None
                        | _ => None
                        end
                      else if String.eqb c "java/lang/Float" || String.eqb c "java/lang/Double" then None
                      else Some None
                  | Some (OObj c _) => if String.eqb c "java/lang/Float" || String.eqb c "java/lang/Double" then None else Some None
                  | Some _ => Some None
                  | None => None
                  end
      | _ => None
      end
  end.

Fixpoint conv_args (p : program) (s : mstate) (ts : list jtype) (vs : list value) : option (option (list value)) :=
  match ts, vs with
  | nil, nil => Some (Some nil)
  | t :: tr, v :: vr => match conv_arg p s t v with
                        | Some (Some w) => match conv_args p s tr vr with
                                           | Some (Some ws) => Some (Some (w :: ws))
                                           | r => r
                                           end
                        | Some None => Some None
                        | None => None
                        end
  | _, _ => None
  end.

Definition kind_of_val (v : value) : tkind :=
  match v with VLong _ => KL | VFloat _ => KF | VDouble _ => KD | VInt _ => KI | _ => KA end.

(** Load the locals [vs] (from slot [k]) onto the stack. *)
Fixpoint loads (vs : list value) (k : Z) : list instr :=
  match vs with
  | nil => nil
  | v :: r => Load (kind_of_val v) k :: loads r (k + slots v)
  end.

Definition box_ret (rt : option jtype) : option (list instr) :=
  let vo := fun c d => Some [Invoke InvStatic {| mr_class := c; mr_name := "valueOf"; mr_desc := d; mr_interface := false |}] in
  match rt with
  | None => Some [AconstNull]
  | Some TInt => vo "java/lang/Integer" "(I)Ljava/lang/Integer;"
  | Some TLong => vo "java/lang/Long" "(J)Ljava/lang/Long;"
  | Some TBool => vo "java/lang/Boolean" "(Z)Ljava/lang/Boolean;"
  | Some TChar => vo "java/lang/Character" "(C)Ljava/lang/Character;"
  | Some TShort => vo "java/lang/Short" "(S)Ljava/lang/Short;"
  | Some TByte => vo "java/lang/Byte" "(B)Ljava/lang/Byte;"
  | Some (TRef _) | Some (TArr _) => Some nil
  | Some _ => None
  end.

Definition mk_member (s : mstate) (kind d : string) (name desc : string) (mods : Z) : model_result :=
  let (c, s1) := cls_obj s d in
  let (nm, s2) := intern s1 (OStr (name_units name)) in
  let (ds, s3) := alloc s2 (OStr (ascii_units desc)) in
  ret_new s3 (OObj kind [("clazz", VRef c); ("name", VRef nm); ("desc", VRef ds); ("mods", VInt mods); ("override", VInt 0)]).

Definition new_class_array (s : mstate) (ns : list string) : model_result :=
  let (vs, s') := fold_left (fun acc n => let (l, s1) := cls_obj (snd acc) n in (app (fst acc) [VRef l], s1)) ns (nil, s) in
  ret_new s' (OArr (TRef "java/lang/Class") vs).

Definition class_of_jtype (t : jtype) : string := class_of_type t.
Definition ret_class (rt : option jtype) : string := match rt with None => "V" | Some t => class_of_jtype t end.

Definition wrong_args (s : mstate) (n m : nat) : model_result :=
  throw_with s IAEX (app (ascii_units "wrong number of arguments: ")
                       (app (z_units (Z.of_nat n)) (app (ascii_units " expected: ") (z_units (Z.of_nat m))))).

(** Method / Constructor / Field / AccessibleObject methods. *)
Definition reflect_model (p : program) (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  match args with
  | VRef l :: rest =>
    match ms_heap s l with
    | Some (OObj k fs) =>
      let get_str := str_field s fs in
      match cls_field s fs "clazz", get_str "name", get_str "desc", int_field fs "mods" with
      | Some d, Some nm, Some ds, Some mods =>
        let mask := if String.eqb k REFF then 20703 else 7679 in
        if String.eqb name "setAccessible" && String.eqb desc "(Z)V" then
          match rest with [VInt b] => MOk None (set_heap s l (OObj k (set_field_v "override" (VInt b) fs))) | _ => MStuckModel "setAccessible" end
        else if String.eqb name "trySetAccessible" && String.eqb desc "()Z" then
          MOk (Some (VInt 1)) (set_heap s l (OObj k (set_field_v "override" (VInt 1) fs)))
        else if String.eqb name "isAccessible" && String.eqb desc "()Z" then
          MOk (Some (match int_field fs "override" with Some 0 => VInt 0 | _ => VInt 1 end)) s
        else if String.eqb name "getDeclaringClass" && String.eqb desc "()Ljava/lang/Class;" then
          MOk (assoc "clazz" fs) s
        else if String.eqb name "getModifiers" && String.eqb desc "()I" then ret_int s (Z.land mods mask)
        else if String.eqb name "getName" && String.eqb desc "()Ljava/lang/String;" then
          if String.eqb k REFC then ret_lit s (class_name_units d) else MOk (assoc "name" fs) s
        else if String.eqb k REFF then
          match parse_ftype 256 ds with
          | Some (ft, EmptyString) =>
            let fr := {| fr_class := d; fr_name := nm; fr_desc := ds |} in
            let static := Z.testbit mods 3 in
            if String.eqb name "getType" && String.eqb desc "()Ljava/lang/Class;" then
              let (r, s') := cls_obj s (class_of_jtype ft) in MOk (Some (VRef r)) s'
            else if String.eqb name "get" && String.eqb desc "(Ljava/lang/Object;)Ljava/lang/Object;" then
              match check_access p s fs d mods, rest with
              | None, _ => MStuckModel "Field.get: access"
              | Some (Some r), _ => r
              | Some None, [obj] =>
                  match box_ret (Some ft) with
                  | None => MStuckModel "Field.get: float/double"
                  | Some bx =>
                    if static then MFrame (Some d) (model_code nil nil (Getstatic fr :: bx) [Return (Some KA)] false) nil (Some (TRef "java/lang/Object")) s
                    else match obj with
                         | VNull => MThrow NPE
                         | VRef o => match ms_heap s o with
                                     | Some ob => match obj_assignable p ob d with
                                                  | Some true => MFrame None (model_code [obj] nil (Load KA 0 :: Getfield fr :: bx) [Return (Some KA)] false)
                                                                   [obj] (Some (TRef "java/lang/Object")) s
                                                  | _ => MStuckModel "Field.get: receiver of another class"
                                                  end
                                     | None => MStuckModel "Field.get"
                                     end
                         | _ => MStuckModel "Field.get"
                         end
                  end
              | _, _ => MStuckModel "Field.get"
              end
            else if String.eqb name "set" && String.eqb desc "(Ljava/lang/Object;Ljava/lang/Object;)V" then
              if Z.testbit mods 4 then MStuckModel "Field.set of a final field" else
              match check_access p s fs d mods, rest with
              | None, _ => MStuckModel "Field.set: access"
              | Some (Some r), _ => r
              | Some None, [obj; v] =>
                  match conv_arg p s ft v with
                  | Some (Some w) =>
                      if static then MFrame (Some d) (model_code [w] nil [Load (kind_of_val w) 0; Putstatic fr] [Return None] false) [w] None s
                      else match obj with
                           | VNull => MThrow NPE
                           | VRef o => match ms_heap s o with
                                       | Some ob => match obj_assignable p ob d with
                                                    | Some true => MFrame None (model_code [obj; w] nil [Load KA 0; Load (kind_of_val w) 1; Putfield fr] [Return None] false)
                                                                     [obj; w] None s
                                                    | _ => MStuckModel "Field.set: receiver of another class"
                                                    end
                                       | None => MStuckModel "Field.set"
                                       end
                           | _ => MStuckModel "Field.set"
                           end
                  | _ => MStuckModel "Field.set: value of another type"
                  end
              | _, _ => MStuckModel "Field.set"
              end
            else MNoModel
          | _ => MStuckModel "Field: descriptor"
          end
        else
          match parse_mdesc ds with
          | Some (ps, rt) =>
            if String.eqb name "getParameterCount" && String.eqb desc "()I" then ret_int s (Z.of_nat (length ps))
            else if String.eqb name "getParameterTypes" && String.eqb desc "()[Ljava/lang/Class;" then
              new_class_array s (map class_of_jtype ps)
            else if String.eqb name "getReturnType" && String.eqb desc "()Ljava/lang/Class;" && String.eqb k REFM then
              let (r, s') := cls_obj s (ret_class rt) in MOk (Some (VRef r)) s'
            else if String.eqb name "invoke" && String.eqb desc "(Ljava/lang/Object;[Ljava/lang/Object;)Ljava/lang/Object;" && String.eqb k REFM then
              let static := Z.testbit mods 3 in
              match rest with
              | [obj; arr] =>
                  (* Method.checkAccess (whose target class is obj.getClass(): NPE for null), then the
                     receiver, the argument count, the argument types *)
                  match (if static then false else match obj with VNull => true | _ => false end) with
                  | true => MThrow NPE
                  | false =>
                  match check_access p s fs d mods with
                  | None => MStuckModel "Method.invoke: access"
                  | Some (Some r) => r
                  | Some None =>
                    match (if static then Some true
                           else match obj with
                                | VRef o => match ms_heap s o with Some ob => obj_assignable p ob d | None => None end
                                | _ => None
                                end) with
                    | None => MStuckModel "Method.invoke: receiver"
                    | Some false => throw_with s IAEX (ascii_units "object is not an instance of declaring class")
                    | Some true =>
                      match array_elems s arr with
                      | None => MStuckModel "Method.invoke: arguments"
                      | Some es =>
                        if negb (Nat.eqb (length es) (length ps)) then wrong_args s (length es) (length ps) else
                        match conv_args p s ps es, box_ret rt with
                        | Some (Some ws), Some bx =>
                            let iface := match class_iface p d with Some b => b | None => false end in
                            let kind := if static then InvStatic else if iface then InvInterface else InvVirtual in
                            let mr := {| mr_class := d; mr_name := nm; mr_desc := ds; mr_interface := iface |} in
                            let locals := if static then ws else obj :: ws in
                            MFrame (if static then Some d else None)
                                   (model_code locals nil (app (loads locals 0) [Invoke kind mr]) (app bx [Return (Some KA)]) true)
                                   locals (Some (TRef "java/lang/Object")) s
                        | Some None, _ => throw_with s IAEX (ascii_units "argument type mismatch")
                        | _, _ => MStuckModel "Method.invoke: argument or result conversion"
                        end
                      end
                    end
                  end
                  end
              | _ => MStuckModel "Method.invoke"
              end
            else if String.eqb name "newInstance" && String.eqb desc "([Ljava/lang/Object;)Ljava/lang/Object;" && String.eqb k REFC then
              match class_access p d with
              | None => MStuckModel "newInstance"
              | Some ca =>
                if acc_abstract ca || Z.testbit ca 14 then MStuckModel "newInstance of an abstract class or an enum" else
                match check_access p s fs d mods, rest with
                | None, _ => MStuckModel "Constructor.newInstance: access"
                | Some (Some r), _ => r
                | Some None, [arr] =>
                    match array_elems s arr with
                    | None => MStuckModel "newInstance: arguments"
                    | Some es =>
                      if negb (Nat.eqb (length es) (length ps)) then wrong_args s (length es) (length ps) else
                      match conv_args p s ps es with
                      | Some (Some ws) =>
                          let mr := {| mr_class := d; mr_name := "<init>"; mr_desc := ds; mr_interface := false |} in
                          MFrame (Some d) (model_code ws [New d; Dup] (app (loads ws 0) [Invoke InvSpecial mr]) [Return (Some KA)] true)
                                 ws (Some (TRef "java/lang/Object")) s
                      | Some None => throw_with s IAEX (ascii_units "argument type mismatch")
                      | None => MStuckModel "newInstance: argument conversion"
                      end
                    end
                | _, _ => MStuckModel "newInstance"
                end
              end
            else MNoModel
          | None => MStuckModel "reflection: descriptor"
          end
      | _, _, _, _ => MNoModel
      end
    | _ => MNoModel
    end
  | _ => MNoModel
  end.

(** Class.getMethod / getDeclaredMethod / getConstructor / getDeclaredConstructor / getField /
    getDeclaredField, for loaded classes. *)
Definition class_member_model (p : program) (name desc : string) (n : string) (rest : list value) (s : mstate) : model_result :=
  let nsm := fun mname ns => throw_with s "java/lang/NoSuchMethodException" (method_string n mname ns) in
  if (String.eqb name "getMethod" || String.eqb name "getDeclaredMethod")
     && String.eqb desc "(Ljava/lang/String;[Ljava/lang/Class;)Ljava/lang/reflect/Method;" then
    match rest with
    | [VNull; _] => MThrow NPE
    | [nv; tv] =>
      match option_bind (str_of s nv) units_string, class_names s tv with
      | Some mname, Some ns =>
        let pd := params_desc ns in
        if String.eqb mname "<init>" || String.eqb mname "<clinit>" then nsm mname ns else
        if String.eqb name "getDeclaredMethod" then
          match find_class p n with
          | Some cf => match pick (decl_methods cf mname pd false) with
                       | Some (Some m) => mk_member s REFM n (m_name m) (m_desc m) (m_access m)
                       | Some None => nsm mname ns
                       | None => MStuckModel "getDeclaredMethod: several candidates"
                       end
          | None => MStuckModel "getDeclaredMethod of a JDK class"
          end
        else
          match chain_method p 32 n mname pd with
          | MLFound d m => mk_member s REFM d (m_name m) (m_desc m) (m_access m)
          | MLNone => if ifaces_lack p n mname pd then nsm mname ns else MStuckModel "getMethod: interface methods"
          | MLUnknown => MStuckModel "getMethod"
          end
      | _, _ => MStuckModel "getMethod: arguments"
      end
    | _ => MStuckModel "getMethod"
    end
  else if (String.eqb name "getConstructor" || String.eqb name "getDeclaredConstructor")
          && String.eqb desc "([Ljava/lang/Class;)Ljava/lang/reflect/Constructor;" then
    match rest with
    | [tv] =>
      match class_names s tv, find_class p n with
      | Some ns, Some cf =>
          match pick (decl_methods cf "<init>" (params_desc ns) (String.eqb name "getConstructor")) with
          | Some (Some m) => mk_member s REFC n "<init>" (m_desc m) (m_access m)
          | Some None => nsm "<init>" ns
          | None => MStuckModel "getConstructor"
          end
      | Some _, None => MStuckModel "getConstructor of a JDK class"
      | None, _ => MStuckModel "getConstructor: arguments"
      end
    | _ => MStuckModel "getConstructor"
    end
  else if (String.eqb name "getField" || String.eqb name "getDeclaredField")
          && String.eqb desc "(Ljava/lang/String;)Ljava/lang/reflect/Field;" then
    match rest with
    | [VNull] => MThrow NPE
    | [nv] =>
      match option_bind (str_of s nv) units_string with
      | Some fname =>
        let nsf := throw_with s "java/lang/NoSuchFieldException" (name_units fname) in
        if String.eqb name "getDeclaredField" then
          match find_class p n with
          | Some cf => match decl_field_in fname (cf_fields cf) with
                       | Some m => mk_member s REFF n (mb_name m) (mb_desc m) (mb_access m)
                       | None => nsf
                       end
          | None => MStuckModel "getDeclaredField of a JDK class"
          end
        else
          match pub_field p 32 n fname with
          | FLFound d m => mk_member s REFF d (mb_name m) (mb_desc m) (mb_access m)
          | FLNone => nsf
          | FLUnknown => MStuckModel "getField"
          end
      | None => MStuckModel "getField: name"
      end
    | _ => MStuckModel "getField"
    end
  else MNoModel.

(** A class that exists in the JDK as far as the model knows: a java.lang builtin, a class of
    the JDK tables, or an array class of such (or of a loaded class, or primitive). *)
Fixpoint known_class_go (p : program) (fuel : nat) (n : string) : bool :=
  match fuel with
  | O => false
  | S f =>
    if is_array_name n then
      match class_type n with
      | TArr t => match t with
                  | TRef c => match find_class p c with Some _ => true | None => known_class_go p f c end
                  | TArr _ => known_class_go p f (class_of_type t)
                  | _ => true
                  end
      | _ => false
      end
    else match builtin_super n with
         | Some _ => true
         | None => builtin_iface n || match jdk_info n with Some _ => true | None => false end
         end
  end.
Definition known_class (p : program) (n : string) : bool := known_class_go p 8 n.

Definition class_model (p : program) (name desc : string) (args : list value) (s : mstate) : model_result :=
  if String.eqb name "forName" && String.eqb desc "(Ljava/lang/String;)Ljava/lang/Class;" then
    (* Class.forName(name): the class must be known; it is initialised, so a class whose
       initialisation has not started yet is STUCK (the model cannot run <clinit>) *)
    match args with
    | [VNull] => MThrow "java/lang/NullPointerException"
    | [v] => match str_of s v with
             | Some u => match units_string (map (fun c => if (c =? 46)%Z then 47 else c)%Z u) with
                         | Some n =>
                             if erroneous p 64 (ms_statics s) n then MThrow "java/lang/NoClassDefFoundError" else
                             match find_class p n with
                             | Some _ =>
                                 (* a loaded class: initialise it, if that needs no <clinit> code *)
                                 match start_chain p s true (rev (uninit_chain p 64 (ms_inited s) n)) with
                                 | Some (s1, nil) => let (r, s') := cls_obj s1 n in MOk (Some (VRef r)) s'
                                 | Some _ => MStuckModel "Class.forName needs class initialisation (<clinit>)"
                                 | None => MStuckModel "Class.forName: class initialisation"
                                 end
                             | None =>
                                 if known_class p n then let (r, s') := cls_obj s n in MOk (Some (VRef r)) s'
                                 else MStuckModel "Class.forName of a class the model does not know"
                             end
                         | None => MStuckModel "Class.forName: name"
                         end
             | None => MStuckModel "Class.forName: argument"
             end
    | _ => MStuckModel "Class.forName"
    end
  else
  match args with
  | VRef l :: rest =>
    match ms_heap s l with
    | Some (OCls n) =>
      match prim_name n with
      | Some u =>
        (* a primitive class (the component class of a primitive array) *)
        if (String.eqb name "getName" || String.eqb name "getSimpleName" || String.eqb name "getTypeName"
            || String.eqb name "toString") && String.eqb desc "()Ljava/lang/String;" then ret_lit s u
        else if String.eqb name "isPrimitive" && String.eqb desc "()Z" then ret_bool s true
        else if (String.eqb name "isArray" || String.eqb name "isInterface" || String.eqb name "isEnum"
                 || String.eqb name "desiredAssertionStatus") && String.eqb desc "()Z" then ret_bool s false
        else if (String.eqb name "getSuperclass" || String.eqb name "getComponentType") && String.eqb desc "()Ljava/lang/Class;" then
          MOk (Some VNull) s
        else if String.eqb name "isInstance" && String.eqb desc "(Ljava/lang/Object;)Z" then ret_bool s false
        else if String.eqb name "isAssignableFrom" && String.eqb desc "(Ljava/lang/Class;)Z" then
          match rest with [VNull] => MThrow "java/lang/NullPointerException" | [v] => ret_bool s (ref_eq (VRef l) v) | _ => MStuckModel "isAssignableFrom" end
        else if String.eqb name "equals" && String.eqb desc "(Ljava/lang/Object;)Z" then
          match rest with [v] => ret_bool s (ref_eq (VRef l) v) | _ => MStuckModel "equals" end
        else MNoModel
      | None =>
      match class_member_model p name desc n rest s with
      | MNoModel =>
      if String.eqb name "getName" && String.eqb desc "()Ljava/lang/String;" then ret_lit s (class_name_units n)
      else if String.eqb name "getTypeName" && String.eqb desc "()Ljava/lang/String;" && negb (is_array_name n) then
        ret_lit s (class_name_units n)
      else if String.eqb name "getSimpleName" && String.eqb desc "()Ljava/lang/String;" then
        match simple_name_of p 8 n with Some u => ret_lit s u | None => MStuckModel "getSimpleName" end
      else if String.eqb name "isArray" && String.eqb desc "()Z" then ret_bool s (is_array_name n)
      else if String.eqb name "isPrimitive" && String.eqb desc "()Z" then ret_bool s false
      else if String.eqb name "isInterface" && String.eqb desc "()Z" then
        match class_iface p n with Some b => ret_bool s b | None => MStuckModel "isInterface" end
      else if String.eqb name "isEnum" && String.eqb desc "()Z" then
        match class_access p n, class_super p n with
        | Some a, Some sup => ret_bool s (Z.testbit a 14 && match sup with Some c => String.eqb c "java/lang/Enum" | None => false end)
        | _, _ => if is_array_name n || builtin_iface n then ret_bool s false
                  else match builtin_super n with Some _ => ret_bool s false | None => MStuckModel "isEnum" end
        end
      else if String.eqb name "getSuperclass" && String.eqb desc "()Ljava/lang/Class;" then
        match class_super p n with
        | Some None => MOk (Some VNull) s
        | Some (Some c) => let (r, s') := cls_obj s c in MOk (Some (VRef r)) s'
        | None => MStuckModel "getSuperclass"
        end
      else if String.eqb name "getComponentType" && String.eqb desc "()Ljava/lang/Class;" then
        match class_type n with
        | TArr t => match t with
                    | _ => let (r, s') := cls_obj s (class_of_type t) in MOk (Some (VRef r)) s'
                    end
        | _ => MOk (Some VNull) s
        end
      else if String.eqb name "isInstance" && String.eqb desc "(Ljava/lang/Object;)Z" then
        match rest with
        | [VNull] => ret_bool s false
        | [VRef o] => match ms_heap s o with
                      | Some ob => match obj_assignable p ob n with Some b => ret_bool s b | None => MStuckModel "isInstance" end
                      | None => MStuckModel "isInstance"
                      end
        | _ => MStuckModel "isInstance"
        end
      else if String.eqb name "isAssignableFrom" && String.eqb desc "(Ljava/lang/Class;)Z" then
        match rest with
        | [VNull] => MThrow "java/lang/NullPointerException"
        | [VRef o] => match ms_heap s o with
                      | Some (OCls m) => match assignable p 64 (class_type m) n with
                                         | Some b => ret_bool s b
                                         | None => MStuckModel "isAssignableFrom"
                                         end
                      | _ => MStuckModel "isAssignableFrom"
                      end
        | _ => MStuckModel "isAssignableFrom"
        end
      else if String.eqb name "cast" && String.eqb desc "(Ljava/lang/Object;)Ljava/lang/Object;" then
        match rest with
        | [VNull] => MOk (Some VNull) s
        | [VRef o] => match ms_heap s o with
                      | Some ob => match obj_assignable p ob n with
                                   | Some true => MOk (Some (VRef o)) s
                                   | Some false => MThrow "java/lang/ClassCastException"
                                   | None => MStuckModel "cast"
                                   end
                      | None => MStuckModel "cast"
                      end
        | _ => MStuckModel "cast"
        end
      else if String.eqb name "desiredAssertionStatus" && String.eqb desc "()Z" then
        (* assertions are disabled (no -ea), as in the differential tests *)
        ret_bool s false
      else if String.eqb name "toString" && String.eqb desc "()Ljava/lang/String;" then
        match class_iface p n with
        | Some b => ret_new s (OStr (app (ascii_units (if b then "interface " else "class ")) (class_name_units n)))
        | None => MStuckModel "Class.toString"
        end
      else if String.eqb name "equals" && String.eqb desc "(Ljava/lang/Object;)Z" then
        match rest with [v] => ret_bool s (ref_eq (VRef l) v) | _ => MStuckModel "equals" end
      else MNoModel
      | r => r
      end
      end
    | _ => MNoModel
    end
  | _ => MNoModel
  end.

(** A synchronized method on the stack whose monitor is [l]: [this] (local 0, which javac
    never overwrites in an instance method) or, for a static one, its class object. *)
Definition sync_frame_holds (s : mstate) (l : Z) : bool :=
  existsb (fun f =>
    Z.testbit (m_access (cf_method f)) 5 && negb (cf_clinit f) &&
    (if Z.testbit (m_access (cf_method f)) 3
     then match assoc (intern_key (OCls (cf_class f))) (ms_statics s) with Some (VRef c) => (c =? l)%Z | _ => false end
     else match f_locals (cf_frame f) with VRef t :: _ => (t =? l)%Z | _ => false end)) (ms_frames s).

(** ** java.lang.Object (methods reached on objects of loaded classes) and clone of arrays *)
Definition object_model (name desc : string) (args : list value) (s : mstate) : model_result :=
  match args with
  | this :: rest =>
    if String.eqb name "equals" && String.eqb desc "(Ljava/lang/Object;)Z" then
      match rest with [v] => ret_bool s (ref_eq this v) | _ => MStuckModel "equals" end
    else if String.eqb name "getClass" && String.eqb desc "()Ljava/lang/Class;" then
      match this with
      | VRef l => match ms_heap s l with
                  | Some o => let n := match runtime_type o with TRef c => c | t => type_desc t end in
                              let (r, s') := intern s (OCls n) in MOk (Some (VRef r)) s'
                  | None => MStuckModel "getClass"
                  end
      | _ => MStuckModel "getClass"
      end
    else if (String.eqb name "notify" || String.eqb name "notifyAll") && String.eqb desc "()V" then
      (* one thread: no other thread waits; the caller must own the monitor, entered by
         monitorenter or by a synchronized method on the stack (the single-thread machine
         keeps no count for those; the thread layer, Threads.v, intercepts notify itself) *)
      match this with
      | VRef l => if (0 <? lock_count (ms_locks s) l)%Z || sync_frame_holds s l then MOk None s
                  else MThrow "java/lang/IllegalMonitorStateException"
      | _ => MStuckModel "notify"
      end
    else if String.eqb name "clone" && String.eqb desc "()Ljava/lang/Object;" then
      match arr_of s this with
      | Some (_, t, es) => ret_new s (OArr t es)
      | None => MStuckModel "clone of a non-array (Cloneable objects not modelled yet)"
      end
    else MNoModel
  | nil => MNoModel
  end.


(** Constructors of the java.lang exceptions keep the message (field "detailMessage", as the
    VM-created exceptions of Machine.throw_msg); causes and stack traces are not modelled. The
    (Throwable) constructor takes cause.toString() as message, modelled only for a null cause. *)
Definition set_detail (fs : list (string * value)) (v : value) : list (string * value) :=
  ("detailMessage", v) :: filter (fun kv => negb (String.eqb (fst kv) "detailMessage")) fs.

Definition throwable_init (desc : string) (args : list value) (s : mstate) : model_result :=
  match args with
  | VRef l :: rest =>
    match ms_heap s l with
    | Some (OObj c fs) =>
      if String.eqb desc "()V" then MOk None (set_heap s l (OObj c (set_detail fs VNull)))
      else if String.eqb desc "(Ljava/lang/Throwable;)V" then
        match rest with
        | [VNull] => MOk None (set_heap s l (OObj c (set_detail fs VNull)))
        | [t] => if String.eqb c "java/lang/reflect/InvocationTargetException"
                 then (* InvocationTargetException(target): super((Throwable) null), the target kept *)
                      MOk None (set_heap s l (OObj c (("target", t) :: set_detail fs VNull)))
                 else MStuckModel "Throwable(cause): message is cause.toString()"
        | _ => MStuckModel "Throwable(cause)"
        end
      else match rest with
           | m :: _ => match m with
                       | VNull | VRef _ => MOk None (set_heap s l (OObj c (set_detail fs m)))
                       | _ => MStuckModel "Throwable.<init>"
                       end
           | nil => MStuckModel "Throwable.<init>"
           end
    | _ => MOk None s
    end
  | _ => MOk None s
  end.

(** ** The JDK model *)
Definition jdk_model (p : program) (e : jenv) : model :=
  fun cls name desc args s =>
    (* constructors of the java.lang exceptions: no observable state is modelled *)
    if String.eqb name "<init>" && is_builtin_throwable cls
       && (String.eqb desc "()V" || String.eqb desc "(Ljava/lang/String;)V"
           || String.eqb desc "(Ljava/lang/String;Ljava/lang/Throwable;)V"
           || String.eqb desc "(Ljava/lang/Throwable;)V") then throwable_init desc args s
    else if (String.eqb cls "java/lang/Record" || String.eqb cls "java/lang/Number")
            && String.eqb name "<init>" && String.eqb desc "()V" then MOk None s
    (* Comparable.compareTo(Object) on a String or a box (the bridge method: the argument is cast
       to the receiver's class first) *)
    else if String.eqb cls "java/lang/Comparable" && String.eqb name "compareTo" && String.eqb desc "(Ljava/lang/Object;)I" then
      match args with
      | [this; o] =>
          match str_of s this with
          | Some a => match o with
                      | VNull => MThrow NPE
                      | _ => match str_of s o with
                             | Some b => ret_int s (compare_units a b)
                             | None => MThrow "java/lang/ClassCastException"
                             end
                      end
          | None =>
              match this with
              | VRef l =>
                  match ms_heap s l with
                  | Some (OObj c _) =>
                      if is_box_class c then
                        match o with
                        | VNull => MThrow NPE
                        | VRef l2 => match ms_heap s l2 with
                                     | Some (OObj c2 _) => if String.eqb c c2 then box_model c "compareTo" desc args s
                                                           else MThrow "java/lang/ClassCastException"
                                     | Some _ => MThrow "java/lang/ClassCastException"
                                     | None => MStuckModel "compareTo: dangling argument"
                                     end
                        | _ => MStuckModel "compareTo: argument"
                        end
                      else MNoModel
                  | _ => MNoModel
                  end
              | _ => MNoModel
              end
          end
      | _ => MStuckModel "compareTo args"
      end
    (* Integer.TYPE (int.class) and the other primitive classes *)
    else if String.eqb name "<get>TYPE" && String.eqb desc "Ljava/lang/Class;"
            && (is_box_class cls || String.eqb cls "java/lang/Float" || String.eqb cls "java/lang/Double" || String.eqb cls "java/lang/Void") then
      let d := if String.eqb cls "java/lang/Float" then "F" else if String.eqb cls "java/lang/Double" then "D"
               else if String.eqb cls "java/lang/Void" then "V" else prim_desc cls in
      let (r, s') := intern s (OCls d) in MOk (Some (VRef r)) s'
    (* Throwable.getMessage / getLocalizedMessage of a VM-created exception
       (Machine.throw_msg); other exception objects carry no modelled message *)
    else if is_builtin_throwable cls && (String.eqb name "getCause" && String.eqb desc "()Ljava/lang/Throwable;"
                                         || String.eqb name "getTargetException" && String.eqb desc "()Ljava/lang/Throwable;") then
      match args with
      | [VRef l] => match ms_heap s l with
                    | Some (OObj _ fs) => match assoc "target" fs with Some v => MOk (Some v) s | None => MStuckModel "getCause: causes are not modelled" end
                    | _ => MStuckModel "getCause"
                    end
      | _ => MStuckModel "getCause"
      end
    else if is_builtin_throwable cls && String.eqb name "toString" && String.eqb desc "()Ljava/lang/String;" then
      match args with
      | [VRef l] => match ms_heap s l with
                    | Some (OObj c fs) =>
                        match find_class p c, assoc "detailMessage" fs with
                        | None, Some VNull => ret_new s (OStr (class_name_units c))
                        | None, Some v => match str_of s v with
                                          | Some u => ret_new s (OStr (app (class_name_units c) (app [58; 32] u)))
                                          | None => MStuckModel "Throwable.toString"
                                          end
                        | _, _ => MStuckModel "Throwable.toString"
                        end
                    | _ => MStuckModel "Throwable.toString"
                    end
      | _ => MStuckModel "Throwable.toString"
      end
    else if is_builtin_throwable cls && (String.eqb name "getMessage" || String.eqb name "getLocalizedMessage")
            && String.eqb desc "()Ljava/lang/String;" then
      match args with
      | [VRef l] => match ms_heap s l with
                    | Some (OObj c fs) =>
                        (* the message set by a modelled constructor (also of a loaded subclass,
                           which reaches this model only if it does not override getMessage) *)
                        match assoc "detailMessage" fs with
                        | Some v => MOk (Some v) s
                        | None => MStuckModel "exception message not modelled"
                        end
                    | _ => MStuckModel "getMessage"
                    end
      | _ => MStuckModel "getMessage"
      end
    else if String.eqb cls "java/lang/Object" then
      if String.eqb name "<init>" && String.eqb desc "()V" then MOk None s
      else object_model name desc args s
    else if String.eqb cls "java/lang/String" then
      match string_model e name desc args s with
      | MNoModel => match string_static name desc args s with
                    | MNoModel => object_model name desc args s
                    | r => r
                    end
      | r => r
      end
    else if String.eqb cls "java/lang/StringBuilder" || String.eqb cls "java/lang/AbstractStringBuilder" then
      sb_model name desc args s
    else if is_box_class cls && match box_model cls name desc args s with MNoModel => false | _ => true end then
      box_model cls name desc args s
    else if String.eqb cls "java/lang/Character" then char_model e name desc args s
    else if String.eqb cls "java/lang/Integer" || String.eqb cls "java/lang/Long" || String.eqb cls "java/lang/Math" then
      num_model e cls name desc args s
    else if String.eqb cls "java/util/Objects" then objects_model name desc args s
    else if String.eqb cls "java/lang/System" && String.eqb name "arraycopy" then arraycopy p args s
    else if String.eqb cls "java/util/Arrays" then arrays_model p name desc args s
    else if String.eqb cls "java/lang/Enum" then enum_model name desc args s
    else if prefix "[" cls then object_model name desc args s
    else if prefix "org/slf4j/" cls then slf4j_model e cls name desc args s
    else if String.eqb cls "java/lang/Class" then class_model p name desc args s
    else if String.eqb cls REFM || String.eqb cls REFC || String.eqb cls REFF
            || String.eqb cls "java/lang/reflect/Executable" || String.eqb cls "java/lang/reflect/AccessibleObject" then
      reflect_model p cls name desc args s
    else MNoModel.

(** ** Entry with String arguments (for the harness and for theorem statements):
    each [JStr] argument is a fresh (non-interned) String object, allocated
    before the call, as [new String(chars)] does on the HotSpot side. *)
Inductive jarg : Type := JVal (v : value) | JStr (u : list Z) | JNull.

Fixpoint alloc_args (s : mstate) (xs : list jarg) : list value * mstate :=
  match xs with
  | nil => (nil, s)
  | JVal v :: r => let (vs, s') := alloc_args s r in (v :: vs, s')
  | JNull :: r => let (vs, s') := alloc_args s r in (VNull :: vs, s')
  | JStr u :: r => let (l, s1) := alloc s (OStr u) in
                   let (vs, s') := alloc_args s1 r in (VRef l :: vs, s')
  end.

Definition call_static_args (p : program) (mdl : model) (fuel : nat) (cls name desc : string)
           (xs : list jarg) : mresult :=
  let s0 := {| ms_heap := fun _ => None; ms_next := 1; ms_statics := nil; ms_inited := nil;
               ms_locks := nil; ms_frames := nil |} in
  let (vs, s1) := alloc_args s0 xs in
  match entry_state cls name desc vs with
  | Some s => mrun p mdl fuel {| ms_heap := ms_heap s1; ms_next := ms_next s1; ms_statics := nil;
                                 ms_inited := nil; ms_locks := nil; ms_frames := ms_frames s |}
  | None => MRStuck "entry: bad descriptor or arguments"
  end.

Definition str_value (s : mstate) (v : value) : option (list Z) := str_of s v.

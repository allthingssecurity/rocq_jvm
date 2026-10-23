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
From JVM.Core Require Import Int Instr Desc Semantics Machine.
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
Definition string_model (e : jenv) (name desc : string) (args : list value) (s : mstate) : model_result :=
  let u := j_u e in
  match args with
  | nil => MNoModel
  | this :: rest =>
  match str_of s this with
  | None => MNoModel
  | Some a =>
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
  end
  end.

(** static String.valueOf(...) *)
Definition string_static (name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := name ++ desc in
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
    | [v] => match str_of s v with Some _ => MOk (Some v) s | None => MStuckModel "valueOf(Object): toString callback" end
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
               | None => MStuckModel ("StringBuilder.append" ++ desc ++ ": not modelled for this argument")
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

Definition num_model (e : jenv) (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := cls ++ "." ++ name ++ desc in
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
    else if String.eqb name "clone" && String.eqb desc "()Ljava/lang/Object;" then
      match arr_of s this with
      | Some (_, t, es) => ret_new s (OArr t es)
      | None => MStuckModel "clone of a non-array (Cloneable objects not modelled yet)"
      end
    else MNoModel
  | nil => MNoModel
  end.


(** ** The JDK model *)
Definition jdk_model (p : program) (e : jenv) : model :=
  fun cls name desc args s =>
    (* constructors of the java.lang exceptions: no observable state is modelled *)
    if String.eqb name "<init>" && is_builtin_throwable cls
       && (String.eqb desc "()V" || String.eqb desc "(Ljava/lang/String;)V"
           || String.eqb desc "(Ljava/lang/String;Ljava/lang/Throwable;)V"
           || String.eqb desc "(Ljava/lang/Throwable;)V") then MOk None s
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

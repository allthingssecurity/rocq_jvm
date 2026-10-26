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
From JVM.Core Require Float FloatDec FloatMath.
Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.
Open Scope Z_scope.

Record jenv := {
  j_u : uenv;
  j_log_enabled : string -> bool;   (** "isDebugEnabled" etc. of slf4j loggers *)
  j_ihash : Z -> Z;                 (** identity hash code of the object at a heap address (unspecified
                                        by the JVMS: a parameter, as the Unicode tables) *)
  j_seed : Z -> Z;                  (** values the JDK draws once per run from the outside world
                                        (java.util.ModelEnv.seed(n)): 0 = the SALT32L of the immutable
                                        collections (Set.of/Map.of iteration order) *)
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

(** Character.digit(c, radix) (CharacterData.digit): a decimal digit's value, or 10.. for the
    Latin letters (ASCII and fullwidth), if below the radix; -1 otherwise. *)
Definition char_digit (u : uenv) (c r : Z) : Z :=
  if (r <? 2) || (36 <? r) then -1 else
  let v := if u_is_digit u c then u_digit u c 10
           else if (65 <=? c) && (c <=? 90) then c - 55
           else if (97 <=? c) && (c <=? 122) then c - 87
           else if (65313 <=? c) && (c <=? 65338) then c - 65303
           else if (65345 <=? c) && (c <=? 65370) then c - 65335
           else -1 in
  if (0 <=? v) && (v <? r) then v else -1.

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
  else if String.eqb name "hashCode" && String.eqb desc ("(" ++ pd ++ ")I")
          && (String.eqb cls "java/lang/Boolean" || String.eqb cls "java/lang/Short" || String.eqb cls "java/lang/Byte") then
    (* Boolean.hashCode(b): 1231 / 1237; Short/Byte.hashCode(v): (int) v *)
    match args with
    | [VInt z] => ret_int s (if String.eqb cls "java/lang/Boolean" then (if z =? 0 then 1237 else 1231) else z)
    | _ => MStuckModel "hashCode"
    end
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
      else if (String.eqb key "doubleValue()D" || String.eqb key "floatValue()F")
              && negb (String.eqb cls "java/lang/Character") && negb (String.eqb cls "java/lang/Boolean") then
        (* Number.doubleValue / floatValue: the widening conversion (i2d, l2d, i2f, l2f) *)
        if String.eqb key "doubleValue()D" then MOk (Some (VDouble (Float.of_int Float.binary64 z))) s
        else MOk (Some (VFloat (Float.of_int Float.binary32 z))) s
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

(** ** java.lang.Double and java.lang.Float boxes (no caches: JDK 21 Double/Float.valueOf always
    allocate), their xxxValue conversions (the JVM's d2f/d2i/...), hashCode/equals/compareTo through
    doubleToLongBits / floatToIntBits (one canonical NaN), and the static helpers compare, isNaN,
    isInfinite, isFinite, hashCode, the bit conversions; toString and parseDouble/parseFloat/valueOf
    (the decimal conversions of JDK 21, theories/Core/FloatDec.v). *)
Definition is_fbox (cls : string) : bool := String.eqb cls "java/lang/Double" || String.eqb cls "java/lang/Float".

Definition fbox_bits (s : mstate) (cls : string) (v : value) : option Z :=
  match v with
  | VRef l => match ms_heap s l with
              | Some (OObj c [("value", (VDouble b | VFloat b))]) => if String.eqb c cls then Some b else None
              | _ => None
              end
  | _ => None
  end.

Definition signed (w : Z) (b : Z) : Z := if b <? 2 ^ (w - 1) then b else b - 2 ^ w.

(** Double.compare / Float.compare *)
Definition fcompare (dbl : bool) (a b : Z) : Z :=
  let lt := if dbl then Float.dcmpg a b =? -1 else Float.fcmpg a b =? -1 in
  let gt := if dbl then Float.dcmpl a b =? 1 else Float.fcmpl a b =? 1 in
  if lt then -1 else if gt then 1
  else let ca := signed (if dbl then 64 else 32) (Float.canon (if dbl then Float.binary64 else Float.binary32) a) in
       let cb := signed (if dbl then 64 else 32) (Float.canon (if dbl then Float.binary64 else Float.binary32) b) in
       if ca =? cb then 0 else if ca <? cb then -1 else 1.

Definition fhash (dbl : bool) (b : Z) : Z :=
  if dbl then let c := Float.canon Float.binary64 b in wrap32 (Z.lxor c (Z.shiftr c 32))
  else wrap32 (Float.canon Float.binary32 b).

Definition fbox_model (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  let dbl := String.eqb cls "java/lang/Double" in
  let fmt := if dbl then Float.binary64 else Float.binary32 in
  let mk := fun b => if dbl then VDouble b else VFloat b in
  let key := name ++ desc in
  let pd := if dbl then "D" else "F" in
  if String.eqb key ("valueOf(" ++ pd ++ ")L" ++ cls ++ ";") then
    match args with [(VDouble b | VFloat b)] => ret_new s (OObj cls [("value", mk b)]) | _ => MStuckModel "valueOf" end
  else if String.eqb key ("sum(" ++ pd ++ pd ++ ")" ++ pd) || String.eqb key ("max(" ++ pd ++ pd ++ ")" ++ pd)
          || String.eqb key ("min(" ++ pd ++ pd ++ ")" ++ pd) then
    (* Double.sum = a + b; Double.max/min = Math.max/min *)
    match args with
    | [(VDouble a | VFloat a); (VDouble b | VFloat b)] =>
        let r := if String.eqb name "sum" then Float.add fmt a b
                 else if String.eqb name "max" then FloatMath.fmax fmt a b else FloatMath.fmin fmt a b in
        MOk (Some (mk r)) s
    | _ => MStuckModel "Double.sum/max/min"
    end
  else if String.eqb key ("compare(" ++ pd ++ pd ++ ")I") then
    match args with [(VDouble a | VFloat a); (VDouble b | VFloat b)] => ret_int s (fcompare dbl a b) | _ => MStuckModel "compare" end
  else if String.eqb key ("isNaN(" ++ pd ++ ")Z") then
    match args with [(VDouble a | VFloat a)] => ret_bool s (Float.is_nan fmt a) | _ => MStuckModel "isNaN" end
  else if String.eqb key ("isInfinite(" ++ pd ++ ")Z") then
    match args with [(VDouble a | VFloat a)] => ret_bool s (Float.is_inf fmt a) | _ => MStuckModel "isInfinite" end
  else if String.eqb key ("isFinite(" ++ pd ++ ")Z") then
    match args with [(VDouble a | VFloat a)] => ret_bool s (Float.is_finite fmt a) | _ => MStuckModel "isFinite" end
  else if String.eqb key ("hashCode(" ++ pd ++ ")I") then
    match args with [(VDouble a | VFloat a)] => ret_int s (fhash dbl a) | _ => MStuckModel "hashCode" end
  else if String.eqb key "doubleToLongBits(D)J" then
    match args with [VDouble a] => MOk (Some (VLong (signed 64 (Float.canon fmt a)))) s | _ => MStuckModel "doubleToLongBits" end
  else if String.eqb key "doubleToRawLongBits(D)J" then
    match args with [VDouble a] => MOk (Some (VLong (signed 64 a))) s | _ => MStuckModel "doubleToRawLongBits" end
  else if String.eqb key "longBitsToDouble(J)D" then
    match args with [VLong a] => MOk (Some (VDouble (a mod 2 ^ 64))) s | _ => MStuckModel "longBitsToDouble" end
  else if String.eqb key "floatToIntBits(F)I" then
    match args with [VFloat a] => ret_int s (signed 32 (Float.canon fmt a)) | _ => MStuckModel "floatToIntBits" end
  else if String.eqb key "floatToRawIntBits(F)I" then
    match args with [VFloat a] => ret_int s (signed 32 a) | _ => MStuckModel "floatToRawIntBits" end
  else if String.eqb key "intBitsToFloat(I)F" then
    match args with [VInt a] => MOk (Some (VFloat (a mod 2 ^ 32))) s | _ => MStuckModel "intBitsToFloat" end
  else if String.eqb key ("toHexString(" ++ pd ++ ")Ljava/lang/String;") then
    match args with [(VDouble b | VFloat b)] => ret_new s (OStr (FloatDec.to_hex fmt b)) | _ => MStuckModel "toHexString" end
  else if String.eqb key ("toString(" ++ pd ++ ")Ljava/lang/String;") then
    match args with
    | [(VDouble b | VFloat b)] => match FloatDec.to_dec fmt b with Some u => ret_new s (OStr u) | None => MStuckModel "toString" end
    | _ => MStuckModel "toString"
    end
  else if String.eqb key (if dbl then "parseDouble(Ljava/lang/String;)D" else "parseFloat(Ljava/lang/String;)F")
          || String.eqb key ("valueOf(Ljava/lang/String;)L" ++ cls ++ ";") then
    let throw_m := fun (c : string) (u : list Z) =>
      let (m, s1) := alloc s (OStr u) in
      let (l, s2) := alloc s1 (OObj c [("detailMessage", VRef m)]) in MThrowObj l s2 in
    match args with
    | [VNull] => (* FloatingDecimal.readJavaFormatString: in.trim() *)
        throw_m NPE (ascii_units "Cannot invoke ""String.trim()"" because ""in"" is null")
    | [v] => match str_of s v with
             | Some u => match FloatDec.parse fmt u with
                         | FloatDec.PVal b => if String.eqb name "valueOf" then ret_new s (OObj cls [("value", mk b)])
                                              else MOk (Some (mk b)) s
                         | FloatDec.PErr m => throw_m "java/lang/NumberFormatException" m
                         end
             | None => MStuckModel "parse: argument"
             end
    | _ => MStuckModel "parse"
    end
  else
  match args with
  | this :: more =>
    match fbox_bits s cls this with
    | None => MNoModel
    | Some b =>
      if String.eqb key "doubleValue()D" then MOk (Some (VDouble (if dbl then b else Float.f2d b))) s
      else if String.eqb key "floatValue()F" then MOk (Some (VFloat (if dbl then Float.d2f b else b))) s
      else if String.eqb key "intValue()I" then ret_int s (if dbl then Float.d2i b else Float.f2i b)
      else if String.eqb key "longValue()J" then MOk (Some (VLong (if dbl then Float.d2l b else Float.f2l b))) s
      else if String.eqb key "shortValue()S" then ret_int s (i2s (if dbl then Float.d2i b else Float.f2i b))
      else if String.eqb key "byteValue()B" then ret_int s (i2b (if dbl then Float.d2i b else Float.f2i b))
      else if String.eqb key "toString()Ljava/lang/String;" then
        match FloatDec.to_dec fmt b with Some u => ret_new s (OStr u) | None => MStuckModel "toString" end
      else if String.eqb key "isNaN()Z" then ret_bool s (Float.is_nan fmt b)
      else if String.eqb key "isInfinite()Z" then ret_bool s (Float.is_inf fmt b)
      else if String.eqb key "hashCode()I" then ret_int s (fhash dbl b)
      else if String.eqb key "equals(Ljava/lang/Object;)Z" then
        match more with
        | [o] => ret_bool s (match fbox_bits s cls o with Some b' => Z.eqb (Float.canon fmt b) (Float.canon fmt b') | None => false end)
        | _ => MStuckModel "equals"
        end
      else if String.eqb name "compareTo" then
        match more with
        | [VNull] => MThrow NPE
        | [o] => match fbox_bits s cls o with
                 | Some b' => ret_int s (fcompare dbl b b')
                 | None => MThrow "java/lang/ClassCastException"
                 end
        | _ => MStuckModel "compareTo"
        end
      else MNoModel
    end
  | nil => MNoModel
  end.

(** ** java.lang.Math / StrictMath on float and double (theories/Core/FloatMath.v): the methods
    the specification fixes exactly; pow only where the specification fixes its result. *)
Definition DEG2RAD : Z := 4580687790476533049.   (* 0x3f91df46a2529d39 = Math.PI / 180 *)
Definition RAD2DEG : Z := 4633260481411531256.   (* 0x404ca5dc1a63c1f8 = 180 / Math.PI *)

Definition fmath_model (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  let strict := String.eqb cls "java/lang/StrictMath" in
  let key := name ++ desc in
  let d64 := Float.binary64 in
  let f32 := Float.binary32 in
  let rd := fun b => MOk (Some (VDouble b)) s in
  let rf := fun b => MOk (Some (VFloat b)) s in
  match args with
  | [VDouble a] =>
      if String.eqb key "abs(D)D" then rd (FloatMath.fabs d64 a)
      else if String.eqb key "signum(D)D" then rd (FloatMath.fsignum d64 a)
      else if String.eqb key "floor(D)D" then rd (FloatMath.fround_int d64 (-1) a)
      else if String.eqb key "ceil(D)D" then rd (FloatMath.fround_int d64 1 a)
      else if String.eqb key "rint(D)D" then rd (FloatMath.fround_int d64 0 a)
      else if String.eqb key "round(D)J" then MOk (Some (VLong (FloatMath.fround d64 LONG_MIN LONG_MAX a))) s
      else if String.eqb key "sqrt(D)D" then rd (FloatMath.fsqrt d64 a)
      else if String.eqb key "ulp(D)D" then rd (FloatMath.fulp d64 a)
      else if String.eqb key "nextUp(D)D" then rd (FloatMath.fnext_up d64 a)
      else if String.eqb key "nextDown(D)D" then rd (FloatMath.fnext_down d64 a)
      else if String.eqb key "getExponent(D)I" then ret_int s (FloatMath.fget_exponent d64 a)
      else if String.eqb key "toRadians(D)D" then rd (Float.dmul64 a DEG2RAD)
      else if String.eqb key "toDegrees(D)D" then rd (Float.dmul64 a RAD2DEG)
      else MNoModel
  | [VDouble a; VDouble b] =>
      if String.eqb key "max(DD)D" then rd (FloatMath.fmax d64 a b)
      else if String.eqb key "min(DD)D" then rd (FloatMath.fmin d64 a b)
      else if String.eqb key "copySign(DD)D" then rd ((if strict then FloatMath.fcopysign_strict else FloatMath.fcopysign) d64 a b)
      else if String.eqb key "IEEEremainder(DD)D" then rd (FloatMath.fremainder d64 a b)
      else if String.eqb key "nextAfter(DD)D" then
        rd (FloatMath.fnext_after d64 a (FloatMath.flt d64 b a) (FloatMath.flt d64 a b) (FloatMath.feq d64 a b) b false)
      else if String.eqb key "pow(DD)D" && negb strict then
        match FloatMath.fpow d64 a b with Some r => rd r | None => MStuckModel "Math.pow: result not fixed by the specification (HotSpot intrinsic)" end
      else MNoModel
  | [VDouble a; VDouble b; VDouble c] =>
      if String.eqb key "fma(DDD)D" then rd (FloatMath.ffma d64 a b c) else MNoModel
  | [VDouble a; VInt n] =>
      if String.eqb key "scalb(DI)D" then rd (FloatMath.fscalb d64 a n) else MNoModel
  | [VFloat a] =>
      if String.eqb key "abs(F)F" then rf (FloatMath.fabs f32 a)
      else if String.eqb key "signum(F)F" then rf (FloatMath.fsignum f32 a)
      else if String.eqb key "round(F)I" then ret_int s (FloatMath.fround f32 INT_MIN INT_MAX a)
      else if String.eqb key "ulp(F)F" then rf (FloatMath.fulp f32 a)
      else if String.eqb key "nextUp(F)F" then rf (FloatMath.fnext_up f32 a)
      else if String.eqb key "nextDown(F)F" then rf (FloatMath.fnext_down f32 a)
      else if String.eqb key "getExponent(F)I" then ret_int s (FloatMath.fget_exponent f32 a)
      else MNoModel
  | [VFloat a; VFloat b] =>
      if String.eqb key "max(FF)F" then rf (FloatMath.fmax f32 a b)
      else if String.eqb key "min(FF)F" then rf (FloatMath.fmin f32 a b)
      else if String.eqb key "copySign(FF)F" then rf ((if strict then FloatMath.fcopysign_strict else FloatMath.fcopysign) f32 a b)
      else MNoModel
  | [VFloat a; VFloat b; VFloat c] =>
      if String.eqb key "fma(FFF)F" then rf (FloatMath.ffma f32 a b c) else MNoModel
  | [VFloat a; VInt n] =>
      if String.eqb key "scalb(FI)F" then rf (FloatMath.fscalb f32 a n) else MNoModel
  | [VFloat a; VDouble b] =>
      if String.eqb key "nextAfter(FD)F" then
        let a' := Float.f2d a in
        rf (FloatMath.fnext_after f32 a (FloatMath.flt d64 b a') (FloatMath.flt d64 a' b) (FloatMath.feq d64 a' b) (Float.d2f b) false)
      else MNoModel
  | _ => MNoModel
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

Definition om (c n d : string) (iface : bool) : methodref :=
  {| mr_class := c; mr_name := n; mr_desc := d; mr_interface := iface |}.

(** An exception made by its no-argument constructor (a null message), e.g. Objects.requireNonNull. *)
Definition throw_nomsg (cls : string) (s : mstate) : model_result :=
  MFrame None (model_code nil nil [New cls; Dup; Invoke InvSpecial (om cls "<init>" "()V" false); Athrow] nil false) nil None s.

Definition throw_msg (cls : string) (msg : list Z) (s : mstate) : model_result :=
  let (l, s') := alloc s (OStr msg) in
  MFrame None (model_code [VRef l] nil
    [New cls; Dup; Load KA 0; Invoke InvSpecial (om cls "<init>" "(Ljava/lang/String;)V" false); Athrow] nil false)
    [VRef l] None s'.

(** A call forwarded to a static helper of a model class: the arguments loaded by kind (a long or
    double takes two local slots), the helper invoked, its result returned. *)
Fixpoint load_args (vs : list value) (i : Z) : list instr :=
  match vs with
  | nil => nil
  | VInt _ :: r => Load KI i :: load_args r (i + 1)
  | VLong _ :: r => Load KL i :: load_args r (i + 2)
  | VFloat _ :: r => Load KF i :: load_args r (i + 1)
  | VDouble _ :: r => Load KD i :: load_args r (i + 2)
  | _ :: r => Load KA i :: load_args r (i + 1)
  end.

Definition forward (cls name desc : string) (ret : option jtype) (args : list value) (s : mstate) : model_result :=
  let rk := match ret with
            | None => None
            | Some (TInt | TBool | TChar | TShort | TByte) => Some KI
            | Some TLong => Some KL | Some TFloat => Some KF | Some TDouble => Some KD
            | Some _ => Some KA
            end in
  MFrame None (model_code args nil (app (load_args args 0) [Invoke InvStatic (om cls name desc false)])
                 [Return rk] false) args ret s.

(** The StringIndexOutOfBoundsException texts of Preconditions (checkIndex / checkFromToIndex). *)
Definition sioobe_index (i n : Z) (s : mstate) : model_result :=
  throw_msg SIOOBE (app (ascii_units "Index ") (app (z_units i) (app (ascii_units " out of bounds for length ") (z_units n)))) s.
Definition sioobe_range (b e n : Z) (s : mstate) : model_result :=
  throw_msg SIOOBE (app (ascii_units "Range [") (app (z_units b) (app (ascii_units ", ") (app (z_units e)
    (app (ascii_units ") out of bounds for length ") (z_units n)))))) s.

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
    (* Character.toUpperCase/toLowerCase per code point with the JDK's special casing (U+00DF ->
       "SS", U+0130 -> "i" U+0307, ...), for a default locale other than tr/az/lt; a GREEK CAPITAL
       LETTER SIGMA to lower case is STUCK (the final sigma needs word boundaries) *)
    match (if String.eqb name "toUpperCase" then Some (upper_units u a) else lower_units u a) with
    | Some r => (* the JDK returns the string itself when no character changes (for toUpperCase:
                   Character.toUpperCaseEx) and none is a surrogate *)
                if units_eqb r a && negb (existsb (fun c => (55296 <=? c) && (c <=? 57343)) a)
                   && negb (String.eqb name "toUpperCase" && existsb (fun c => u_prop u c 11) a) then MOk (Some this) s
                else ret_new s (OStr r)
    | None => MStuckModel "toLowerCase of a string with a capital sigma (final sigma rule)"
    end
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
            | None => MNoModel (* a regular expression: run on the java.util.regex model (string_static) *)
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
  (* charAt first (the same result as its case below): proofs that reduce this model on a
     symbolic string then see only this case *)
  if String.eqb name "charAt" && String.eqb desc "(I)C" then
    match str_of s this with
    | None => MNoModel
    | Some a => match rest with
                | [VInt i] => match char_at a i with inr c => ret_int s c | inl _ => sioobe_index i (slen a) s end
                | _ => MStuckModel "charAt args"
                end
    end
  else
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
      | [VInt i] => match char_at a i with inr c => ret_int s c | inl _ => sioobe_index i (slen a) s end
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
    else if String.eqb key "substring(I)Ljava/lang/String;" || String.eqb key "substring(II)Ljava/lang/String;"
            || String.eqb key "subSequence(II)Ljava/lang/CharSequence;" then
      let be := match rest with
                | [VInt b] => Some (b, slen a)
                | [VInt b; VInt e] => Some (b, e)
                | _ => None
                end in
      match be with
      | None => MStuckModel "substring args"
      | Some (b, en) =>
        match substring2 a b en with
        | inl _ => sioobe_range b en (slen a) s
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

(** [new NullPointerException(<local 1 or null>)]; throw it. *)
Definition npe_code (vs : list value) (msg_local : option Z) : code :=
  model_code vs nil
    (New NPE :: Dup :: (match msg_local with Some i => Load KA i | None => AconstNull end) ::
     [Invoke InvSpecial (om NPE "<init>" "(Ljava/lang/String;)V" false); Athrow]) nil false.

(** Throw a new exception of class [cls] with this message (its (String) constructor, run as bytecode). *)
(** static String.valueOf(...) *)
Definition string_static (name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := name ++ desc in
  if String.eqb key "join(Ljava/lang/CharSequence;[Ljava/lang/CharSequence;)Ljava/lang/String;" then string_join s args else
  (* String.format(fmt, args) and fmt.formatted(args): new java.util.Formatter().format(fmt, args).toString(),
     run as bytecode on the model class harness/jdkmodel/src/java/util/Formatter.java *)
  if String.eqb key "format(Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;"
     || String.eqb key "formatted([Ljava/lang/Object;)Ljava/lang/String;" then
    match args with
    | [f; a] =>
        let fm := fun n d => {| mr_class := "java/util/Formatter"; mr_name := n; mr_desc := d; mr_interface := false |} in
        MFrame None (model_code [f; a] nil
          [New "java/util/Formatter"; Dup; Invoke InvSpecial (fm "<init>" "()V");
           Load KA 0; Load KA 1;
           Invoke InvVirtual (fm "format" "(Ljava/lang/String;[Ljava/lang/Object;)Ljava/util/Formatter;");
           Invoke InvVirtual (fm "toString" "()Ljava/lang/String;")]
          [Return (Some KA)] false) [f; a] (Some (TRef "java/lang/String")) s
    | _ => MStuckModel "format args"
    end else
  (* String.format(Locale, fmt, args): Locale.formatCheck$ admits the locales that format as the
     model Formatter does (null, ROOT, en, en_US/GB/CA), else STUCK *)
  if String.eqb key "format(Ljava/util/Locale;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/String;" then
    match args with
    | [lc; f; a] =>
        let fm := fun n d => {| mr_class := "java/util/Formatter"; mr_name := n; mr_desc := d; mr_interface := false |} in
        MFrame None (model_code [lc; f; a] nil
          [Load KA 0; Invoke InvStatic (om "java/util/Locale" "formatCheck$" "(Ljava/util/Locale;)V" false);
           New "java/util/Formatter"; Dup; Invoke InvSpecial (fm "<init>" "()V");
           Load KA 1; Load KA 2;
           Invoke InvVirtual (fm "format" "(Ljava/lang/String;[Ljava/lang/Object;)Ljava/util/Formatter;");
           Invoke InvVirtual (fm "toString" "()Ljava/lang/String;")]
          [Return (Some KA)] false) [lc; f; a] (Some (TRef "java/lang/String")) s
    | _ => MStuckModel "format args"
    end else
  (* methods written in Java on the modelled natives (java.lang.ModelStrings) *)
  let ms := fun (h d : string) (r : option jtype) => forward "java/lang/ModelStrings" h d r args s in
  (* codePointAt / codePointBefore: checkIndex(index, length) (the index - 1 for codePointBefore) *)
  if String.eqb key "codePointAt(I)I" || String.eqb key "codePointBefore(I)I" then
    match args with
    | [this; VInt i] =>
        match str_of s this with
        | None => MStuckModel "codePointAt"
        | Some u =>
            let n := slen u in
            if String.eqb name "codePointAt" then
              if (0 <=? i) && (i <? n) then
                match nth_unit u i, nth_unit u (i + 1) with
                | Some h, Some lo => if is_high_surrogate h && is_low_surrogate lo
                                     then ret_int s ((h - 55296) * 1024 + (lo - 56320) + 65536) else ret_int s h
                | Some h, None => ret_int s h
                | _, _ => MStuckModel "codePointAt"
                end
              else sioobe_index i n s
            else
              if (1 <=? i) && (i <=? n) then
                match nth_unit u (i - 1), nth_unit u (i - 2) with
                | Some lo, Some h => if is_low_surrogate lo && is_high_surrogate h && (2 <=? i)
                                     then ret_int s ((h - 55296) * 1024 + (lo - 56320) + 65536) else ret_int s lo
                | Some lo, None => ret_int s lo
                | _, _ => MStuckModel "codePointBefore"
                end
              else sioobe_index (i - 1) n s
        end
    | _ => MStuckModel "codePointAt"
    end
  else if String.eqb key "getChars(II[CI)V" then ms "getChars$" "(Ljava/lang/String;II[CI)V" None
  else if String.eqb key "regionMatches(ILjava/lang/String;II)Z" then ms "regionMatches$" "(Ljava/lang/String;ILjava/lang/String;II)Z" (Some TBool)
  else if String.eqb key "regionMatches(ZILjava/lang/String;II)Z" then ms "regionMatchesCI$" "(Ljava/lang/String;ZILjava/lang/String;II)Z" (Some TBool)
  else if String.eqb key "contentEquals(Ljava/lang/CharSequence;)Z" then ms "contentEquals$" "(Ljava/lang/String;Ljava/lang/CharSequence;)Z" (Some TBool)
  else if String.eqb key "contentEquals(Ljava/lang/StringBuffer;)Z" then ms "contentEqualsSb$" "(Ljava/lang/String;Ljava/lang/StringBuffer;)Z" (Some TBool)
  else if String.eqb key "codePointCount(II)I" then ms "codePointCount$" "(Ljava/lang/String;II)I" (Some TInt)
  else if String.eqb key "offsetByCodePoints(II)I" then ms "offsetByCodePoints$" "(Ljava/lang/CharSequence;II)I" (Some TInt)
  else if String.eqb key "chars()Ljava/util/stream/IntStream;" then ms "chars$" "(Ljava/lang/CharSequence;)Ljava/util/stream/IntStream;" (Some (TRef "java/util/stream/IntStream"))
  else if String.eqb key "codePoints()Ljava/util/stream/IntStream;" then ms "codePoints$" "(Ljava/lang/String;)Ljava/util/stream/IntStream;" (Some (TRef "java/util/stream/IntStream"))
  else if String.eqb key "lines()Ljava/util/stream/Stream;" then ms "lines$" "(Ljava/lang/String;)Ljava/util/stream/Stream;" (Some (TRef "java/util/stream/Stream"))
  else if String.eqb key "transform(Ljava/util/function/Function;)Ljava/lang/Object;" then
    ms "transform$" "(Ljava/lang/String;Ljava/util/function/Function;)Ljava/lang/Object;" (Some (TRef "java/lang/Object"))
  else
  (* toLowerCase(Locale) / toUpperCase(Locale): Locale.caseCheck$ (null: NullPointerException; the
     tr/az/lt rules: STUCK), then the locale-independent mapping *)
  if String.eqb key "toLowerCase(Ljava/util/Locale;)Ljava/lang/String;" || String.eqb key "toUpperCase(Ljava/util/Locale;)Ljava/lang/String;" then
    match args with
    | [this; lc] =>
        MFrame None (model_code [this; lc] nil
          [Load KA 1; Invoke InvStatic (om "java/util/Locale" "caseCheck$" "(Ljava/util/Locale;)V" false);
           Load KA 0; Invoke InvVirtual (om "java/lang/String" name "()Ljava/lang/String;" false)]
          [Return (Some KA)] false) [this; lc] (Some (TRef "java/lang/String")) s
    | _ => MStuckModel "case mapping args"
    end else
  (* regular expressions, as the JDK defines them: s.matches(r) = Pattern.matches(r, s),
     s.replaceAll(r, x) = Pattern.compile(r).matcher(s).replaceAll(x) (and replaceFirst),
     s.split(r, n) = Pattern.compile(r).split(s, n) (the one-character fast path is modelled
     directly in string_model2); run as bytecode on harness/jdkmodel/src/java/util/regex *)
  let pm := fun n d => {| mr_class := "java/util/regex/Pattern"; mr_name := n; mr_desc := d; mr_interface := false |} in
  let mm := fun n d => {| mr_class := "java/util/regex/Matcher"; mr_name := n; mr_desc := d; mr_interface := false |} in
  let compile := Invoke InvStatic (pm "compile" "(Ljava/lang/String;)Ljava/util/regex/Pattern;") in
  if String.eqb key "matches(Ljava/lang/String;)Z" then
    match args with
    | [this; r] =>
        MFrame None (model_code [this; r] nil
          [Load KA 1; Load KA 0; Invoke InvStatic (pm "matches" "(Ljava/lang/String;Ljava/lang/CharSequence;)Z")]
          [Return (Some KI)] false) [this; r] (Some TBool) s
    | _ => MStuckModel "matches args"
    end else
  if String.eqb key "replaceAll(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;"
     || String.eqb key "replaceFirst(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;" then
    match args with
    | [this; r; x] =>
        MFrame None (model_code [this; r; x] nil
          [Load KA 1; compile; Load KA 0;
           Invoke InvVirtual (pm "matcher" "(Ljava/lang/CharSequence;)Ljava/util/regex/Matcher;");
           Load KA 2; Invoke InvVirtual (mm name "(Ljava/lang/String;)Ljava/lang/String;")]
          [Return (Some KA)] false) [this; r; x] (Some (TRef "java/lang/String")) s
    | _ => MStuckModel "replaceAll args"
    end else
  if String.eqb key "split(Ljava/lang/String;)[Ljava/lang/String;" || String.eqb key "split(Ljava/lang/String;I)[Ljava/lang/String;" then
    match args with
    | this :: r :: lim =>
        let ld := match lim with [VInt _] => Load KI 2 | _ => Iconst 0 end in
        MFrame None (model_code args nil
          [Load KA 1; compile; Load KA 0; ld;
           Invoke InvVirtual (pm "split" "(Ljava/lang/CharSequence;I)[Ljava/lang/String;")]
          [Return (Some KA)] false) args (Some (TArr (TRef "java/lang/String"))) s
    | _ => MStuckModel "split args"
    end else
  (* String constructors (the object made by [new java/lang/String] becomes a String) *)
  let init_units := fun (this : value) (u : list Z) =>
    match this with VRef l => MOk None (set_heap s l (OStr u)) | _ => MStuckModel "String.<init> receiver" end in
  let chars_of := fun (v : value) => match v with
                                     | VRef l => match ms_heap s l with Some (OArr TChar es) => Some es | _ => None end
                                     | _ => None end in
  let units_of_chars := fun (es : list value) => map (fun v => match v with VInt c => c | _ => 0 end) es in
  let range_fail := fun (o n len : Z) =>
    throw_msg "java/lang/StringIndexOutOfBoundsException"
      (app (ascii_units "Range [") (app (z_units o) (app (ascii_units ", ") (app (z_units o) (app (ascii_units " + ")
        (app (z_units n) (app (ascii_units ") out of bounds for length ") (z_units len)))))))) s in
  let npe_msg := fun (m : string) => let (ml, s') := alloc s (OStr (ascii_units m)) in
                                     MFrame None (npe_code [VNull; VRef ml] (Some 1)) [VNull; VRef ml] None s' in
  let sub_chars := fun (es : list value) (o n : Z) => units_of_chars (firstn (Z.to_nat n) (skipn (Z.to_nat o) es)) in
  (* the byte[] constructors and getBytes: java.nio.charset.Charset's helpers, run as bytecode *)
  let loads := fun (vs : list value) =>
    (fix go (vs : list value) (i : Z) : list instr :=
       match vs with
       | nil => nil
       | VInt _ :: r => Load KI i :: go r (i + 1)
       | _ :: r => Load KA i :: go r (i + 1)
       end) vs 0 in
  let params := fun (d : string) => match index 0 ")" d with Some k => substring 1 (k - 1) d | None => "" end in
  let csm := fun n d => {| mr_class := "java/nio/charset/Charset"; mr_name := n; mr_desc := d; mr_interface := false |} in
  if String.eqb name "<init>" then
    match args with
    | this :: rest =>
      if String.eqb desc "()V" then init_units this nil
      else if String.eqb desc "(Ljava/lang/String;)V" then
        match rest with
        | [VNull] => npe_msg "Cannot read field ""value"" because ""original"" is null"
        | [v] => match str_of s v with Some u => init_units this u | None => MStuckModel "String(String)" end
        | _ => MStuckModel "String(String)"
        end
      else if String.eqb desc "(Ljava/lang/StringBuffer;)V" then
        (* String(StringBuffer buffer) = this(buffer.toString()) *)
        match rest with
        | [VNull] => npe_msg "Cannot invoke ""java.lang.StringBuffer.toString()"" because ""buffer"" is null"
        | [v] => MFrame None (model_code [this; v] nil
                   [Load KA 0; Load KA 1;
                    Invoke InvVirtual (om "java/lang/StringBuffer" "toString" "()Ljava/lang/String;" false);
                    Invoke InvSpecial (om "java/lang/String" "<init>" "(Ljava/lang/String;)V" false)]
                   [Return None] false) [this; v] None s
        | _ => MStuckModel "String(StringBuffer)"
        end
      else if String.eqb desc "(Ljava/lang/StringBuilder;)V" then
        match rest with
        | [VNull] => npe_msg "Cannot invoke ""java.lang.AbstractStringBuilder.getValue()"" because ""asb"" is null"
        | [VRef b] => match ms_heap s b with Some (OSb u) => init_units this u | _ => MStuckModel "String(StringBuilder)" end
        | _ => MStuckModel "String(StringBuilder)"
        end
      else if String.eqb desc "([C)V" then
        match rest with
        | [VNull] => npe_msg "Cannot read the array length because ""value"" is null"
        | [v] => match chars_of v with Some es => init_units this (units_of_chars es) | None => MStuckModel "String(char[])" end
        | _ => MStuckModel "String(char[])"
        end
      else if String.eqb desc "([CII)V" then
        match rest with
        | [VNull; _; _] => npe_msg "Cannot read the array length because ""value"" is null"
        | [v; VInt o; VInt n] =>
            match chars_of v with
            | Some es => let len := slen_v es in
                         if (o <? 0) || (n <? 0) || (len - o <? n) then range_fail o n len
                         else init_units this (sub_chars es o n)
            | None => MStuckModel "String(char[], int, int)"
            end
        | _ => MStuckModel "String(char[], int, int)"
        end
      else if prefix "([B" desc then
        MFrame None (model_code args nil
          (app (loads args)
            [Invoke InvStatic (csm "newString$" ("(" ++ params desc ++ ")Ljava/lang/String;"));
             Invoke InvSpecial {| mr_class := "java/lang/String"; mr_name := "<init>"; mr_desc := "(Ljava/lang/String;)V"; mr_interface := false |}])
          [Return None] false) args None s
      else MNoModel
    | nil => MNoModel
    end
  else if String.eqb name "getBytes" && (String.eqb desc "()[B" || String.eqb desc "(Ljava/nio/charset/Charset;)[B"
                                         || String.eqb desc "(Ljava/lang/String;)[B") then
    MFrame None (model_code args nil
      (app (loads args) [Invoke InvStatic (csm "getBytes$" ("(Ljava/lang/String;" ++ params desc ++ ")[B"))])
      [Return (Some KA)] false) args (Some (TArr TByte)) s
  else if String.eqb key "valueOf([C)Ljava/lang/String;" || String.eqb key "copyValueOf([C)Ljava/lang/String;" then
    match args with
    | [VNull] => npe_msg "Cannot read the array length because ""value"" is null"
    | [v] => match chars_of v with Some es => ret_new s (OStr (units_of_chars es)) | None => MStuckModel "valueOf(char[])" end
    | _ => MStuckModel "valueOf(char[])"
    end
  else if String.eqb key "valueOf([CII)Ljava/lang/String;" || String.eqb key "copyValueOf([CII)Ljava/lang/String;" then
    match args with
    | [VNull; _; _] => npe_msg "Cannot read the array length because ""value"" is null"
    | [v; VInt o; VInt n] =>
        match chars_of v with
        | Some es => let len := slen_v es in
                     if (o <? 0) || (n <? 0) || (len - o <? n) then range_fail o n len
                     else ret_new s (OStr (sub_chars es o n))
        | None => MStuckModel "valueOf(char[], int, int)"
        end
    | _ => MStuckModel "valueOf(char[], int, int)"
    end
  else if String.eqb key "valueOf(I)Ljava/lang/String;" then
    match args with [VInt z] => ret_new s (OStr (z_units z)) | _ => MStuckModel "valueOf" end
  else if String.eqb key "valueOf(J)Ljava/lang/String;" then
    match args with [VLong z] => ret_new s (OStr (z_units z)) | _ => MStuckModel "valueOf" end
  else if String.eqb key "valueOf(D)Ljava/lang/String;" then
    match args with [VDouble b] => match FloatDec.dtoa b with Some u => ret_new s (OStr u) | None => MStuckModel "valueOf" end
               | _ => MStuckModel "valueOf" end
  else if String.eqb key "valueOf(F)Ljava/lang/String;" then
    match args with [VFloat b] => match FloatDec.ftoa b with Some u => ret_new s (OStr u) | None => MStuckModel "valueOf" end
               | _ => MStuckModel "valueOf" end
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
    match v with
    | VNull => Some null_units
    | VRef l => match ms_heap s l with Some (OStr u) => Some u | Some (OSb u) => Some u | _ => None end
    | _ => None
    end
  else match v with
       | VInt z => if String.eqb t "(I)Ljava/lang/StringBuilder;" then Some (z_units z)
                   else if String.eqb t "(C)Ljava/lang/StringBuilder;" then Some [z]
                   else if String.eqb t "(Z)Ljava/lang/StringBuilder;" then Some (bool_units (negb (z =? 0)))
                   else None
       | VLong z => if String.eqb t "(J)Ljava/lang/StringBuilder;" then Some (z_units z) else None
       | VDouble b => if String.eqb t "(D)Ljava/lang/StringBuilder;" then FloatDec.dtoa b else None
       | VFloat b => if String.eqb t "(F)Ljava/lang/StringBuilder;" then FloatDec.ftoa b else None
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
      else if String.eqb desc "(Ljava/lang/CharSequence;)V" then
        (* AbstractStringBuilder(CharSequence seq): seq.length(), then append(seq) *)
        match rest with
        | [VNull] => throw_msg NPE (ascii_units "Cannot invoke ""java.lang.CharSequence.length()"" because ""seq"" is null") s
        | [VRef r] => match ms_heap s r with
                      | Some (OStr u) | Some (OSb u) => MOk None (set_heap s l (OSb u))
                      | Some (OObj c _) =>
                          if String.eqb c "java/lang/StringBuffer" then
                            MFrame None (model_code [this; VRef r] nil
                              [Load KA 0; Invoke InvSpecial (om "java/lang/StringBuilder" "<init>" "()V" false);
                               Load KA 0; Load KA 1;
                               Invoke InvVirtual (om "java/lang/StringBuffer" "toString" "()Ljava/lang/String;" false);
                               Invoke InvVirtual (om "java/lang/StringBuilder" "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;" false);
                               Pop] [Return None] false) [this; VRef r] None s
                          else MStuckModel "StringBuilder(CharSequence): a user CharSequence (length/charAt callbacks)"
                      | _ => MStuckModel "StringBuilder(CharSequence)"
                      end
        | _ => MStuckModel "StringBuilder(CharSequence)"
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
                   if String.eqb desc "(Ljava/lang/StringBuffer;)Ljava/lang/StringBuilder;"
                      || (String.eqb desc "(Ljava/lang/CharSequence;)Ljava/lang/StringBuilder;"
                          && match v with VRef r => match ms_heap s r with Some (OObj c _) => String.eqb c "java/lang/StringBuffer" | _ => false end | _ => false end) then
                     (* the contents of a StringBuffer (its synchronized toString()) *)
                     match v with
                     | VNull => MOk (Some this) (set_heap s l (OSb (app u null_units)))
                     | _ => MFrame None (model_code [this; v] nil
                              [Load KA 0; Load KA 1;
                               Invoke InvVirtual (om "java/lang/StringBuffer" "toString" "()Ljava/lang/String;" false);
                               Invoke InvVirtual (om "java/lang/StringBuilder" "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;" false)]
                              [Return (Some KA)] false) [this; v] (Some (TRef "java/lang/StringBuilder")) s
                     end
                   else if String.eqb desc "(Ljava/lang/Object;)Ljava/lang/StringBuilder;" then
                     (* append(String.valueOf(obj)): toString() runs as bytecode *)
                     MFrame None (model_code [this; v] nil
                       [Load KA 0; Load KA 1;
                        Invoke InvStatic {| mr_class := "java/lang/String"; mr_name := "valueOf";
                                            mr_desc := "(Ljava/lang/Object;)Ljava/lang/String;"; mr_interface := false |};
                        Invoke InvVirtual {| mr_class := "java/lang/StringBuilder"; mr_name := "append";
                                             mr_desc := "(Ljava/lang/String;)Ljava/lang/StringBuilder;"; mr_interface := false |}]
                       [Return (Some KA)] false) [this; v] (Some (TRef "java/lang/StringBuilder")) s
                   else if String.eqb desc "([C)Ljava/lang/StringBuilder;" then
                     match v with
                     | VNull => throw_msg NPE (ascii_units "Cannot read the array length because ""str"" is null") s
                     | VRef r => match ms_heap s r with
                                  | Some (OArr TChar es) => MOk (Some this) (set_heap s l (OSb (app u (map (fun x => match x with VInt c => c | _ => 0 end) es))))
                                  | _ => MStuckModel "append(char[])"
                                  end
                     | _ => MStuckModel "append(char[])"
                     end
                   else MStuckModel ("StringBuilder.append" ++ desc ++ ": not modelled for this argument")
               end
      | [v; VInt st; VInt en] =>
          (* append(CharSequence, start, end) ("null" for null) and append(char[], offset, len):
             Preconditions.checkFromToIndex(start, end, length) with IOOBE_FORMATTER *)
          let rng := fun (w : list Z) (a b : Z) =>
            if (a <? 0) || (b <? a) || (slen w <? b) then
              throw_msg "java/lang/IndexOutOfBoundsException"
                (app (ascii_units "Range [") (app (z_units a) (app (ascii_units ", ") (app (z_units b)
                  (app (ascii_units ") out of bounds for length ") (z_units (slen w))))))) s
            else MOk (Some this) (set_heap s l (OSb (app u (firstn (Z.to_nat (b - a)) (skipn (Z.to_nat a) w))))) in
          if String.eqb desc "(Ljava/lang/CharSequence;II)Ljava/lang/StringBuilder;" then
            match v with
            | VNull => rng null_units st en
            | VRef r => match ms_heap s r with
                        | Some (OStr w) | Some (OSb w) => rng w st en
                        | _ => MStuckModel "append(CharSequence,int,int): argument needs charAt()"
                        end
            | _ => MStuckModel "append(CharSequence,int,int)"
            end
          else if String.eqb desc "([CII)Ljava/lang/StringBuilder;" then
            match v with
            | VNull => let (ml, s') := alloc s (OStr (ascii_units "Cannot read the array length because ""str"" is null")) in
                       MFrame None (npe_code [VNull; VRef ml] (Some 1)) [VNull; VRef ml] None s'
            | VRef r => match ms_heap s r with
                        | Some (OArr TChar es) => rng (map (fun x => match x with VInt c => c | _ => 0 end) es) st (signed 32 ((st + en) mod 2 ^ 32))
                        | _ => MStuckModel "append(char[],int,int)"
                        end
            | _ => MStuckModel "append(char[],int,int)"
            end
          else MStuckModel "append args"
      | _ => MStuckModel "append args"
      end
    else if String.eqb name "toString" && String.eqb desc "()Ljava/lang/String;" then ret_new s (OStr u)
    else if String.eqb name "length" && String.eqb desc "()I" then ret_int s (slen u)
    else if (String.eqb name "indexOf" || String.eqb name "lastIndexOf")
            && (String.eqb desc "(Ljava/lang/String;)I" || String.eqb desc "(Ljava/lang/String;I)I") then
      (* AbstractStringBuilder.indexOf/lastIndexOf: String.indexOf/lastIndexOf on the contents *)
      match rest with
      | VNull :: _ => MThrow NPE
      | v :: more =>
          match str_of s v, more with
          | Some b, nil => ret_int s (if String.eqb name "indexOf" then index_of_str u b 0 else last_index_of_str u b (slen u))
          | Some b, [VInt i] => ret_int s (if String.eqb name "indexOf" then index_of_str u b i else last_index_of_str u b i)
          | _, _ => MStuckModel "StringBuilder.indexOf"
          end
      | nil => MStuckModel "StringBuilder.indexOf"
      end
    else if String.eqb name "charAt" && String.eqb desc "(I)C" then
      match rest with
      | [VInt i] => match char_at u i with inr c => ret_int s c | inl _ => sioobe_index i (slen u) s end
      | _ => MStuckModel "charAt"
      end
    else if String.eqb name "setLength" && String.eqb desc "(I)V" then
      match rest with
      | [VInt n] => if n <? 0 then throw_msg SIOOBE (app (ascii_units "String index out of range: ") (z_units n)) s
                    else MOk None (set_heap s l (OSb (if n <=? slen u then firstn (Z.to_nat n) u
                                                      else app u (repeat 0 (Z.to_nat (n - slen u))))))
      | _ => MStuckModel "setLength"
      end
    else if String.eqb name "deleteCharAt" && String.eqb desc "(I)Ljava/lang/StringBuilder;" then
      match rest with
      | [VInt i] => if (i <? 0) || (slen u <=? i) then sioobe_index i (slen u) s
                    else MOk (Some this) (set_heap s l (OSb (app (firstn (Z.to_nat i) u) (skipn (Z.to_nat (i + 1)) u))))
      | _ => MStuckModel "deleteCharAt"
      end
    else if String.eqb name "insert" then
      (* AbstractStringBuilder.insert(offset, x): checkOffset (Preconditions.checkFromToIndex(offset,
         count, count)), String.valueOf(x) for the primitives and objects *)
      let off_fail := fun (i : Z) => throw_msg SIOOBE
        (app (ascii_units "Range [") (app (z_units i) (app (ascii_units ", ") (app (z_units (slen u))
          (app (ascii_units ") out of bounds for length ") (z_units (slen u))))))) s in
      let ins := fun (i : Z) (w : list Z) =>
        if (i <? 0) || (slen u <? i) then off_fail i
        else MOk (Some this) (set_heap s l (OSb (app (firstn (Z.to_nat i) u) (app w (skipn (Z.to_nat i) u))))) in
      match rest with
      | [VInt i; v] =>
          let t := desc in
          if String.eqb t "(ILjava/lang/String;)Ljava/lang/StringBuilder;"
             || String.eqb t "(ILjava/lang/CharSequence;)Ljava/lang/StringBuilder;"
             || String.eqb t "(ILjava/lang/Object;)Ljava/lang/StringBuilder;" then
            match v with
            | VNull => ins i null_units
            | _ => match str_of s v with
                   | Some w => ins i w
                   | None => match v with
                             | VRef r => match option_bind (ms_heap s r) box_string with
                                         | Some w => ins i w
                                         | None => MStuckModel "insert: argument needs toString()"
                                         end
                             | _ => MStuckModel "insert"
                             end
                   end
            end
          else if String.eqb t "(I[C)Ljava/lang/StringBuilder;" then
            if (i <? 0) || (slen u <? i) then off_fail i else
            match v with
            | VNull => let (ml, s') := alloc s (OStr (ascii_units "Cannot read the array length because ""str"" is null")) in
                       MFrame None (npe_code [VNull; VRef ml] (Some 1)) [VNull; VRef ml] None s'
            | VRef r => match ms_heap s r with
                        | Some (OArr TChar es) => ins i (map (fun x => match x with VInt c => c | _ => 0 end) es)
                        | _ => MStuckModel "insert(char[])"
                        end
            | _ => MStuckModel "insert(char[])"
            end
          else
            match v with
            | VInt z => if String.eqb t "(IC)Ljava/lang/StringBuilder;" then ins i [z]
                        else if String.eqb t "(II)Ljava/lang/StringBuilder;" then ins i (z_units z)
                        else if String.eqb t "(IZ)Ljava/lang/StringBuilder;" then ins i (bool_units (negb (z =? 0)))
                        else MStuckModel "insert"
            | VLong z => ins i (z_units z)
            | VDouble b => match FloatDec.dtoa b with Some w => ins i w | None => MStuckModel "insert" end
            | VFloat b => match FloatDec.ftoa b with Some w => ins i w | None => MStuckModel "insert" end
            | _ => MStuckModel "insert"
            end
      | _ => MStuckModel "insert"
      end
    else
    (* AbstractStringBuilder (JDK 21): delete/replace clamp end to the length, then
       checkFromToIndex(start, end, count); setCharAt/codePointAt checkIndex; reverse keeps surrogate
       pairs; substring of nothing is the literal "" *)
    let n := slen u in
    let setu := fun (w : list Z) => MOk (Some this) (set_heap s l (OSb w)) in
    let rng_ok := fun (b e : Z) => (0 <=? b) && (b <=? e) && (e <=? n) in
    if String.eqb name "delete" && String.eqb desc "(II)Ljava/lang/StringBuilder;" then
      match rest with
      | [VInt b; VInt e] => let e := Z.min e n in
                            if rng_ok b e then setu (app (firstn (Z.to_nat b) u) (skipn (Z.to_nat e) u)) else sioobe_range b e n s
      | _ => MStuckModel "delete"
      end
    else if String.eqb name "replace" && String.eqb desc "(IILjava/lang/String;)Ljava/lang/StringBuilder;" then
      match rest with
      | [VInt b; VInt e; v] =>
          let e := Z.min e n in
          if negb (rng_ok b e) then sioobe_range b e n s else
          match v with
          | VNull => throw_msg NPE (ascii_units "Cannot invoke ""String.length()"" because ""str"" is null") s
          | _ => match str_of s v with
                 | Some w => setu (app (firstn (Z.to_nat b) u) (app w (skipn (Z.to_nat e) u)))
                 | None => MStuckModel "replace"
                 end
          end
      | _ => MStuckModel "replace"
      end
    else if String.eqb name "setCharAt" && String.eqb desc "(IC)V" then
      match rest with
      | [VInt i; VInt c] => if (0 <=? i) && (i <? n)
                            then MOk None (set_heap s l (OSb (app (firstn (Z.to_nat i) u) (c :: skipn (Z.to_nat (i + 1)) u))))
                            else sioobe_index i n s
      | _ => MStuckModel "setCharAt"
      end
    else if String.eqb name "reverse" && String.eqb desc "()Ljava/lang/StringBuilder;" then
      let fix fixp (w : list Z) : list Z :=
        match w with
        | a :: ((b :: t) as r) => if is_low_surrogate a && is_high_surrogate b then b :: a :: fixp t else a :: fixp r
        | _ => w
        end in
      setu (fixp (rev u))
    else if (String.eqb name "substring" && (String.eqb desc "(I)Ljava/lang/String;" || String.eqb desc "(II)Ljava/lang/String;"))
            || (String.eqb name "subSequence" && String.eqb desc "(II)Ljava/lang/CharSequence;") then
      let be := match rest with [VInt b] => Some (b, n) | [VInt b; VInt e] => Some (b, e) | _ => None end in
      match be with
      | Some (b, e) => if rng_ok b e then
                         (if b =? e then ret_lit s nil else ret_new s (OStr (firstn (Z.to_nat (e - b)) (skipn (Z.to_nat b) u))))
                       else sioobe_range b e n s
      | None => MStuckModel "substring"
      end
    else if String.eqb name "appendCodePoint" && String.eqb desc "(I)Ljava/lang/StringBuilder;" then
      match rest with
      | [VInt c] =>
          if (0 <=? c) && (c <? 65536) then setu (app u [c])
          else if (65536 <=? c) && (c <=? 1114111) then
            setu (app u [Z.shiftr (c - 65536) 10 + 55296; Z.land (c - 65536) 1023 + 56320])
          else throw_msg IAE (app (ascii_units "Not a valid Unicode code point: 0x")
                                  (map (fun d => if (97 <=? d) && (d <=? 102) then d - 32 else d)
                                    (match FloatDec.drop_lead_zeros (FloatDec.hex_digits 8 (c mod 2 ^ 32) nil) with nil => [48] | w => w end))) s
      | _ => MStuckModel "appendCodePoint"
      end
    else if String.eqb name "codePointAt" && String.eqb desc "(I)I" then
      match rest with
      | [VInt i] => if (0 <=? i) && (i <? n) then
                      match nth_unit u i, nth_unit u (i + 1) with
                      | Some h, Some lo => if is_high_surrogate h && is_low_surrogate lo
                                           then ret_int s ((h - 55296) * 1024 + (lo - 56320) + 65536) else ret_int s h
                      | Some h, None => ret_int s h
                      | _, _ => MStuckModel "codePointAt"
                      end
                    else sioobe_index i n s
      | _ => MStuckModel "codePointAt"
      end
    else if String.eqb name "codePointBefore" && String.eqb desc "(I)I" then
      match rest with
      | [VInt i] => if (1 <=? i) && (i <=? n) then
                      match nth_unit u (i - 1), nth_unit u (i - 2) with
                      | Some lo, Some h => if is_low_surrogate lo && is_high_surrogate h && (2 <=? i)
                                           then ret_int s ((h - 55296) * 1024 + (lo - 56320) + 65536) else ret_int s lo
                      | Some lo, None => ret_int s lo
                      | _, _ => MStuckModel "codePointBefore"
                      end
                    else sioobe_index (i - 1) n s
      | _ => MStuckModel "codePointBefore"
      end
    else if String.eqb name "isEmpty" && String.eqb desc "()Z" then ret_bool s (n =? 0)
    else if String.eqb name "compareTo" && String.eqb desc "(Ljava/lang/StringBuilder;)I" then
      match rest with
      | [VNull] => throw_msg NPE (ascii_units "Cannot read field ""value"" because ""another"" is null") s
      | [v] => match sb_of s v with Some (_, w) => ret_int s (compare_units u w) | None => MStuckModel "compareTo" end
      | _ => MStuckModel "compareTo"
      end
    else if (String.eqb name "ensureCapacity" && String.eqb desc "(I)V") then
      match rest with [VInt c] => if c <=? MAX_ARRAY then MOk None s else MStuckModel "ensureCapacity beyond the model bound"
                      | _ => MStuckModel "ensureCapacity" end
    else if String.eqb name "trimToSize" && String.eqb desc "()V" then MOk None s
    else if String.eqb name "getChars" && String.eqb desc "(II[CI)V" then
      forward "java/lang/ModelStrings" "sbGetChars$" "(Ljava/lang/StringBuilder;II[CI)V" None args s
    else if String.eqb name "codePointCount" && String.eqb desc "(II)I" then
      forward "java/lang/ModelStrings" "sbCodePointCount$" "(Ljava/lang/StringBuilder;II)I" (Some TInt) args s
    else if String.eqb name "offsetByCodePoints" && String.eqb desc "(II)I" then
      forward "java/lang/ModelStrings" "offsetByCodePoints$" "(Ljava/lang/CharSequence;II)I" (Some TInt) args s
    else if String.eqb name "chars" && String.eqb desc "()Ljava/util/stream/IntStream;" then
      forward "java/lang/ModelStrings" "chars$" "(Ljava/lang/CharSequence;)Ljava/util/stream/IntStream;" (Some (TRef "java/util/stream/IntStream")) args s
    else MNoModel
  end
  end.

(** ** java.lang.Character, Integer, Long, Math *)
Definition char_model (e : jenv) (name desc : string) (args : list value) (s : mstate) : model_result :=
  let u := j_u e in
  let key := name ++ desc in
  match args with
  | [VInt c] =>
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
    else if String.eqb key "isSurrogate(C)Z" then ret_bool s ((55296 <=? c) && (c <=? 57343))
    else if String.eqb key "getType(C)I" || String.eqb key "getType(I)I" then ret_int s (u_type u c)
    else if String.eqb key "getNumericValue(C)I" || String.eqb key "getNumericValue(I)I" then ret_int s (u_numeric u c)
    else if String.eqb key "isJavaIdentifierStart(C)Z" || String.eqb key "isJavaIdentifierStart(I)Z" then ret_bool s (u_prop u c 0)
    else if String.eqb key "isJavaIdentifierPart(C)Z" || String.eqb key "isJavaIdentifierPart(I)Z" then ret_bool s (u_prop u c 1)
    else if String.eqb key "isJavaLetter(C)Z" then ret_bool s (u_prop u c 0)
    else if String.eqb key "isJavaLetterOrDigit(C)Z" then ret_bool s (u_prop u c 1)
    else if String.eqb key "isUnicodeIdentifierStart(C)Z" || String.eqb key "isUnicodeIdentifierStart(I)Z" then ret_bool s (u_prop u c 2)
    else if String.eqb key "isUnicodeIdentifierPart(C)Z" || String.eqb key "isUnicodeIdentifierPart(I)Z" then ret_bool s (u_prop u c 3)
    else if String.eqb key "isIdentifierIgnorable(C)Z" || String.eqb key "isIdentifierIgnorable(I)Z" then ret_bool s (u_prop u c 4)
    else if String.eqb key "isAlphabetic(I)Z" then ret_bool s (u_prop u c 5)
    else if String.eqb key "isIdeographic(I)Z" then ret_bool s (u_prop u c 6)
    else if String.eqb key "isSpaceChar(C)Z" || String.eqb key "isSpaceChar(I)Z" then ret_bool s (u_prop u c 7)
    else if String.eqb key "isTitleCase(C)Z" || String.eqb key "isTitleCase(I)Z" then ret_bool s (u_prop u c 8)
    else if String.eqb key "isDefined(C)Z" || String.eqb key "isDefined(I)Z" then ret_bool s (u_prop u c 9)
    else if String.eqb key "isMirrored(C)Z" || String.eqb key "isMirrored(I)Z" then ret_bool s (u_prop u c 10)
    else if String.eqb key "isISOControl(C)Z" || String.eqb key "isISOControl(I)Z" then
      ret_bool s (((0 <=? c) && (c <=? 31)) || ((127 <=? c) && (c <=? 159)))
    else if String.eqb key "isValidCodePoint(I)Z" then ret_bool s ((0 <=? c) && (c <=? 1114111))
    else if String.eqb key "isBmpCodePoint(I)Z" then ret_bool s ((0 <=? c) && (c <? 65536))
    else if String.eqb key "isSupplementaryCodePoint(I)Z" then ret_bool s ((65536 <=? c) && (c <=? 1114111))
    else if String.eqb key "charCount(I)I" then ret_int s (if 65536 <=? c then 2 else 1)
    else if String.eqb key "highSurrogate(I)C" then ret_int s (i2c (Z.shiftr (c mod 2 ^ 32) 10 + 55232))
    else if String.eqb key "lowSurrogate(I)C" then ret_int s (i2c (Z.land c 1023 + 56320))
    else if String.eqb key "hashCode(C)I" then ret_int s c
    else if String.eqb key "reverseBytes(C)C" then ret_int s (Z.lor (Z.shiftl (Z.land c 255) 8) (Z.shiftr c 8))
    else MNoModel
  | [VInt c; VInt r] =>
    if String.eqb name "digit" && (String.eqb desc "(CI)I" || String.eqb desc "(II)I") then
      (* CharacterData.digit: a decimal digit's value, or 10.. for the Latin letters (ASCII and
         fullwidth), if below the radix *)
      ret_int s (char_digit u c r)
    else if String.eqb key "forDigit(II)C" then
      (* Character.forDigit(digit, radix): '\0' when the digit or the radix is out of range *)
      ret_int s (if (c <? 0) || (r <=? c) || (r <? 2) || (36 <? r) then 0 else if c <? 10 then 48 + c else 87 + c)
    else if String.eqb key "toCodePoint(CC)I" then ret_int s (Z.shiftl c 10 + r - 56613888)
    else if String.eqb key "compare(CC)I" then ret_int s (c - r)
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
  if ((z <? INT_MIN) || (INT_MAX <? z))%Z then throw_msg ARITH (ascii_units "integer overflow") s else ret_int s z.
Definition exact64 (s : mstate) (z : Z) : model_result :=
  if ((z <? LONG_MIN) || (LONG_MAX <? z))%Z then throw_msg ARITH (ascii_units "long overflow") s else MOk (Some (VLong z)) s.

(** The digits of [v] read as an unsigned [bits]-bit number in radix 2^[sh] (lower case). *)
Fixpoint radix_digits (fuel : nat) (sh v : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => let d := Z.land v (2 ^ sh - 1) in
           let c := if d <? 10 then 48 + d else 87 + d in
           let v' := Z.shiftr v sh in
           if v' =? 0 then c :: acc else radix_digits f sh v' (c :: acc)
  end.
Definition unsigned_units (sh bits v : Z) : list Z := radix_digits (Z.to_nat bits) sh (v mod 2 ^ bits) nil.

Definition num_model1 (e : jenv) (key : string) (args : list value) (s : mstate) : model_result :=
  match args with

  | [VInt a] =>
    if String.eqb key "java/lang/Integer.toString(I)Ljava/lang/String;" then ret_new s (OStr (z_units a))
    else if String.eqb key "java/lang/Integer.toHexString(I)Ljava/lang/String;" then ret_new s (OStr (unsigned_units 4 32 a))
    else if String.eqb key "java/lang/Integer.toOctalString(I)Ljava/lang/String;" then ret_new s (OStr (unsigned_units 3 32 a))
    else if String.eqb key "java/lang/Integer.toBinaryString(I)Ljava/lang/String;" then ret_new s (OStr (unsigned_units 1 32 a))
    else if String.eqb key "java/lang/Math.abs(I)I" then ret_int s (wrap32 (Z.abs a))
    else if String.eqb key "java/lang/Integer.signum(I)I" then ret_int s (Z.sgn a)
    else MNoModel
  | [VLong a] =>
    if String.eqb key "java/lang/Long.toString(J)Ljava/lang/String;" then ret_new s (OStr (z_units a))
    else if String.eqb key "java/lang/Long.toHexString(J)Ljava/lang/String;" then ret_new s (OStr (unsigned_units 4 64 a))
    else if String.eqb key "java/lang/Long.toOctalString(J)Ljava/lang/String;" then ret_new s (OStr (unsigned_units 3 64 a))
    else if String.eqb key "java/lang/Long.toBinaryString(J)Ljava/lang/String;" then ret_new s (OStr (unsigned_units 1 64 a))
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
    else if String.eqb key "java/lang/Long.min(JJ)J" then MOk (Some (VLong (Z.min a b))) s
    else if String.eqb key "java/lang/Long.max(JJ)J" then MOk (Some (VLong (Z.max a b))) s
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
    else if String.eqb key "java/lang/Integer.reverse(I)I" then
      let u := unsigned 32 a in
      ret_int s (wrap32 (fold_left (fun acc i => if Z.testbit u i then Z.lor acc (Z.shiftl 1 (31 - i)) else acc) (map Z.of_nat (seq 0 32)) 0))
    else if String.eqb key "java/lang/Integer.reverseBytes(I)I" then
      let u := unsigned 32 a in
      ret_int s (wrap32 (fold_left (fun acc i => Z.lor acc (Z.shiftl (Z.land (Z.shiftr u (8 * i)) 255) (8 * (3 - i)))) (map Z.of_nat (seq 0 4)) 0))
    else if String.eqb key "java/lang/Integer.toUnsignedLong(I)J" then MOk (Some (VLong (unsigned 32 a))) s
    else if String.eqb key "java/lang/Integer.toUnsignedString(I)Ljava/lang/String;" then ret_new s (OStr (z_units (unsigned 32 a)))
    else if String.eqb key "java/lang/Math.negateExact(I)I" then exact32 s (- a)
    else if String.eqb key "java/lang/Math.incrementExact(I)I" then exact32 s (a + 1)
    else if String.eqb key "java/lang/Math.decrementExact(I)I" then exact32 s (a - 1)
    else if String.eqb key "java/lang/Math.absExact(I)I" then
      if a =? INT_MIN then throw_msg ARITH (ascii_units "Overflow to represent absolute value of Integer.MIN_VALUE") s else ret_int s (Z.abs a)
    else MNoModel
  | [VLong a] =>
    if String.eqb key "java/lang/Long.bitCount(J)I" then ret_int s (popcount 80 (unsigned 64 a))
    else if String.eqb key "java/lang/Long.numberOfLeadingZeros(J)I" then ret_int s (nlz 64 a)
    else if String.eqb key "java/lang/Long.numberOfTrailingZeros(J)I" then ret_int s (ntz 64 a)
    else if String.eqb key "java/lang/Long.highestOneBit(J)J" then MOk (Some (VLong (highest 64 a))) s
    else if String.eqb key "java/lang/Long.lowestOneBit(J)J" then MOk (Some (VLong (lowest 64 a))) s
    else if String.eqb key "java/lang/Long.hashCode(J)I" then ret_int s (wrap32 (Z.lxor (unsigned 64 a) (Z.shiftr (unsigned 64 a) 32)))
    else if String.eqb key "java/lang/Long.signum(J)I" then ret_int s (Z.sgn a)
    else if String.eqb key "java/lang/Long.reverse(J)J" then
      let u := unsigned 64 a in
      MOk (Some (VLong (wrap64 (fold_left (fun acc i => if Z.testbit u i then Z.lor acc (Z.shiftl 1 (63 - i)) else acc) (map Z.of_nat (seq 0 64)) 0)))) s
    else if String.eqb key "java/lang/Long.reverseBytes(J)J" then
      let u := unsigned 64 a in
      MOk (Some (VLong (wrap64 (fold_left (fun acc i => Z.lor acc (Z.shiftl (Z.land (Z.shiftr u (8 * i)) 255) (8 * (7 - i)))) (map Z.of_nat (seq 0 8)) 0)))) s
    else if String.eqb key "java/lang/Long.toUnsignedString(J)Ljava/lang/String;" then ret_new s (OStr (z_units (unsigned 64 a)))
    else if String.eqb key "java/lang/Math.toIntExact(J)I" then exact32 s a
    else if String.eqb key "java/lang/Math.negateExact(J)J" then exact64 s (- a)
    else if String.eqb key "java/lang/Math.incrementExact(J)J" then exact64 s (a + 1)
    else if String.eqb key "java/lang/Math.decrementExact(J)J" then exact64 s (a - 1)
    else if String.eqb key "java/lang/Math.absExact(J)J" then
      if a =? LONG_MIN then throw_msg ARITH (ascii_units "Overflow to represent absolute value of Long.MIN_VALUE") s else MOk (Some (VLong (Z.abs a))) s
    else MNoModel
  | [VInt a; VInt b] =>
    if String.eqb key "java/lang/Math.floorMod(II)I" then if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else ret_int s (Z.modulo a b)
    else if String.eqb key "java/lang/Math.floorDiv(II)I" then if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else ret_int s (wrap32 (Z.div a b))
    else if String.eqb key "java/lang/Math.addExact(II)I" then exact32 s (a + b)
    else if String.eqb key "java/lang/Math.subtractExact(II)I" then exact32 s (a - b)
    else if String.eqb key "java/lang/Math.multiplyExact(II)I" then exact32 s (a * b)
    else if String.eqb key "java/lang/Integer.sum(II)I" then ret_int s (wrap32 (a + b))
    else if String.eqb key "java/lang/Integer.compareUnsigned(II)I" then ret_int s (lcmp (unsigned 32 a) (unsigned 32 b))
    else if String.eqb key "java/lang/Integer.divideUnsigned(II)I" then
      if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else ret_int s (wrap32 (unsigned 32 a / unsigned 32 b))
    else if String.eqb key "java/lang/Integer.remainderUnsigned(II)I" then
      if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else ret_int s (wrap32 (unsigned 32 a mod unsigned 32 b))
    else if String.eqb key "java/lang/Integer.rotateLeft(II)I" then
      let u := unsigned 32 a in let k := Z.modulo b 32 in ret_int s (wrap32 (Z.lor (Z.shiftl u k) (Z.shiftr u (32 - k))))
    else if String.eqb key "java/lang/Integer.rotateRight(II)I" then
      let u := unsigned 32 a in let k := Z.modulo b 32 in ret_int s (wrap32 (Z.lor (Z.shiftr u k) (Z.shiftl u (32 - k))))
    else MNoModel
  | [VLong a; VLong b] =>
    if String.eqb key "java/lang/Math.floorMod(JJ)J" then if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else MOk (Some (VLong (Z.modulo a b))) s
    else if String.eqb key "java/lang/Math.floorDiv(JJ)J" then if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else MOk (Some (VLong (wrap64 (Z.div a b)))) s
    else if String.eqb key "java/lang/Long.compareUnsigned(JJ)I" then ret_int s (lcmp (unsigned 64 a) (unsigned 64 b))
    else if String.eqb key "java/lang/Long.divideUnsigned(JJ)J" then
      if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else MOk (Some (VLong (wrap64 (unsigned 64 a / unsigned 64 b)))) s
    else if String.eqb key "java/lang/Long.remainderUnsigned(JJ)J" then
      if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else MOk (Some (VLong (wrap64 (unsigned 64 a mod unsigned 64 b)))) s
    else if String.eqb key "java/lang/Math.addExact(JJ)J" then exact64 s (a + b)
    else if String.eqb key "java/lang/Math.subtractExact(JJ)J" then exact64 s (a - b)
    else if String.eqb key "java/lang/Math.multiplyExact(JJ)J" then exact64 s (a * b)
    else if String.eqb key "java/lang/Long.sum(JJ)J" then MOk (Some (VLong (wrap64 (a + b)))) s
    else MNoModel
  | [VLong a; VInt b] =>
    if String.eqb key "java/lang/Math.floorMod(JI)I" then if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else ret_int s (Z.modulo a b)
    else if String.eqb key "java/lang/Math.floorDiv(JI)J" then if (b =? 0)%Z then throw_msg ARITH (ascii_units "/ by zero") s else MOk (Some (VLong (wrap64 (Z.div a b)))) s
    else if String.eqb key "java/lang/Math.multiplyExact(JI)J" then exact64 s (a * b)
    else if String.eqb key "java/lang/Long.rotateLeft(JI)J" then
      let u := unsigned 64 a in let k := Z.modulo b 64 in MOk (Some (VLong (wrap64 (Z.lor (Z.shiftl u k) (Z.shiftr u (64 - k)))))) s
    else if String.eqb key "java/lang/Long.rotateRight(JI)J" then
      let u := unsigned 64 a in let k := Z.modulo b 64 in MOk (Some (VLong (wrap64 (Z.lor (Z.shiftr u k) (Z.shiftl u (64 - k)))))) s
    else MNoModel
  | _ => MNoModel
  end.

(** Integer.parseInt / Long.parseLong (String, radix) and (CharSequence, begin, end, radix): the
    digits [cs] (starting at index [i]) of a magnitude at most [lim]; the index of the first
    character that is no digit or makes the magnitude exceed [lim], or the magnitude. *)
Fixpoint parse_mag (u : uenv) (r lim : Z) (cs : list Z) (i m : Z) : Z + Z :=
  match cs with
  | nil => inr m
  | c :: t => let d := char_digit u c r in
              if d <? 0 then inl i else
              let m' := m * r + d in
              if lim <? m' then inl i else parse_mag u r lim t (i + 1) m'
  end.

(** The JDK's loop (accumulating negatively against limit = MIN or -MAX): inl None for no
    characters, inl (Some i) for the error index, or the value. *)
Definition parse_signed (u : uenv) (lo r : Z) (cs : list Z) (b : Z) : option Z + Z :=
  match cs with
  | nil => inl None
  | c :: t =>
      if c <? 48 then
        if (c =? 45) || (c =? 43) then
          match t with
          | nil => inl (Some (b + 1))
          | _ => match parse_mag u r (if c =? 45 then - lo else - lo - 1) t (b + 1) 0 with
                 | inl i => inl (Some i)
                 | inr m => inr (if c =? 45 then - m else m)
                 end
          end
        else inl (Some b)
      else match parse_mag u r (- lo - 1) cs b 0 with inl i => inl (Some i) | inr m => inr m end
  end.

Definition for_input (u : list Z) (r : Z) : list Z :=
  app (ascii_units "For input string: """) (app u (app (ascii_units """")
    (if r =? 10 then nil else app (ascii_units " under radix ") (z_units r)))).

Definition radix_check (r : Z) : option (list Z) :=
  if r <? 2 then Some (app (ascii_units "radix ") (app (z_units r) (ascii_units " less than Character.MIN_RADIX")))
  else if 36 <? r then Some (app (ascii_units "radix ") (app (z_units r) (ascii_units " greater than Character.MAX_RADIX")))
  else None.

(** parseInt/parseLong/parseShort/parseByte/valueOf with JDK 21's NumberFormatException texts;
    Short/Byte check the int's range ("Value out of range. Value:"s" Radix:r"). *)
(** Integer/Long.toString(i, radix): the radix 10 when out of [2, 36]; lower-case digits. *)
Fixpoint radix_units (fuel : nat) (r v : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => let d := v mod r in
           let c := if d <? 10 then 48 + d else 87 + d in
           if v <? r then c :: acc else radix_units f r (v / r) (c :: acc)
  end.
Definition z_radix_units (z r : Z) : list Z :=
  let r := if (r <? 2) || (36 <? r) then 10 else r in
  let m := radix_units 70 r (Z.abs z) nil in
  if z <? 0 then 45 :: m else m.

Definition num_parse (e : jenv) (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  let u := j_u e in
  let isI := String.eqb cls "java/lang/Integer" in
  let isL := String.eqb cls "java/lang/Long" in
  let isS := String.eqb cls "java/lang/Short" in
  let isB := String.eqb cls "java/lang/Byte" in
  if negb (isI || isL || isS || isB) then MNoModel else
  let pd := prim_desc cls in
  let lo := if isL then LONG_MIN else INT_MIN in
  let parse_name := if isI then "parseInt" else if isL then "parseLong" else if isS then "parseShort" else "parseByte" in
  let ret := fun (z : Z) => if String.eqb name "valueOf" then let (l, s') := box s cls (if isL then VLong z else VInt z) in MOk (Some (VRef l)) s'
                            else if isL then MOk (Some (VLong z)) s else ret_int s z in
  let str1 := String.eqb desc ("(Ljava/lang/String;)" ++ pd) || String.eqb desc ("(Ljava/lang/String;)L" ++ cls ++ ";") in
  let str2 := String.eqb desc ("(Ljava/lang/String;I)" ++ pd) || String.eqb desc ("(Ljava/lang/String;I)L" ++ cls ++ ";") in
  if String.eqb name "toString" && (String.eqb desc "(II)Ljava/lang/String;" || String.eqb desc "(JI)Ljava/lang/String;") then
    match args with [(VInt z | VLong z); VInt r] => ret_new s (OStr (z_radix_units z r)) | _ => MStuckModel "toString(radix)" end
  else   if (String.eqb name parse_name || String.eqb name "valueOf") && (str1 || str2) then
    let r := match args with [_; VInt r] => r | _ => 10 end in
    match args with
    | VNull :: _ => throw_msg NFE (ascii_units "Cannot parse null string") s
    | v :: _ =>
        match radix_check r with
        | Some m => throw_msg NFE m s
        | None =>
            match str_of s v with
            | None => MStuckModel "parse: string argument"
            | Some w =>
                match parse_signed u lo r w 0 with
                | inl _ => throw_msg NFE (for_input w r) s
                | inr z =>
                    if (isS && ((z <? -32768) || (32767 <? z))) || (isB && ((z <? -128) || (127 <? z))) then
                      throw_msg NFE (app (ascii_units "Value out of range. Value:""") (app w (app (ascii_units """ Radix:") (z_units r)))) s
                    else ret z
                end
            end
        end
    | _ => MStuckModel "parse"
    end
  else if (isI || isL) && String.eqb name (if isI then "parseUnsignedInt" else "parseUnsignedLong")
          && (String.eqb desc ("(Ljava/lang/String;)" ++ pd) || String.eqb desc ("(Ljava/lang/String;I)" ++ pd)) then
    (* parseUnsignedInt/Long: no minus sign; short strings as parseInt/parseLong; longer ones as
       Long.parseLong (int) or parseLong of all but the last digit (long), then the range *)
    let r := match args with [_; VInt r] => r | _ => 10 end in
    let bits := if isI then 32 else 64 in
    match args with
    | VNull :: _ => throw_msg NFE (ascii_units "Cannot parse null string") s
    | v :: _ =>
        match str_of s v with
        | None => MStuckModel "parseUnsigned: string argument"
        | Some nil => throw_msg NFE (for_input nil r) s
        | Some w =>
            let len := slen w in
            let too_big := throw_msg NFE (app (ascii_units "String value ") (app w (ascii_units (if isI then " exceeds range of unsigned int." else " exceeds range of unsigned long.")))) s in
            let fin := fun (z : Z) => if isL then MOk (Some (VLong (signed 64 z))) s else ret_int s (signed 32 z) in
            if match w with c :: _ => c =? 45 | nil => false end then
              throw_msg NFE (app (ascii_units "Illegal leading minus sign on unsigned string ") (app w [46])) s
            else match radix_check r with
                 | Some m => throw_msg NFE m s
                 | None =>
                   if isI then
                     (* parseInt (len <= 5 or radix 10 and len <= 9) else Long.parseLong *)
                     let lo' := if (len <=? 5) || ((r =? 10) && (len <=? 9)) then INT_MIN else LONG_MIN in
                     match parse_signed u lo' r w 0 with
                     | inl _ => throw_msg NFE (for_input w r) s
                     | inr z => if (0 <=? z) && (z <? 2 ^ 32) then fin z else too_big
                     end
                   else if (len <=? 12) || ((r =? 10) && (len <=? 18)) then
                     match parse_signed u LONG_MIN r w 0 with
                     | inl _ => throw_msg NFE (for_input w r) s
                     | inr z => fin (z mod 2 ^ 64)
                     end
                   else
                     let first := firstn (Z.to_nat (len - 1)) w in
                     match parse_signed u LONG_MIN r first 0 with
                     | inl None => throw_msg NFE nil s
                     | inl (Some i) => throw_msg NFE (app (ascii_units "Error at index ") (app (z_units i)
                                         (app (ascii_units " in: """) (app first (ascii_units """"))))) s
                     | inr f =>
                         let d := match nth_unit w (len - 1) with Some c => char_digit u c r | None => -1 end in
                         if d <? 0 then throw_msg NFE (app (ascii_units "Bad digit at end of ") w) s
                         else let z := f * r + d in if (0 <=? z) && (z <? 2 ^ 64) then fin z else too_big
                     end
                 end
        end
    | _ => MStuckModel "parseUnsigned"
    end
  else if String.eqb name "decode" && String.eqb desc ("(Ljava/lang/String;)L" ++ cls ++ ";") then
    (* Integer.decode: an optional sign, then 0x / 0X / # (hex) or 0 followed by more (octal); the
       rest parsed in the radix with the sign (so MIN_VALUE decodes); Short/Byte check the range *)
    match args with
    | [VNull] => throw_msg NPE (ascii_units "Cannot invoke ""String.isEmpty()"" because ""nm"" is null") s
    | [v] =>
        match str_of s v with
        | None => MStuckModel "decode: string argument"
        | Some nil => throw_msg NFE (ascii_units "Zero length string") s
        | Some w =>
            let hd := fun (l : list Z) => match l with c :: _ => c | nil => -1 end in
            let tl := fun (l : list Z) => match l with _ :: t => t | nil => nil end in
            let neg := hd w =? 45 in
            let r1 := if (hd w =? 45) || (hd w =? 43) then tl w else w in
            let '(rad, r2) := if (hd r1 =? 48) && ((hd (tl r1) =? 120) || (hd (tl r1) =? 88)) then (16, tl (tl r1))
                              else if hd r1 =? 35 then (16, tl r1)
                              else if (hd r1 =? 48) && negb (Nat.eqb (length r1) 1) then (8, tl r1)
                              else (10, r1) in
            if (hd r2 =? 45) || (hd r2 =? 43) then throw_msg NFE (ascii_units "Sign character in wrong position") s
            else
                let c := if neg then 45 :: r2 else r2 in
                let lo' := if isL then LONG_MIN else INT_MIN in
                match parse_signed u lo' rad c 0 with
                | inl _ => throw_msg NFE (for_input c rad) s
                | inr z =>
                    if (isS && ((z <? -32768) || (32767 <? z))) || (isB && ((z <? -128) || (127 <? z))) then
                      throw_msg NFE (app (ascii_units "Value ") (app (z_units z) (app (ascii_units " out of range from input ") w))) s
                    else let (l, s') := box s cls (if isL then VLong z else VInt z) in MOk (Some (VRef l)) s'
                end
        end
    | _ => MStuckModel "decode"
    end
  else if String.eqb name parse_name && String.eqb desc ("(Ljava/lang/CharSequence;III)" ++ pd) && (isI || isL) then
    match args with
    | [VNull; _; _; _] => throw_nomsg NPE s
    | [VRef l; VInt b; VInt en; VInt r] =>
        match ms_heap s l with
        | Some (OStr w) | Some (OSb w) =>
            if (b <? 0) || (en <? b) || (slen w <? en) then
              throw_msg "java/lang/IndexOutOfBoundsException"
                (app (ascii_units "Range [") (app (z_units b) (app (ascii_units ", ") (app (z_units en)
                  (app (ascii_units ") out of bounds for length ") (z_units (slen w))))))) s
            else match radix_check r with
                 | Some m => throw_msg NFE m s
                 | None =>
                     let sub := firstn (Z.to_nat (en - b)) (skipn (Z.to_nat b) w) in
                     match parse_signed u lo r sub b with
                     | inl None => throw_msg NFE (if isL then nil else for_input nil r) s
                     | inl (Some i) => throw_msg NFE (app (ascii_units "Error at index ") (app (z_units (i - b))
                                         (app (ascii_units " in: """) (app sub (ascii_units """"))))) s
                     | inr z => ret z
                     end
                 end
        | _ => MStuckModel "parse(CharSequence): argument needs charAt()"
        end
    | _ => MStuckModel "parse(CharSequence)"
    end
  else MNoModel.

Definition num_model (e : jenv) (cls name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := cls ++ "." ++ name ++ desc in
  match num_parse e cls name desc args s with
  | MNoModel => match num_model2 key args s with MNoModel => num_model1 e key args s | r => r end
  | r => r
  end.


(** ** java.util.Objects *)
(** Methods that call back into user code ([equals], [hashCode], [toString], a [Supplier]) or
    throw an exception with a message run as bytecode in a frame of their own (MFrame), as the
    JDK's own code does. *)


Definition objects_model (name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := name ++ desc in
  let frame := fun vs body post rt => MFrame None (model_code vs nil body post false) vs rt s in
  let objeq := Invoke InvVirtual (om "java/lang/Object" "equals" "(Ljava/lang/Object;)Z" false) in
  if String.eqb key "requireNonNull(Ljava/lang/Object;)Ljava/lang/Object;" then
    match args with [VNull] => MFrame None (npe_code args None) args None s | [v] => MOk (Some v) s | _ => MStuckModel "requireNonNull" end
  else if String.eqb key "requireNonNull(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/Object;" then
    match args with [VNull; _] => MFrame None (npe_code args (Some 1)) args None s | [v; _] => MOk (Some v) s | _ => MStuckModel "requireNonNull" end
  else if String.eqb key "requireNonNull(Ljava/lang/Object;Ljava/util/function/Supplier;)Ljava/lang/Object;" then
    match args with
    | [VNull; VNull] => MFrame None (npe_code args None) args None s
    | [VNull; _] =>
        frame args
          [New NPE; Dup; Load KA 1; Invoke InvInterface (om "java/util/function/Supplier" "get" "()Ljava/lang/Object;" true);
           Checkcast "java/lang/String"; Invoke InvSpecial (om NPE "<init>" "(Ljava/lang/String;)V" false); Athrow] nil None
    | [v; _] => MOk (Some v) s
    | _ => MStuckModel "requireNonNull"
    end
  else if String.eqb key "requireNonNullElse(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;" then
    match args with
    | [VNull; VNull] =>
        let (l, s') := alloc s (OStr (ascii_units "defaultObj")) in
        MFrame None (npe_code [VNull; VRef l] (Some 1)) [VNull; VRef l] None s'
    | [VNull; d] => MOk (Some d) s
    | [v; _] => MOk (Some v) s
    | _ => MStuckModel "requireNonNullElse"
    end
  else if String.eqb key "isNull(Ljava/lang/Object;)Z" then
    match args with [v] => ret_bool s (match v with VNull => true | _ => false end) | _ => MStuckModel "isNull" end
  else if String.eqb key "nonNull(Ljava/lang/Object;)Z" then
    match args with [v] => ret_bool s (match v with VNull => false | _ => true end) | _ => MStuckModel "nonNull" end
  else if String.eqb key "equals(Ljava/lang/Object;Ljava/lang/Object;)Z" then
    (* (a == b) || (a != null && a.equals(b)) *)
    match args with
    | [a; b] =>
      if ref_eq a b then ret_bool s true
      else match a with
           | VNull => ret_bool s false
           | _ => match str_of s a with
                  | Some ua => ret_bool s (match str_of s b with Some ub => units_eqb ua ub | None => false end)
                  | None => frame args [Load KA 0; Load KA 1; objeq] [Return (Some KI)] (Some TBool)
                  end
           end
    | _ => MStuckModel "Objects.equals"
    end
  else if String.eqb key "hashCode(Ljava/lang/Object;)I" then
    match args with
    | [VNull] => ret_int s 0
    | [v] => match str_of s v with
             | Some u => ret_int s (str_hash u)
             | None => frame args [Load KA 0; Invoke InvVirtual (om "java/lang/Object" "hashCode" "()I" false)]
                         [Return (Some KI)] (Some TInt)
             end
    | _ => MStuckModel "Objects.hashCode"
    end
  else if String.eqb key "hash([Ljava/lang/Object;)I" then
    (* Arrays.hashCode(values) *)
    match args with
    | [_] => frame args [Load KA 0; Invoke InvStatic (om "java/util/Arrays" "hashCode" "([Ljava/lang/Object;)I" false)]
               [Return (Some KI)] (Some TInt)
    | _ => MStuckModel "Objects.hash"
    end
  else if String.eqb key "toString(Ljava/lang/Object;)Ljava/lang/String;" then
    (* String.valueOf(o) *)
    match args with
    | [_] => frame args [Load KA 0; Invoke InvStatic (om "java/lang/String" "valueOf" "(Ljava/lang/Object;)Ljava/lang/String;" false)]
               [Return (Some KA)] (Some (TRef "java/lang/String"))
    | _ => MStuckModel "Objects.toString"
    end
  else if String.eqb key "toString(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/String;" then
    match args with
    | [VNull; d] => MOk (Some d) s
    | [_; _] => frame args [Load KA 0; Invoke InvVirtual (om "java/lang/Object" "toString" "()Ljava/lang/String;" false)]
                  [Return (Some KA)] (Some (TRef "java/lang/String"))
    | _ => MStuckModel "Objects.toString"
    end
  else if String.eqb key "compare(Ljava/lang/Object;Ljava/lang/Object;Ljava/util/Comparator;)I" then
    (* (a == b) ? 0 : c.compare(a, b) *)
    match args with
    | [a; b; _] => if ref_eq a b then ret_int s 0
                   else frame args [Load KA 2; Load KA 0; Load KA 1;
                                    Invoke InvInterface (om "java/util/Comparator" "compare" "(Ljava/lang/Object;Ljava/lang/Object;)I" true)]
                          [Return (Some KI)] (Some TInt)
    | _ => MStuckModel "Objects.compare"
    end
  else if String.eqb key "checkIndex(II)I" then
    (* Preconditions.outOfBounds: IndexOutOfBoundsException("Index i out of bounds for length n") *)
    match args with
    | [VInt i; VInt n] =>
        if (0 <=? i) && (i <? n) then ret_int s i
        else let (l, s') := alloc s (OStr (app (ascii_units "Index ") (app (z_units i) (app (ascii_units " out of bounds for length ") (z_units n))))) in
             MFrame None (model_code [VInt i; VInt n; VRef l] nil
               [New "java/lang/IndexOutOfBoundsException"; Dup; Load KA 2;
                Invoke InvSpecial (om "java/lang/IndexOutOfBoundsException" "<init>" "(Ljava/lang/String;)V" false); Athrow] nil false)
               [VInt i; VInt n; VRef l] None s'
    | _ => MStuckModel "checkIndex"
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

(** HotSpot's names in arraycopy messages: [int], ..., or [object array]. *)
Definition acopy_kind (t : jtype) : list Z :=
  ascii_units (match t with
               | TBool => "boolean" | TByte => "byte" | TChar => "char" | TShort => "short" | TInt => "int"
               | TLong => "long" | TFloat => "float" | TDouble => "double" | _ => "object array" end).

Definition elem_name (t : jtype) : list Z :=
  class_name_units (match t with TRef c => c | _ => type_desc t end).

(** System.arraycopy with HotSpot's checks in HotSpot's order and its exception messages
    (TypeArrayKlass/ObjArrayKlass::copy_array, JDK 21). *)
Definition arraycopy (p : program) (args : list value) (s : mstate) : model_result :=
  let au := ascii_units in
  let ase := fun m => throw_msg "java/lang/ArrayStoreException" (app (au "arraycopy: ") m) s in
  let aioobe := fun m => throw_msg "java/lang/ArrayIndexOutOfBoundsException" (app (au "arraycopy: ") m) s in
  let dims := fun (t : jtype) (n : Z) => app (acopy_kind t) (app (au "[") (app (z_units n) (au "]"))) in
  match args with
  | [src; VInt sp; dst; VInt dp; VInt n] =>
    match src, dst with
    | VNull, _ | _, VNull => MFrame None (npe_code [] None) [] None s
    | _, _ =>
      match arr_of s src with
      | None =>
          match src with
          | VRef l => match option_map runtime_type (ms_heap s l) with
                      | Some (TRef c) => ase (app (au "source type ") (app (class_name_units c) (au " is not an array")))
                      | _ => MStuckModel "arraycopy: source"
                      end
          | _ => MStuckModel "arraycopy: source"
          end
      | Some (_, ts, es) =>
      match arr_of s dst with
      | None =>
          match dst with
          | VRef l => match option_map runtime_type (ms_heap s l) with
                      | Some (TRef c) => ase (app (au "destination type ") (app (class_name_units c) (au " is not an array")))
                      | _ => MStuckModel "arraycopy: destination"
                      end
          | _ => MStuckModel "arraycopy: destination"
          end
      | Some (ld, td, ed) =>
        let sl := slen_v es in
        let dl := slen_v ed in
        if negb (Bool.eqb (prim_type ts) (prim_type td)) || (prim_type ts && negb (String.eqb (type_desc ts) (type_desc td))) then
          ase (app (au "type mismatch: can not copy ") (app (acopy_kind ts) (app (au "[] into ") (app (acopy_kind td) (au "[]")))))
        else if sp <? 0 then aioobe (app (au "source index ") (app (z_units sp) (app (au " out of bounds for ") (dims ts sl))))
        else if dp <? 0 then aioobe (app (au "destination index ") (app (z_units dp) (app (au " out of bounds for ") (dims td dl))))
        else if n <? 0 then aioobe (app (au "length ") (app (z_units n) (au " is negative")))
        else if sl <? sp + n then aioobe (app (au "last source index ") (app (z_units (sp + n)) (app (au " out of bounds for ") (dims ts sl))))
        else if dl <? dp + n then aioobe (app (au "last destination index ") (app (z_units (dp + n)) (app (au " out of bounds for ") (dims td dl))))
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
              let tname := fun (t : jtype) => match t with TRef c => c | _ => type_desc t end in
              if all_ok then MOk None s'
              else match assignable p 64 td (tname ts) with
                   | Some false =>
                       throw_msg "java/lang/ArrayStoreException"
                         (app (au "arraycopy: type mismatch: can not copy ")
                           (app (elem_name ts) (app (au "[] into ") (app (elem_name td) (au "[]"))))) s'
                   | Some true =>
                       throw_msg "java/lang/ArrayStoreException"
                         (app (au "arraycopy: element type mismatch: can not cast one of the elements of ")
                           (app (elem_name ts) (app (au "[] to the type of the destination array, ") (elem_name td)))) s'
                   | None => MStuckModel "arraycopy: cannot decide element type"
                   end
          end
      end
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
(** The declaring class of an enum constant of class [c]: [c], or its superclass for a constant
    with a body (Enum.getDeclaringClass). *)
Definition enum_decl (p : program) (c : string) : string :=
  match find_class p c with
  | Some cf => match cf_super cf with Some sup => if String.eqb sup "java/lang/Enum" then c else sup | None => c end
  | None => c
  end.

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

(** Class.getCanonicalName of a loaded class from its binary name and simple name (javac's
    naming): a member class Outer$Inner is canonical(Outer) + "." + Inner; a top-level class its
    dotted name; a local or anonymous class has none (Some None). None: not modelled. *)
Fixpoint canon_units (p : program) (fuel : nat) (n : string) : option (option (list Z)) :=
  match fuel with
  | O => None
  | S f =>
    let b := match utf8_units n with Some u => u | None => ascii_units n end in
    match find_class p n with
    | None => if existsb (fun c => c =? 36) b then None else Some (Some (dotted b))
    | Some cf =>
      match simple_name cf with
      | None => None
      | Some nil => Some None
      | Some u =>
        let lb := length b in let lu := length u in
        if Nat.leb (S lu) lb && FloatDec.list_eqb (skipn (lb - S lu) b) (36 :: u) then
          let r := firstn (lb - S lu) b in
          match rev r with
          | c :: _ => if (48 <=? c) && (c <=? 57) then Some None
                      else match units_string r with
                           | Some outer => match canon_units p f outer with
                                           | Some (Some cu) => Some (Some (app cu (46 :: u)))
                                           | Some None => Some None
                                           | None => None
                                           end
                           | None => None
                           end
          | nil => None
          end
        else if FloatDec.list_eqb (after_last 47 b) u then Some (Some (dotted b))
        else Some None
      end
    end
  end.

Definition enum_model (p : program) (name desc : string) (args : list value) (s : mstate) : model_result :=
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
      else if String.eqb name "getDeclaringClass" && String.eqb desc "()Ljava/lang/Class;" then
        let (r, s') := intern s (OCls (enum_decl p c)) in MOk (Some (VRef r)) s'
      else if String.eqb name "compareTo" && (String.eqb desc "(Ljava/lang/Enum;)I" || String.eqb desc "(Ljava/lang/Object;)I") then
        (* self.getClass() != other.getClass() && declaring classes differ: ClassCastException;
           else self.ordinal - other.ordinal *)
        match rest with
        | [VNull] => let (ml, s') := alloc s (OStr (ascii_units "Cannot invoke ""Object.getClass()"" because ""other"" is null")) in
                     MFrame None (npe_code [VNull; VRef ml] (Some 1)) [VNull; VRef ml] None s'
        | [VRef l2] =>
            match ms_heap s l2 with
            | Some (OObj c2 fs2) =>
                if negb (String.eqb c c2) && negb (String.eqb (enum_decl p c) (enum_decl p c2)) then
                  MFrame None (model_code [] nil [New "java/lang/ClassCastException"; Dup;
                    Invoke InvSpecial (om "java/lang/ClassCastException" "<init>" "()V" false); Athrow] nil false) [] None s
                else match assoc (own_key "java/lang/Enum" "ordinal" fs) fs, assoc (own_key "java/lang/Enum" "ordinal" fs2) fs2 with
                     | Some (VInt a), Some (VInt b) => ret_int s (a - b)
                     | _, _ => MStuckModel "Enum.compareTo: not an enum constant"
                     end
            | _ => MThrow "java/lang/ClassCastException"
            end
        | _ => MStuckModel "Enum.compareTo"
        end
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
    type mismatch, [None] not modelled. *)
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
  | TFloat | TDouble =>
      (* unboxing then a widening primitive conversion (byte/short/char/int/long/float -> float/double) *)
      let dbl := match t with TDouble => true | _ => false end in
      match v with
      | VNull => Some None
      | VRef l => match ms_heap s l with
                  | Some (OObj c [("value", w)]) =>
                      match w with
                      | VInt z => if is_box_class c && negb (String.eqb c "java/lang/Boolean")
                                  then Some (Some (if dbl then VDouble (Float.i2d z) else VFloat (Float.i2f z))) else Some None
                      | VLong z => if String.eqb c "java/lang/Long"
                                   then Some (Some (if dbl then VDouble (Float.l2d z) else VFloat (Float.l2f z))) else Some None
                      | VFloat b => if String.eqb c "java/lang/Float"
                                    then Some (Some (if dbl then VDouble (Float.f2d b) else VFloat b)) else Some None
                      | VDouble b => if String.eqb c "java/lang/Double" && dbl then Some (Some (VDouble b)) else Some None
                      | _ => Some None
                      end
                  | Some _ => Some None
                  | None => None
                  end
      | _ => None
      end
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
                      else Some None
                  | Some (OObj c _) => Some None
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
  | Some TFloat => vo "java/lang/Float" "(F)Ljava/lang/Float;"
  | Some TDouble => vo "java/lang/Double" "(D)Ljava/lang/Double;"
  | Some (TRef _) | Some (TArr _) => Some nil
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
      else if String.eqb name "getEnumConstants" && String.eqb desc "()[Ljava/lang/Object;" then
        match class_access p n, class_super p n with
        | Some a, Some sup =>
            if Z.testbit a 14 && match sup with Some c => String.eqb c "java/lang/Enum" | None => false end then
              MFrame None (model_code [] nil
                [Invoke InvStatic {| mr_class := n; mr_name := "values"; mr_desc := "()[L" ++ n ++ ";"; mr_interface := false |}]
                [Return (Some KA)] false) [] (Some (TArr (TRef n))) s
            else MOk (Some VNull) s
        | _, _ => if is_array_name n || builtin_iface n then MOk (Some VNull) s
                  else match builtin_super n with Some _ => MOk (Some VNull) s | None => MStuckModel "getEnumConstants" end
        end
      else if String.eqb name "getSuperclass" && String.eqb desc "()Ljava/lang/Class;" && String.eqb n "java/lang/StringBuffer" then
        MStuckModel "StringBuffer.getSuperclass: AbstractStringBuilder in the JDK"
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
Definition object_model (p : program) (e : jenv) (name desc : string) (args : list value) (s : mstate) : model_result :=
  match args with
  | this :: rest =>
    if String.eqb name "hashCode" && String.eqb desc "()I" then
      match this with VRef l => ret_int s (j_ihash e l) | _ => MStuckModel "hashCode" end
    else if String.eqb name "toString" && String.eqb desc "()Ljava/lang/String;" then
      (* getClass().getName() + "@" + Integer.toHexString(hashCode()), hashCode called virtually *)
      let sbm := fun n d => {| mr_class := "java/lang/StringBuilder"; mr_name := n; mr_desc := d; mr_interface := false |} in
      MFrame None (model_code [this] nil
        [New "java/lang/StringBuilder"; Dup; Invoke InvSpecial (sbm "<init>" "()V");
         Load KA 0;
         Invoke InvVirtual {| mr_class := "java/lang/Object"; mr_name := "getClass"; mr_desc := "()Ljava/lang/Class;"; mr_interface := false |};
         Invoke InvVirtual {| mr_class := "java/lang/Class"; mr_name := "getName"; mr_desc := "()Ljava/lang/String;"; mr_interface := false |};
         Invoke InvVirtual (sbm "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;");
         Iconst 64; Invoke InvVirtual (sbm "append" "(C)Ljava/lang/StringBuilder;");
         Load KA 0;
         Invoke InvVirtual {| mr_class := "java/lang/Object"; mr_name := "hashCode"; mr_desc := "()I"; mr_interface := false |};
         Invoke InvStatic {| mr_class := "java/lang/Integer"; mr_name := "toHexString"; mr_desc := "(I)Ljava/lang/String;"; mr_interface := false |};
         Invoke InvVirtual (sbm "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;");
         Invoke InvVirtual (sbm "toString" "()Ljava/lang/String;")]
        [Return (Some KA)] false) [this] (Some (TRef "java/lang/String")) s
    else if String.eqb name "equals" && String.eqb desc "(Ljava/lang/Object;)Z" then
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
      | None =>
          (* Object.clone: a field-by-field copy if the class implements Cloneable, else
             CloneNotSupportedException(class name) *)
          match this with
          | VRef l =>
              match ms_heap s l with
              | Some (OObj c fs) =>
                  match assignable p 64 (TRef c) "java/lang/Cloneable" with
                  | Some true => ret_new s (OObj c fs)
                  | Some false => throw_msg "java/lang/CloneNotSupportedException" (class_name_units c) s
                  | None => MStuckModel "clone: cannot decide Cloneable"
                  end
              | _ => MStuckModel "clone of this object"
              end
          | _ => MStuckModel "clone"
          end
      end
    else MNoModel
  | nil => MNoModel
  end.


(** Throwable (JDK 21, without stack traces). The fields of an exception object:
    "detailMessage"; "cause" (the object itself while the cause is not initialised, as the
    JDK's [cause = this]; absent for exceptions the machine creates: also not initialised);
    "suppressed" (absent: none yet; VNull: suppression disabled; else a Throwable[]).
    The (Throwable) constructor's message is cause.toString(), computed as bytecode by
    calling the (String, Throwable) constructor with it. *)
Definition set_field (fs : list (string * value)) (k : string) (v : value) : list (string * value) :=
  (k, v) :: filter (fun kv => negb (String.eqb (fst kv) k)) fs.
Definition set_detail (fs : list (string * value)) (v : value) : list (string * value) :=
  set_field fs "detailMessage" v.

Definition THR := "java/lang/Throwable".
Definition SB := "java/lang/StringBuilder".

Definition throwable_init (cls desc : string) (args : list value) (s : mstate) : model_result :=
  match args with
  | VRef l :: rest =>
    match ms_heap s l with
    | Some (OObj c fs) =>
      let put := fun m cause => MOk None (set_heap s l (OObj c (set_field (set_detail fs m) "cause" cause))) in
      if String.eqb desc "()V" then put VNull (VRef l)
      else if String.eqb desc "(Ljava/lang/Throwable;)V" then
        match rest with
        | [VNull] => put VNull VNull
        | [t] => if String.eqb c "java/lang/reflect/InvocationTargetException"
                 then (* InvocationTargetException(target): super((Throwable) null), the target kept *)
                      MOk None (set_heap s l (OObj c (("target", t) :: set_field (set_detail fs VNull) "cause" VNull)))
                 else (* this(cause.toString(), cause) *)
                      MFrame None (model_code args nil
                        [Load KA 0; Load KA 1;
                         Invoke InvVirtual (om "java/lang/Object" "toString" "()Ljava/lang/String;" false);
                         Load KA 1;
                         Invoke InvSpecial (om cls "<init>" "(Ljava/lang/String;Ljava/lang/Throwable;)V" false)]
                        [Return None] false) args None s
        | _ => MStuckModel "Throwable(cause)"
        end
      else if String.eqb desc "(Ljava/lang/String;Ljava/lang/Throwable;)V" then
        match rest with
        | [m; cause] => match m, cause with
                        | (VNull | VRef _), (VNull | VRef _) => put m cause
                        | _, _ => MStuckModel "Throwable.<init>"
                        end
        | _ => MStuckModel "Throwable.<init>"
        end
      else if String.eqb desc "(Ljava/lang/String;Ljava/lang/Throwable;ZZ)V" then
        match rest with
        | [m; cause; VInt supp; _] =>
            match m, cause with
            | (VNull | VRef _), (VNull | VRef _) =>
                let fs' := set_field (set_detail fs m) "cause" cause in
                MOk None (set_heap s l (OObj c (if Z.eqb supp 0 then set_field fs' "suppressed" VNull else fs')))
            | _, _ => MStuckModel "Throwable.<init>"
            end
        | _ => MStuckModel "Throwable.<init>"
        end
      else match rest with
           | [m] => match m with
                    | VNull | VRef _ => put m (VRef l)
                    | _ => MStuckModel "Throwable.<init>"
                    end
           | _ => MStuckModel "Throwable.<init>"
           end
    | _ => MOk None s
    end
  | _ => MOk None s
  end.

(** [new cls(msg, cause)] thrown, as bytecode; [msg] is an ASCII literal, [cause] local 0. *)
Definition throw_with_cause (cls : string) (msg : string) (vs : list value) (cause_local : Z) : code :=
  model_code vs nil
    [New cls; Dup; Ldc (LdcString msg); Load KA cause_local;
     Invoke InvSpecial (om cls "<init>" "(Ljava/lang/String;Ljava/lang/Throwable;)V" false); Athrow] nil false.

(** Throwable's methods on an exception object (receiver first in [args]). *)
Definition throwable_model (name desc : string) (args : list value) (s : mstate) : model_result :=
  let key := name ++ desc in
  match args with
  | VRef l :: rest =>
    match ms_heap s l with
    | Some (OObj c fs) =>
      if String.eqb key "getCause()Ljava/lang/Throwable;" || String.eqb key "getTargetException()Ljava/lang/Throwable;" then
        match assoc "target" fs with
        | Some v => MOk (Some v) s
        | None => match assoc "cause" fs with
                  | Some (VRef x) => MOk (Some (if Z.eqb x l then VNull else VRef x)) s
                  | Some v => MOk (Some v) s
                  | None => MOk (Some VNull) s
                  end
        end
      else if String.eqb key "initCause(Ljava/lang/Throwable;)Ljava/lang/Throwable;" then
        match rest with
        | [cause] =>
          let uninit := match assoc "cause" fs with None => true | Some (VRef x) => Z.eqb x l | Some _ => false end in
          if negb uninit then
            (* IllegalStateException("Can't overwrite cause with " + Objects.toString(cause, "a null"), this) *)
            MFrame None (model_code args nil
              [New "java/lang/IllegalStateException"; Dup;
               New SB; Dup; Ldc (LdcString "Can't overwrite cause with ");
               Invoke InvSpecial (om SB "<init>" "(Ljava/lang/String;)V" false);
               Load KA 1; Ldc (LdcString "a null");
               Invoke InvStatic (om "java/util/Objects" "toString" "(Ljava/lang/Object;Ljava/lang/String;)Ljava/lang/String;" false);
               Invoke InvVirtual (om SB "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;" false);
               Invoke InvVirtual (om SB "toString" "()Ljava/lang/String;" false);
               Load KA 0;
               Invoke InvSpecial (om "java/lang/IllegalStateException" "<init>" "(Ljava/lang/String;Ljava/lang/Throwable;)V" false);
               Athrow] nil false) args None s
          else if ref_eq cause (VRef l) then
            MFrame None (throw_with_cause "java/lang/IllegalArgumentException" "Self-causation not permitted" args 0) args None s
          else match cause with
               | VNull | VRef _ => MOk (Some (VRef l)) (set_heap s l (OObj c (set_field fs "cause" cause)))
               | _ => MStuckModel "initCause"
               end
        | _ => MStuckModel "initCause"
        end
      else if String.eqb key "addSuppressed(Ljava/lang/Throwable;)V" then
        match rest with
        | [x] =>
          if ref_eq x (VRef l) then
            MFrame None (throw_with_cause "java/lang/IllegalArgumentException" "Self-suppression not permitted" [x] 0) [x] None s
          else match x with
               | VNull =>
                   let (m, s') := alloc s (OStr (ascii_units "Cannot suppress a null exception.")) in
                   MFrame None (npe_code [VNull; VRef m] (Some 1)) [VNull; VRef m] None s'
               | VRef _ =>
                   match assoc "suppressed" fs with
                   | Some VNull => MOk None s
                   | Some (VRef a) =>
                       match ms_heap s a with
                       | Some (OArr t es) => let (a', s') := alloc s (OArr t (app es [x])) in
                                             MOk None (set_heap s' l (OObj c (set_field fs "suppressed" (VRef a'))))
                       | _ => MStuckModel "addSuppressed"
                       end
                   | Some _ => MStuckModel "addSuppressed"
                   | None => let (a', s') := alloc s (OArr (TRef THR) [x]) in
                             MOk None (set_heap s' l (OObj c (set_field fs "suppressed" (VRef a'))))
                   end
               | _ => MStuckModel "addSuppressed"
               end
        | _ => MStuckModel "addSuppressed"
        end
      else if String.eqb key "getSuppressed()[Ljava/lang/Throwable;" then
        match assoc "suppressed" fs with
        | Some (VRef a) => match ms_heap s a with
                           | Some (OArr t es) => ret_new s (OArr t es)
                           | _ => MStuckModel "getSuppressed"
                           end
        | _ => ret_new s (OArr (TRef THR) nil)
        end
      else if String.eqb key "fillInStackTrace()Ljava/lang/Throwable;" then MOk (Some (VRef l)) s
      else if String.eqb key "getLocalizedMessage()Ljava/lang/String;" then
        (* getMessage(), dispatched (a subclass may override it) *)
        MFrame None (model_code [VRef l] nil [Load KA 0; Invoke InvVirtual (om THR "getMessage" "()Ljava/lang/String;" false)]
                       [Return (Some KA)] false) [VRef l] (Some (TRef "java/lang/String")) s
      else if String.eqb key "toString()Ljava/lang/String;" then
        (* s = getClass().getName(); m = getLocalizedMessage(); m != null ? s + ": " + m : s *)
        MFrame None (model_code [VRef l; VNull; VNull] nil
          [Load KA 0; Invoke InvVirtual (om "java/lang/Object" "getClass" "()Ljava/lang/Class;" false);
           Invoke InvVirtual (om "java/lang/Class" "getName" "()Ljava/lang/String;" false); Store KA 1;
           Load KA 0; Invoke InvVirtual (om THR "getLocalizedMessage" "()Ljava/lang/String;" false); Store KA 2;
           Load KA 2; IfNull true 19;
           New SB; Dup; Load KA 1; Invoke InvSpecial (om SB "<init>" "(Ljava/lang/String;)V" false);
           Ldc (LdcString ": "); Invoke InvVirtual (om SB "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;" false);
           Load KA 2; Invoke InvVirtual (om SB "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;" false);
           Invoke InvVirtual (om SB "toString" "()Ljava/lang/String;" false);
           Return (Some KA);
           Load KA 1; Return (Some KA)] nil false)
          [VRef l; VNull; VNull] (Some (TRef "java/lang/String")) s
      else if String.eqb key "getMessage()Ljava/lang/String;" then
        match assoc "detailMessage" fs with
        | Some v => MOk (Some v) s
        | None => MStuckModel "exception message not modelled"
        end
      else MNoModel
    | _ => MNoModel
    end
  | _ => MNoModel
  end.

(** ** The JDK model *)
(** ** java.math: the arithmetic of the BigInteger/BigDecimal model classes
    (harness/jdkmodel/src/java/math), natives of java.math.ModelBig on integers encoded as int[]
    { signum, magnitude words big-endian } (the JDK's representation, signum first). *)
Definition big_word (w : Z) : Z := if w <? 0 then w + 2 ^ 32 else w.
Definition big_of (es : list value) : option Z :=
  match es with
  | VInt sg :: ws =>
      let m := fold_left (fun acc v => match v with VInt w => acc * 2 ^ 32 + big_word w | _ => acc end) ws 0 in
      Some (if sg <? 0 then - m else if sg =? 0 then 0 else m)
  | _ => None
  end.
Fixpoint big_words (fuel : nat) (m : Z) (acc : list value) : list value :=
  match fuel with
  | O => acc
  | S f => if m <=? 0 then acc
           else let w := m mod 2 ^ 32 in
                big_words f (m / 2 ^ 32) (VInt (if 2 ^ 31 <=? w then w - 2 ^ 32 else w) :: acc)
  end.
Definition big_enc (z : Z) : list value :=
  VInt (Z.sgn z) :: big_words (S (Z.to_nat (Z.log2 (Z.abs z) / 32 + 1))) (Z.abs z) nil.

Definition big_arg (s : mstate) (v : value) : option Z :=
  match v with
  | VRef l => match ms_heap s l with Some (OArr TInt es) => big_of es | _ => None end
  | _ => None
  end.
Definition ret_big (s : mstate) (z : Z) : model_result := ret_new s (OArr TInt (big_enc z)).

(** a^e mod m by square and multiply (e >= 0, m > 0) *)
Fixpoint big_modpow (fuel : nat) (a e m acc : Z) : Z :=
  match fuel with
  | O => acc
  | S f => if e <=? 0 then acc
           else big_modpow f (a * a mod m) (Z.shiftr e 1) m (if Z.odd e then acc * a mod m else acc)
  end.

(** extended Euclid: (g, x) with a*x = g (mod b) *)
Fixpoint big_egcd (fuel : nat) (a b x0 x1 : Z) : Z * Z :=
  match fuel with
  | O => (a, x0)
  | S f => if b =? 0 then (a, x0) else big_egcd f b (a mod b) x1 (x0 - (a / b) * x1)
  end.

Definition big_digit_char (d : Z) : Z := if d <? 10 then 48 + d else 87 + d.
Fixpoint big_radix (fuel : nat) (r m : Z) (acc : list Z) : list Z :=
  match fuel with
  | O => acc
  | S f => let acc' := big_digit_char (m mod r) :: acc in if m <? r then acc' else big_radix f r (m / r) acc'
  end.

Definition modelbig (name desc : string) (args : list value) (s : mstate) : model_result :=
  if String.eqb name "op2" then
    match args with
    | [VInt op; a; b] =>
      match big_arg s a, big_arg s b with
      | Some x, Some y =>
          let nz := negb (y =? 0) in
          if op =? 0 then ret_big s (x + y)
          else if op =? 1 then ret_big s (x - y)
          else if op =? 2 then ret_big s (x * y)
          else if (op =? 3) && nz then ret_big s (Z.quot x y)
          else if (op =? 4) && nz then ret_big s (Z.rem x y)
          else if (op =? 5) && (0 <? y) then ret_big s (Z.modulo x y)
          else if op =? 6 then ret_big s (Z.gcd x y)
          else if op =? 7 then ret_big s (Z.land x y)
          else if op =? 8 then ret_big s (Z.lor x y)
          else if op =? 9 then ret_big s (Z.lxor x y)
          else if op =? 10 then ret_big s (Z.ldiff x y)
          else if (op =? 11) && (0 <=? y) && (y <=? 100000) then ret_big s (x ^ y)
          else if (op =? 12) && (Z.abs y <=? 10000000) then ret_big s (Z.shiftl x y)
          else if (op =? 13) && (Z.abs y <=? 10000000) then ret_big s (Z.shiftr x y)
          else if op =? 14 then ret_big s (match Z.compare x y with Lt => -1 | Eq => 0 | Gt => 1 end)
          else if (op =? 15) && (0 <? y) then
            (* modInverse: [] when not invertible *)
            let '(g, u) := big_egcd (S (Z.to_nat (2 * Z.log2 (Z.abs y) + 4))) (Z.modulo x y) y 1 0 in
            if g =? 1 then ret_big s (Z.modulo u y) else ret_new s (OArr TInt nil)
          else MStuckModel "ModelBig.op2"
      | _, _ => MStuckModel "ModelBig.op2 arguments"
      end
    | _ => MStuckModel "ModelBig.op2: arguments"
    end
  else if String.eqb name "op1" then
    match args with
    | [VInt op; a] =>
      match big_arg s a with
      | Some x =>
          if op =? 0 then ret_big s (- x)
          else if op =? 1 then ret_big s (Z.lnot x)
          else if (op =? 2) && (0 <=? x) then ret_big s (Z.sqrt x)
          else if op =? 3 then ret_int s (if x <? 0 then Z.log2 (Z.lnot x) + (if Z.lnot x =? 0 then 0 else 1) else (if x =? 0 then 0 else Z.log2 x + 1))
          else MStuckModel "ModelBig.op1"
      | None => MStuckModel "ModelBig.op1 arguments"
      end
    | _ => MStuckModel "ModelBig.op1: arguments"
    end
  else if String.eqb name "modPow" then
    match args with
    | [a; b; c] =>
      match big_arg s a, big_arg s b, big_arg s c with
      | Some x, Some y, Some m => if (0 <? m) && (0 <=? y)
                                  then ret_big s (big_modpow (S (Z.to_nat (Z.log2 y + 1))) (Z.modulo x m) y m (Z.modulo 1 m))
                                  else MStuckModel "ModelBig.modPow"
      | _, _, _ => MStuckModel "ModelBig.modPow arguments"
      end
    | _ => MStuckModel "ModelBig.modPow: arguments"
    end
  else if String.eqb name "toStr" then
    match args with
    | [a; VInt r] =>
      match big_arg s a with
      | Some x => if (2 <=? r) && (r <=? 36) then
                    let u := big_radix (S (Z.to_nat (Z.log2 (Z.abs x) + 1))) r (Z.abs x) nil in
                    ret_new s (OStr (if x <? 0 then 45 :: u else u))
                  else MStuckModel "ModelBig.toStr radix"
      | None => MStuckModel "ModelBig.toStr"
      end
    | _ => MStuckModel "ModelBig.toStr: arguments"
    end
  else if String.eqb name "fromDigits" then
    match args with
    | [VRef l; VInt r] =>
      match ms_heap s l with
      | Some (OArr TInt ds) => ret_big s (fold_left (fun acc v => match v with VInt d => acc * r + d | _ => acc end) ds 0)
      | _ => MStuckModel "ModelBig.fromDigits"
      end
    | _ => MStuckModel "ModelBig.fromDigits: arguments"
    end
  else if String.eqb name "toDouble" then
    match args with
    | [a] =>
      match big_arg s a with
      | Some x => MOk (Some (VDouble (Float.round Float.binary64 (x <? 0) (Z.abs x) 0))) s
      | None => MStuckModel "ModelBig.toDouble"
      end
    | _ => MStuckModel "ModelBig.toDouble: arguments"
    end
  else if String.eqb name "toFloat" then
    match args with
    | [a] =>
      match big_arg s a with
      | Some x => MOk (Some (VFloat (Float.round Float.binary32 (x <? 0) (Z.abs x) 0))) s
      | None => MStuckModel "ModelBig.toFloat"
      end
    | _ => MStuckModel "ModelBig.toFloat: arguments"
    end
  else MNoModel.

(** Enum.valueOf(Class, String): the constant of [values()] whose name() equals the name; else
    "Name is null" (NullPointerException) or "No enum constant <canonical name>.<name>"; a class that
    is not an enum: "<name> is not an enum class". *)
Definition enum_valueof (p : program) (args : list value) (s : mstate) : model_result :=
  match args with
  | [VNull; _] =>
      let (ml, s') := alloc s (OStr (ascii_units "Cannot invoke ""java.lang.Class.enumConstantDirectory()"" because ""enumClass"" is null")) in
      MFrame None (npe_code [VNull; VRef ml] (Some 1)) [VNull; VRef ml] None s'
  | [VRef c; nm] =>
      match ms_heap s c with
      | Some (OCls n) =>
          match class_access p n, class_super p n with
          | Some a, Some sup =>
              if Z.testbit a 14 && match sup with Some x => String.eqb x "java/lang/Enum" | None => false end then
                match canon_units p 8 n with
                | None => MStuckModel "Enum.valueOf: canonical name"
                | Some cn =>
                    let pre := app (ascii_units "No enum constant ")
                                 (app (match cn with Some u => u | None => null_units end) [46]) in
                    let (pl, s1) := alloc s (OStr pre) in
                    let vs := [VRef c; nm; VNull; VInt 0; VRef pl] in
                    MFrame None (model_code vs nil
                      [Invoke InvStatic (om n "values" ("()[L" ++ n ++ ";") false); Store KA 2;
                       Load KI 3; Load KA 2; Arraylength; IfIcmp CGe 19;
                       Load KA 2; Load KI 3; ALoadArr AA;
                       Invoke InvVirtual (om "java/lang/Enum" "name" "()Ljava/lang/String;" false);
                       Load KA 1; Invoke InvVirtual (om "java/lang/String" "equals" "(Ljava/lang/Object;)Z" false);
                       If CEq 17;
                       Load KA 2; Load KI 3; ALoadArr AA; Return (Some KA);
                       Iinc 3 1; Goto 2;
                       Load KA 1; IfNull false 26;
                       New NPE; Dup; Ldc (LdcString "Name is null");
                       Invoke InvSpecial (om NPE "<init>" "(Ljava/lang/String;)V" false); Athrow;
                       New IAE; Dup; New "java/lang/StringBuilder"; Dup; Load KA 4;
                       Invoke InvSpecial (om "java/lang/StringBuilder" "<init>" "(Ljava/lang/String;)V" false);
                       Load KA 1; Invoke InvVirtual (om "java/lang/StringBuilder" "append" "(Ljava/lang/String;)Ljava/lang/StringBuilder;" false);
                       Invoke InvVirtual (om "java/lang/StringBuilder" "toString" "()Ljava/lang/String;" false);
                       Invoke InvSpecial (om IAE "<init>" "(Ljava/lang/String;)V" false); Athrow] nil false)
                      vs (Some (TRef "java/lang/Enum")) s1
                end
              else throw_msg IAE (app (class_name_units n) (ascii_units " is not an enum class")) s
          | _, _ => match builtin_super n with
                    | Some _ => throw_msg IAE (app (class_name_units n) (ascii_units " is not an enum class")) s
                    | None => MStuckModel "Enum.valueOf: class not loaded"
                    end
          end
      | _ => MStuckModel "Enum.valueOf"
      end
  | _ => MStuckModel "Enum.valueOf"
  end.

(** A system property's String: one object per property for the run (not the interned literal), as
    HotSpot's Properties table holds it. *)
Definition prop_obj (k : string) (u : list Z) (s : mstate) : model_result :=
  let key := "#prop:" ++ k in
  match assoc key (ms_statics s) with
  | Some v => MOk (Some v) s
  | None => let (l, s1) := alloc s (OStr u) in
            MOk (Some (VRef l)) {| ms_heap := ms_heap s1; ms_next := ms_next s1; ms_statics := (key, VRef l) :: ms_statics s1;
                                   ms_inited := ms_inited s1; ms_locks := ms_locks s1; ms_frames := ms_frames s1 |}
  end.

Definition jdk_model (p : program) (e : jenv) : model :=
  fun cls name desc args s =>
    (* constructors of the java.lang exceptions: no observable state is modelled *)
    if String.eqb name "<init>" && is_builtin_throwable cls
       && (String.eqb desc "()V" || String.eqb desc "(Ljava/lang/String;)V"
           || String.eqb desc "(Ljava/lang/String;Ljava/lang/Throwable;)V"
           || String.eqb desc "(Ljava/lang/Throwable;)V"
           || String.eqb desc "(Ljava/lang/String;Ljava/lang/Throwable;ZZ)V") then throwable_init cls desc args s
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
                      else if is_fbox c then fbox_model c "compareTo" desc args s
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
    (* Throwable's methods (causes, suppressed exceptions, messages, toString) *)
    else if is_builtin_throwable cls && match throwable_model name desc args s with MNoModel => false | _ => true end then
      throwable_model name desc args s
    else if String.eqb cls "java/lang/Object" then
      if String.eqb name "<init>" && String.eqb desc "()V" then MOk None s
      else object_model p e name desc args s
    else if String.eqb cls "java/lang/String" then
      match string_model e name desc args s with
      | MNoModel => match string_static name desc args s with
                    | MNoModel => object_model p e name desc args s
                    | r => r
                    end
      | r => r
      end
    else if String.eqb cls "java/lang/StringBuilder" || String.eqb cls "java/lang/AbstractStringBuilder" then
      sb_model name desc args s
    else if is_box_class cls && match box_model cls name desc args s with MNoModel => false | _ => true end then
      box_model cls name desc args s
    else if is_fbox cls && match fbox_model cls name desc args s with MNoModel => false | _ => true end then
      fbox_model cls name desc args s
    else if String.eqb cls "java/lang/Character" then char_model e name desc args s
    else if (String.eqb cls "java/lang/Math" || String.eqb cls "java/lang/StrictMath")
            && match fmath_model cls name desc args s with MNoModel => false | _ => true end then
      fmath_model cls name desc args s
    else if String.eqb cls "java/lang/Integer" || String.eqb cls "java/lang/Long" || String.eqb cls "java/lang/Math"
            || String.eqb cls "java/lang/Short" || String.eqb cls "java/lang/Byte" then
      num_model e cls name desc args s
    (* java.lang.reflect.Array.newInstance(Class, int): a new array of that component type *)
    else if String.eqb cls "java/lang/reflect/Array" && String.eqb name "newInstance"
            && String.eqb desc "(Ljava/lang/Class;I)Ljava/lang/Object;" then
      match args with
      | [VNull; _] => MThrow NPE
      | [VRef c; VInt n] =>
          match ms_heap s c with
          | Some (OCls cn) =>
              let t := if prefix "[" cn || Nat.eqb (String.length cn) 1 then field_type cn else Some (TRef cn) in
              match t with
              | Some et => if n <? 0 then throw_with_msg s "java/lang/NegativeArraySizeException" (z_units n)
                           else if MAX_ARRAY <? n then MStuckModel "Array.newInstance: beyond the model bound"
                           else ret_new s (OArr et (repeat (default_of et) (Z.to_nat n)))
              | None => MThrow "java/lang/IllegalArgumentException"
              end
          | _ => MStuckModel "Array.newInstance: not a Class"
          end
      | _ => MStuckModel "Array.newInstance args"
      end
    else if String.eqb cls "java/util/Objects" then objects_model name desc args s
    else if String.eqb cls "java/math/ModelBig" then modelbig name desc args s
    (* the model classes' "no claim" helpers (java.util.ModelStuck and its per-package copies):
       STUCK, with the reason they give *)
    else if String.eqb name "unsupported" && String.eqb desc "(Ljava/lang/String;)Ljava/lang/RuntimeException;"
            && match index 0 "ModelStuck" cls with Some _ => true | None => false end
            && match args with [v] => match str_of s v with Some _ => true | None => false end | _ => false end then
      match args with
      | [v] => match option_bind (str_of s v) units_string with
               | Some t => MStuckModel ("model class: " ++ t)
               | None => MStuckModel "model class: (non-ASCII reason)"
               end
      | _ => MStuckModel "model class"
      end
    else if String.eqb cls "java/util/ModelEnv" && String.eqb name "seed" && String.eqb desc "(I)J" then
      match args with [VInt n] => MOk (Some (VLong (j_seed e n))) s | _ => MStuckModel "ModelEnv.seed" end
    (* the decimal f * 10^e of Double.toString (FloatDec.select), for the model Formatter *)
    else if String.eqb cls "java/util/ModelEnv" && (String.eqb name "decF" || String.eqb name "decE") then
      match args with
      | [VDouble b] => match FloatDec.select Float.binary64 b with
                       | Some (f, i) => if String.eqb name "decF" then MOk (Some (VLong f)) s else ret_int s i
                       | None => MStuckModel "ModelEnv.dec: not a positive finite double"
                       end
      | _ => MStuckModel "ModelEnv.dec"
      end
    else if String.eqb cls "java/lang/System" && String.eqb name "arraycopy" then arraycopy p args s
    (* System.getProperty(key[, def]): checkKey ("key can't be null" / "key can't be empty"), then the
       platform properties the model fixes (Unix: line.separator, file.separator, path.separator);
       every other property depends on the host: STUCK *)
    else if String.eqb cls "java/lang/System" && String.eqb name "getProperty"
            && (String.eqb desc "(Ljava/lang/String;)Ljava/lang/String;" || String.eqb desc "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;") then
      match args with
      | VNull :: _ => throw_msg NPE (ascii_units "key can't be null") s
      | k :: _ =>
          match str_of s k with
          | Some nil => throw_msg IAE (ascii_units "key can't be empty") s
          | Some u => if FloatDec.list_eqb u (ascii_units "line.separator") then prop_obj "line.separator" [10] s
                      else if FloatDec.list_eqb u (ascii_units "file.separator") then prop_obj "file.separator" [47] s
                      else if FloatDec.list_eqb u (ascii_units "path.separator") then prop_obj "path.separator" [58] s
                      else MStuckModel "System.getProperty: a host property"
          | None => MStuckModel "System.getProperty"
          end
      | _ => MStuckModel "System.getProperty"
      end
    (* CharSequence.isEmpty() (default method): this.length() == 0 *)
    else if String.eqb cls "java/lang/CharSequence" && String.eqb name "isEmpty" && String.eqb desc "()Z" then
      match args with
      | [this] => MFrame None (model_code [this] nil
                    [Load KA 0; Invoke InvInterface (om "java/lang/CharSequence" "length" "()I" true); If CNe 5; Iconst 1; Return (Some KI);
                     Iconst 0; Return (Some KI)] nil false) [this] (Some TBool) s
      | _ => MStuckModel "CharSequence.isEmpty"
      end
    (* System.lineSeparator(): "\n" (a Unix platform, as the model Formatter's %n; TRUST.md 5f) *)
    else if String.eqb cls "java/lang/System" && String.eqb name "lineSeparator" && String.eqb desc "()Ljava/lang/String;" then
      prop_obj "line.separator" [10] s
    else if String.eqb cls "java/lang/System" && String.eqb name "identityHashCode" && String.eqb desc "(Ljava/lang/Object;)I" then
      match args with [VNull] => ret_int s 0 | [VRef l] => ret_int s (j_ihash e l) | _ => MStuckModel "identityHashCode" end
    else if String.eqb cls "java/util/Arrays" then arrays_model p name desc args s
    else if String.eqb cls "java/lang/Enum" && String.eqb name "valueOf"
            && String.eqb desc "(Ljava/lang/Class;Ljava/lang/String;)Ljava/lang/Enum;" then
      enum_valueof p args s
    else if String.eqb cls "java/lang/Enum" then
      match enum_model p name desc args s with MNoModel => object_model p e name desc args s | r => r end
    else if prefix "[" cls then object_model p e name desc args s
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

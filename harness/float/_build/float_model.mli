
val xorb : bool -> bool -> bool

val negb : bool -> bool

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

val eqb : bool -> bool -> bool

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  val size : positive -> positive

  val testbit : positive -> n -> bool
 end

module N :
 sig
  val succ_pos : n -> positive

  val coq_lor : n -> n -> n

  val ldiff : n -> n -> n

  val coq_lxor : n -> n -> n
 end

module Coq_N :
 sig
  val testbit : n -> n -> bool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val eqb : z -> z -> bool

  val max : z -> z -> z

  val min : z -> z -> z

  val of_N : n -> z

  val pos_div_eucl : positive -> z -> z * z

  val div_eucl : z -> z -> z * z

  val modulo : z -> z -> z

  val div2 : z -> z

  val shiftl : z -> z -> z

  val shiftr : z -> z -> z

  val coq_land : z -> z -> z

  val coq_lxor : z -> z -> z

  val pred : z -> z

  val abs : z -> z

  val odd : z -> bool

  val log2 : z -> z

  val testbit : z -> z -> bool

  val ones : z -> z
 end

val iNT_MIN : z

val iNT_MAX : z

val lONG_MIN : z

val lONG_MAX : z

type fmt = { mbits : z; ebits : z }

val binary32 : fmt

val binary64 : fmt

val pow2 : z -> z

val width : fmt -> z

val bias : fmt -> z

val emax_biased : fmt -> z

val emin_ulp : fmt -> z

val norm : fmt -> z -> z

val sign_bit : fmt -> z -> bool

val biased_exp : fmt -> z -> z

val fraction : fmt -> z -> z

type fval =
| NaN
| Inf of bool
| Fin of bool * z * z

val decode : fmt -> z -> fval

val is_nan : fmt -> z -> bool

val sign_val : fmt -> bool -> z

val zero_bits : fmt -> bool -> z

val inf_bits : fmt -> bool -> z

val qnan : fmt -> z

val canon : fmt -> z -> z

val shr_rne : z -> z -> z

val round : fmt -> bool -> z -> z -> z

val neg : fmt -> z -> z

val signed : bool -> z -> z

val add0 : fmt -> z -> z -> z

val sub0 : fmt -> z -> z -> z

val mul0 : fmt -> z -> z -> z

val div : fmt -> z -> z -> z

val pow2mod_pos : positive -> z -> z

val pow2mod : z -> z -> z

val rem : fmt -> z -> z -> z

val of_int : fmt -> z -> z

val convert : fmt -> fmt -> z -> z

val clamp : z -> z -> z -> z

val to_int : fmt -> z -> z -> z -> z

val cmp_key : fmt -> z -> z

val cmp : fmt -> bool -> z -> z -> z

val canon32 : z -> z

val canon64 : z -> z

val fadd32 : z -> z -> z

val fsub32 : z -> z -> z

val fmul32 : z -> z -> z

val fdiv32 : z -> z -> z

val frem32 : z -> z -> z

val fneg32 : z -> z

val dadd64 : z -> z -> z

val dsub64 : z -> z -> z

val dmul64 : z -> z -> z

val ddiv64 : z -> z -> z

val drem64 : z -> z -> z

val dneg64 : z -> z

val i2f : z -> z

val i2d : z -> z

val l2f : z -> z

val l2d : z -> z

val f2d : z -> z

val d2f : z -> z

val f2i : z -> z

val f2l : z -> z

val d2i : z -> z

val d2l : z -> z

val fcmp32 : bool -> z -> z -> z

val dcmp64 : bool -> z -> z -> z

val fcmpl : z -> z -> z

val fcmpg : z -> z -> z

val dcmpl : z -> z -> z

val dcmpg : z -> z -> z

val shr_away : z -> z -> z

val round_mut : z -> fmt -> bool -> z -> z -> z

val add_mut : z -> fmt -> z -> z -> z

val mul_mut : z -> fmt -> z -> z -> z

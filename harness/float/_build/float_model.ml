
(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

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

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
  | XH -> XH

  (** val testbit : positive -> n -> bool **)

  let rec testbit p n0 =
    match p with
    | XI p0 -> (match n0 with
                | N0 -> true
                | Npos n1 -> testbit p0 (pred_N n1))
    | XO p0 -> (match n0 with
                | N0 -> false
                | Npos n1 -> testbit p0 (pred_N n1))
    | XH -> (match n0 with
             | N0 -> true
             | Npos _ -> false)
 end

module N =
 struct
  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Pos.succ p

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.ldiff p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.coq_lxor p q)
 end

module Coq_N =
 struct
  (** val testbit : n -> n -> bool **)

  let testbit a n0 =
    match a with
    | N0 -> false
    | Npos p -> Coq_Pos.testbit p n0
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val min : z -> z -> z **)

  let min n0 m =
    match compare n0 m with
    | Gt -> m
    | _ -> n0

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Pos.pred_N a0))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_lxor : z -> z -> z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Pos.coq_lxor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lxor (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))

  (** val pred : z -> z **)

  let pred x =
    add x (Zneg XH)

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> false
  | Zpos p -> (match p with
               | XO _ -> false
               | _ -> true)
  | Zneg p -> (match p with
               | XO _ -> false
               | _ -> true)

  (** val log2 : z -> z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | XI p -> Zpos (Coq_Pos.size p)
     | XO p -> Zpos (Coq_Pos.size p)
     | XH -> Z0)
  | _ -> Z0

  (** val testbit : z -> z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> false
     | Zpos a0 -> Coq_Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (Coq_N.testbit (Coq_Pos.pred_N a0) (Npos p)))
  | Zneg _ -> false

  (** val ones : z -> z **)

  let ones n0 =
    pred (shiftl (Zpos XH) n0)
 end

(** val iNT_MIN : z **)

let iNT_MIN =
  Z.opp (Z.pow (Zpos (XO XH)) (Zpos (XI (XI (XI (XI XH))))))

(** val iNT_MAX : z **)

let iNT_MAX =
  Z.sub (Z.pow (Zpos (XO XH)) (Zpos (XI (XI (XI (XI XH)))))) (Zpos XH)

(** val lONG_MIN : z **)

let lONG_MIN =
  Z.opp (Z.pow (Zpos (XO XH)) (Zpos (XI (XI (XI (XI (XI XH)))))))

(** val lONG_MAX : z **)

let lONG_MAX =
  Z.sub (Z.pow (Zpos (XO XH)) (Zpos (XI (XI (XI (XI (XI XH))))))) (Zpos XH)

type fmt = { mbits : z; ebits : z }

(** val binary32 : fmt **)

let binary32 =
  { mbits = (Zpos (XI (XI (XI (XO XH))))); ebits = (Zpos (XO (XO (XO XH)))) }

(** val binary64 : fmt **)

let binary64 =
  { mbits = (Zpos (XO (XO (XI (XO (XI XH)))))); ebits = (Zpos (XI (XI (XO
    XH)))) }

(** val pow2 : z -> z **)

let pow2 n0 =
  Z.shiftl (Zpos XH) n0

(** val width : fmt -> z **)

let width f =
  Z.add (Z.add f.mbits f.ebits) (Zpos XH)

(** val bias : fmt -> z **)

let bias f =
  Z.sub (pow2 (Z.sub f.ebits (Zpos XH))) (Zpos XH)

(** val emax_biased : fmt -> z **)

let emax_biased f =
  Z.sub (pow2 f.ebits) (Zpos XH)

(** val emin_ulp : fmt -> z **)

let emin_ulp f =
  Z.sub (Z.sub (Zpos XH) (bias f)) f.mbits

(** val norm : fmt -> z -> z **)

let norm f x =
  Z.coq_land x (Z.ones (width f))

(** val sign_bit : fmt -> z -> bool **)

let sign_bit f x =
  Z.testbit x (Z.sub (width f) (Zpos XH))

(** val biased_exp : fmt -> z -> z **)

let biased_exp f x =
  Z.coq_land (Z.shiftr x f.mbits) (Z.ones f.ebits)

(** val fraction : fmt -> z -> z **)

let fraction f x =
  Z.coq_land x (Z.ones f.mbits)

type fval =
| NaN
| Inf of bool
| Fin of bool * z * z

(** val decode : fmt -> z -> fval **)

let decode f x =
  let s = sign_bit f x in
  let be = biased_exp f x in
  let fr = fraction f x in
  if Z.eqb be (emax_biased f)
  then if Z.eqb fr Z0 then Inf s else NaN
  else if Z.eqb be Z0
       then Fin (s, fr, (emin_ulp f))
       else Fin (s, (Z.add fr (pow2 f.mbits)),
              (Z.add (Z.sub be (Zpos XH)) (emin_ulp f)))

(** val is_nan : fmt -> z -> bool **)

let is_nan f x =
  (&&) (Z.eqb (biased_exp f x) (emax_biased f))
    (negb (Z.eqb (fraction f x) Z0))

(** val sign_val : fmt -> bool -> z **)

let sign_val f = function
| true -> pow2 (Z.sub (width f) (Zpos XH))
| false -> Z0

(** val zero_bits : fmt -> bool -> z **)

let zero_bits =
  sign_val

(** val inf_bits : fmt -> bool -> z **)

let inf_bits f s =
  Z.add (sign_val f s) (Z.mul (emax_biased f) (pow2 f.mbits))

(** val qnan : fmt -> z **)

let qnan f =
  Z.add (Z.mul (emax_biased f) (pow2 f.mbits))
    (pow2 (Z.sub f.mbits (Zpos XH)))

(** val canon : fmt -> z -> z **)

let canon f x =
  if is_nan f x then qnan f else norm f x

(** val shr_rne : z -> z -> z **)

let shr_rne m k =
  let q = Z.shiftr m k in
  let r = Z.sub m (Z.shiftl q k) in
  let half = pow2 (Z.sub k (Zpos XH)) in
  if (||) (Z.ltb half r) ((&&) (Z.eqb r half) (Z.odd q))
  then Z.add q (Zpos XH)
  else q

(** val round : fmt -> bool -> z -> z -> z **)

let round f s m e =
  if Z.leb m Z0
  then zero_bits f s
  else let q0 = Z.max (Z.sub (Z.add (Z.log2 m) e) f.mbits) (emin_ulp f) in
       let mq0 =
         if Z.leb q0 e
         then Z.shiftl m (Z.sub e q0)
         else shr_rne m (Z.sub q0 e)
       in
       if Z.eqb mq0 (pow2 (Z.add f.mbits (Zpos XH)))
       then let mq = pow2 f.mbits in
            let q = Z.add q0 (Zpos XH) in
            if Z.ltb mq (pow2 f.mbits)
            then Z.add (sign_val f s) mq
            else let be = Z.add (Z.sub q (emin_ulp f)) (Zpos XH) in
                 if Z.leb (emax_biased f) be
                 then inf_bits f s
                 else Z.add (Z.add (sign_val f s) (Z.mul be (pow2 f.mbits)))
                        (Z.sub mq (pow2 f.mbits))
       else if Z.ltb mq0 (pow2 f.mbits)
            then Z.add (sign_val f s) mq0
            else let be = Z.add (Z.sub q0 (emin_ulp f)) (Zpos XH) in
                 if Z.leb (emax_biased f) be
                 then inf_bits f s
                 else Z.add (Z.add (sign_val f s) (Z.mul be (pow2 f.mbits)))
                        (Z.sub mq0 (pow2 f.mbits))

(** val neg : fmt -> z -> z **)

let neg f x =
  Z.coq_lxor x (pow2 (Z.sub (width f) (Zpos XH)))

(** val signed : bool -> z -> z **)

let signed s m =
  if s then Z.opp m else m

(** val add0 : fmt -> z -> z -> z **)

let add0 f x y =
  match decode f x with
  | NaN -> qnan f
  | Inf sx ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> if eqb sx sy then inf_bits f sx else qnan f
     | Fin (_, _, _) -> inf_bits f sx)
  | Fin (sx, mx, ex) ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> inf_bits f sy
     | Fin (sy, my, ey) ->
       let e = Z.min ex ey in
       let t =
         Z.add (signed sx (Z.shiftl mx (Z.sub ex e)))
           (signed sy (Z.shiftl my (Z.sub ey e)))
       in
       if Z.eqb t Z0
       then zero_bits f ((&&) sx sy)
       else round f (Z.ltb t Z0) (Z.abs t) e)

(** val sub0 : fmt -> z -> z -> z **)

let sub0 f x y =
  add0 f x (neg f y)

(** val mul0 : fmt -> z -> z -> z **)

let mul0 f x y =
  match decode f x with
  | NaN -> qnan f
  | Inf sx ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> inf_bits f (xorb sx sy)
     | Fin (sy, my, _) ->
       if Z.eqb my Z0 then qnan f else inf_bits f (xorb sx sy))
  | Fin (sx, mx, ex) ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> if Z.eqb mx Z0 then qnan f else inf_bits f (xorb sx sy)
     | Fin (sy, my, ey) -> round f (xorb sx sy) (Z.mul mx my) (Z.add ex ey))

(** val div : fmt -> z -> z -> z **)

let div f x y =
  match decode f x with
  | NaN -> qnan f
  | Inf sx ->
    (match decode f y with
     | Fin (sy, _, _) -> inf_bits f (xorb sx sy)
     | _ -> qnan f)
  | Fin (sx, mx, ex) ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> zero_bits f (xorb sx sy)
     | Fin (sy, my, ey) ->
       if Z.eqb my Z0
       then if Z.eqb mx Z0 then qnan f else inf_bits f (xorb sx sy)
       else let k = Z.add (Z.mul (Zpos (XO XH)) f.mbits) (Zpos (XO (XI XH)))
            in
            let (q, r) = Z.div_eucl (Z.shiftl mx k) my in
            round f (xorb sx sy)
              (Z.add (Z.mul (Zpos (XO XH)) q)
                (if Z.eqb r Z0 then Z0 else Zpos XH))
              (Z.sub (Z.sub (Z.sub ex ey) k) (Zpos XH)))

(** val pow2mod_pos : positive -> z -> z **)

let rec pow2mod_pos p m =
  match p with
  | XI p' ->
    let r = pow2mod_pos p' m in Z.modulo (Z.mul (Zpos (XO XH)) (Z.mul r r)) m
  | XO p' -> let r = pow2mod_pos p' m in Z.modulo (Z.mul r r) m
  | XH -> Z.modulo (Zpos (XO XH)) m

(** val pow2mod : z -> z -> z **)

let pow2mod d m =
  match d with
  | Zpos p -> pow2mod_pos p m
  | _ -> Z.modulo (Zpos XH) m

(** val rem : fmt -> z -> z -> z **)

let rem f x y =
  match decode f x with
  | Fin (sx, mx, ex) ->
    (match decode f y with
     | NaN -> qnan f
     | Inf _ -> norm f x
     | Fin (_, my, ey) ->
       if Z.eqb my Z0
       then qnan f
       else if Z.eqb mx Z0
            then norm f x
            else if Z.leb ey ex
                 then round f sx
                        (Z.modulo
                          (Z.mul (Z.modulo mx my) (pow2mod (Z.sub ex ey) my))
                          my)
                        ey
                 else round f sx (Z.modulo mx (Z.shiftl my (Z.sub ey ex))) ex)
  | _ -> qnan f

(** val of_int : fmt -> z -> z **)

let of_int f z0 =
  if Z.eqb z0 Z0
  then zero_bits f false
  else round f (Z.ltb z0 Z0) (Z.abs z0) Z0

(** val convert : fmt -> fmt -> z -> z **)

let convert f1 f2 x =
  match decode f1 x with
  | NaN -> qnan f2
  | Inf s -> inf_bits f2 s
  | Fin (s, m, e) -> round f2 s m e

(** val clamp : z -> z -> z -> z **)

let clamp lo hi z0 =
  Z.max lo (Z.min hi z0)

(** val to_int : fmt -> z -> z -> z -> z **)

let to_int f lo hi x =
  match decode f x with
  | NaN -> Z0
  | Inf s -> if s then lo else hi
  | Fin (s, m, e) ->
    let t = if Z.leb Z0 e then Z.shiftl m e else Z.shiftr m (Z.opp e) in
    clamp lo hi (signed s t)

(** val cmp_key : fmt -> z -> z **)

let cmp_key f x =
  let a = Z.coq_land x (Z.ones (Z.sub (width f) (Zpos XH))) in
  if sign_bit f x then Z.opp a else a

(** val cmp : fmt -> bool -> z -> z -> z **)

let cmp f g x y =
  if (||) (is_nan f x) (is_nan f y)
  then if g then Zpos XH else Zneg XH
  else (match Z.compare (cmp_key f x) (cmp_key f y) with
        | Eq -> Z0
        | Lt -> Zneg XH
        | Gt -> Zpos XH)

(** val canon32 : z -> z **)

let canon32 =
  canon binary32

(** val canon64 : z -> z **)

let canon64 =
  canon binary64

(** val fadd32 : z -> z -> z **)

let fadd32 =
  add0 binary32

(** val fsub32 : z -> z -> z **)

let fsub32 =
  sub0 binary32

(** val fmul32 : z -> z -> z **)

let fmul32 =
  mul0 binary32

(** val fdiv32 : z -> z -> z **)

let fdiv32 =
  div binary32

(** val frem32 : z -> z -> z **)

let frem32 =
  rem binary32

(** val fneg32 : z -> z **)

let fneg32 =
  neg binary32

(** val dadd64 : z -> z -> z **)

let dadd64 =
  add0 binary64

(** val dsub64 : z -> z -> z **)

let dsub64 =
  sub0 binary64

(** val dmul64 : z -> z -> z **)

let dmul64 =
  mul0 binary64

(** val ddiv64 : z -> z -> z **)

let ddiv64 =
  div binary64

(** val drem64 : z -> z -> z **)

let drem64 =
  rem binary64

(** val dneg64 : z -> z **)

let dneg64 =
  neg binary64

(** val i2f : z -> z **)

let i2f =
  of_int binary32

(** val i2d : z -> z **)

let i2d =
  of_int binary64

(** val l2f : z -> z **)

let l2f =
  of_int binary32

(** val l2d : z -> z **)

let l2d =
  of_int binary64

(** val f2d : z -> z **)

let f2d =
  convert binary32 binary64

(** val d2f : z -> z **)

let d2f =
  convert binary64 binary32

(** val f2i : z -> z **)

let f2i =
  to_int binary32 iNT_MIN iNT_MAX

(** val f2l : z -> z **)

let f2l =
  to_int binary32 lONG_MIN lONG_MAX

(** val d2i : z -> z **)

let d2i =
  to_int binary64 iNT_MIN iNT_MAX

(** val d2l : z -> z **)

let d2l =
  to_int binary64 lONG_MIN lONG_MAX

(** val fcmp32 : bool -> z -> z -> z **)

let fcmp32 g =
  cmp binary32 g

(** val dcmp64 : bool -> z -> z -> z **)

let dcmp64 g =
  cmp binary64 g

(** val fcmpl : z -> z -> z **)

let fcmpl =
  fcmp32 false

(** val fcmpg : z -> z -> z **)

let fcmpg =
  fcmp32 true

(** val dcmpl : z -> z -> z **)

let dcmpl =
  dcmp64 false

(** val dcmpg : z -> z -> z **)

let dcmpg =
  dcmp64 true

(** val shr_away : z -> z -> z **)

let shr_away m k =
  let q = Z.shiftr m k in
  let r = Z.sub m (Z.shiftl q k) in
  if Z.leb (pow2 (Z.sub k (Zpos XH))) r then Z.add q (Zpos XH) else q

(** val round_mut : z -> fmt -> bool -> z -> z -> z **)

let round_mut mode f s m e =
  if Z.leb m Z0
  then zero_bits f s
  else let q0 = Z.max (Z.sub (Z.add (Z.log2 m) e) f.mbits) (emin_ulp f) in
       let mq0 =
         if Z.leb q0 e
         then Z.shiftl m (Z.sub e q0)
         else if Z.eqb mode (Zpos XH)
              then shr_away m (Z.sub q0 e)
              else shr_rne m (Z.sub q0 e)
       in
       if Z.eqb mq0 (pow2 (Z.add f.mbits (Zpos XH)))
       then let mq = pow2 f.mbits in
            let q = Z.add q0 (Zpos XH) in
            if Z.ltb mq (pow2 f.mbits)
            then if Z.eqb mode (Zpos (XO XH))
                 then zero_bits f s
                 else Z.add (sign_val f s) mq
            else let be = Z.add (Z.sub q (emin_ulp f)) (Zpos XH) in
                 if Z.leb (emax_biased f) be
                 then inf_bits f s
                 else Z.add (Z.add (sign_val f s) (Z.mul be (pow2 f.mbits)))
                        (Z.sub mq (pow2 f.mbits))
       else if Z.ltb mq0 (pow2 f.mbits)
            then if Z.eqb mode (Zpos (XO XH))
                 then zero_bits f s
                 else Z.add (sign_val f s) mq0
            else let be = Z.add (Z.sub q0 (emin_ulp f)) (Zpos XH) in
                 if Z.leb (emax_biased f) be
                 then inf_bits f s
                 else Z.add (Z.add (sign_val f s) (Z.mul be (pow2 f.mbits)))
                        (Z.sub mq0 (pow2 f.mbits))

(** val add_mut : z -> fmt -> z -> z -> z **)

let add_mut mode f x y =
  match decode f x with
  | NaN -> qnan f
  | Inf sx ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> if eqb sx sy then inf_bits f sx else qnan f
     | Fin (_, _, _) -> inf_bits f sx)
  | Fin (sx, mx, ex) ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> inf_bits f sy
     | Fin (sy, my, ey) ->
       let e = Z.min ex ey in
       let t =
         Z.add (signed sx (Z.shiftl mx (Z.sub ex e)))
           (signed sy (Z.shiftl my (Z.sub ey e)))
       in
       if Z.eqb t Z0
       then zero_bits f ((&&) sx sy)
       else round_mut mode f (Z.ltb t Z0) (Z.abs t) e)

(** val mul_mut : z -> fmt -> z -> z -> z **)

let mul_mut mode f x y =
  match decode f x with
  | NaN -> qnan f
  | Inf sx ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> inf_bits f (xorb sx sy)
     | Fin (sy, my, _) ->
       if Z.eqb my Z0 then qnan f else inf_bits f (xorb sx sy))
  | Fin (sx, mx, ex) ->
    (match decode f y with
     | NaN -> qnan f
     | Inf sy -> if Z.eqb mx Z0 then qnan f else inf_bits f (xorb sx sy)
     | Fin (sy, my, ey) ->
       round_mut mode f (xorb sx sy) (Z.mul mx my) (Z.add ex ey))

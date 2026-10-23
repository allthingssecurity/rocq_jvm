(** * CaseInsensitiveMap.put (fix 27aeb4f860d9): the tail shared by all paths that insert
    a new key, and the path that grows the slot arrays with Arrays.copyOf. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimPut CimTac.
Import ListNotations.
Open Scope Z_scope.

Definition ARR := "java/util/Arrays"%string.
Definition copyO_desc := "([Ljava/lang/Object;I)[Ljava/lang/Object;"%string.
Definition copyI_desc := "([II)[I"%string.
Lemma rf_copyO : resolve_full cp ARR "copyOf" copyO_desc = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_copyI : resolve_full cp ARR "copyOf" copyI_desc = None. Proof. vm_compute. reflexivity. Qed.
Lemma err_arr : forall st, erroneous cp 64 st ARR = false. Proof. intros. vm_compute. reflexivity. Qed.
Lemma in_arr : forall st, init_needed cp 64 st ARR = None. Proof. intros. vm_compute. reflexivity. Qed.

Definition grow (t : jtype) (es : list value) (n : Z) : list value := es ++ repeat (default_of t) (Z.to_nat (n - slen_v es)).

Lemma grow_length : forall t es n, slen_v es <= n -> Z.of_nat (length (grow t es n)) = n.
Proof. intros t es n H. unfold grow, slen_v in *. rewrite app_length, repeat_length. lia. Qed.

Section Put2.
Variable e : jenv.

Lemma m_copyO : forall s a t es n, ms_heap s a = Some (OArr t es) -> 0 <= n <= MAX_ARRAY -> slen_v es < n ->
  jdk_model cp e ARR "copyOf" copyO_desc [VRef a; VInt n] s =
  MOk (Some (VRef (ms_next s))) (snd (alloc s (OArr t (grow t es n)))).
Proof.
  intros s a t es n H Hn Hl. unfold jdk_model. cbv -[ms_heap alloc slen_v grow app repeat Z.ltb Z.leb].
  rewrite H.
  replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (1048576 <? n) with false by (symmetry; apply Z.ltb_ge; unfold MAX_ARRAY in Hn; lia).
  replace (n <=? slen_v es) with false by (symmetry; apply Z.leb_gt; lia).
  unfold grow. reflexivity.
Qed.

Lemma m_copyI : forall s a es n, ms_heap s a = Some (OArr TInt es) -> 0 <= n <= MAX_ARRAY -> slen_v es < n ->
  jdk_model cp e ARR "copyOf" copyI_desc [VRef a; VInt n] s =
  MOk (Some (VRef (ms_next s))) (snd (alloc s (OArr TInt (grow TInt es n)))).
Proof.
  intros s a es n H Hn Hl. unfold jdk_model. cbv -[ms_heap alloc slen_v grow app repeat Z.ltb Z.leb].
  rewrite H.
  replace (n <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (1048576 <? n) with false by (symmetry; apply Z.ltb_ge; unfold MAX_ARRAY in Hn; lia).
  replace (n <=? slen_v es) with false by (symmetry; apply Z.leb_gt; lia).
  unfold grow. reflexivity.
Qed.

Ltac STOREV H1 H2 := eapply returns_step;
  [ first [ eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact H1 | reflexivity ]
          | eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact H1 | hp
                                      | reflexivity | exact H2 | reflexivity ] ]
  | try nz ].

(** From pc 157 (a free slot exists): the insertion itself. *)
Lemma put_tail : forall h n sts ini lk m k ku v hsh x5 tA kA vA cA sz u thr af tbl ks vs cn pw i0,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) -> tA <> cA ->
  h k = Some (OStr ku) ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  length vs = length ks -> length cn = length ks -> Z.of_nat (length ks) <= INT_MAX ->
  nth_z tbl (hsh mod 2 ^ pw) = Some (VInt i0) ->
  0 <= sz < INT_MAX -> 0 <= u < Z.of_nat (length ks) -> vok h v ->
  (match v with VRef vl => vl <> m /\ vl <> kA | _ => True end) ->
  (match x5 with VTop | VInt _ => true | _ => false end) = true ->
  let b := hsh mod 2 ^ pw in
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
     ms_frames := [set_frame (put_frame m k v) (mkframe 157 nil [VRef m; VRef k; v; VInt hsh; VInt (-1); x5; VTop])] |}
    (Some VNull)
    (fun s' => ms_heap s' m = Some (OObj CIM (cim_fields tA kA vA cA (sz + 1) (u + 1) thr af)) /\
               ms_heap s' kA = Some (OArr (TRef STR) (set_nth_z ks u (VRef k))) /\
               ms_heap s' vA = Some (OArr (TRef OBJ) (set_nth_z vs u v)) /\
               ms_heap s' cA = Some (OArr TInt (set_nth_z cn u (VInt i0))) /\
               ms_heap s' tA = Some (OArr TInt (set_nth_z tbl b (VInt u))) /\
               (forall y, y <> m -> y <> kA -> y <> vA -> y <> cA -> y <> tA -> ms_heap s' y = h y) /\
               ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku v hsh x5 tA kA vA cA sz u thr af tbl ks vs cn pw i0
         Hm HtA HkA HvA HcA Htc Hk Hlen Hpw Hvl Hcl HK2 Hb Hsz Hu Hv Hvd Hx5 b.
  assert (Hv' : (match v with VNull | VRef _ => true | _ => false end) = true) by (destruct v; try contradiction; reflexivity).
  assert (Hc2 : cat2 v = false) by (destruct v; try discriminate Hv'; reflexivity).
  assert (Hs2 : slots v = 1) by (destruct v; try discriminate Hv'; reflexivity).
  assert (Hu1 : wrap 32 (u + 1) = u + 1) by (apply wrap_id; [lia | unfold in_range, INT_MAX in *; cbn; lia]).
  assert (Hs1 : wrap 32 (sz + 1) = sz + 1) by (apply wrap_id; [lia | unfold in_range, INT_MAX in *; cbn; lia]).
  assert (Hbk : wrap 32 (Z.land hsh (wrap 32 (2 ^ pw - 1))) = b) by (apply bucket_eq; lia).
  assert (Hbb : 0 <= b < Z.of_nat (length tbl)) by (rewrite Hlen; apply Z.mod_pos_bound; lia).
  assert (Hub : ((u <? 0) || (Z.of_nat (length ks) <=? u)) = false) by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
  assert (Hubv : ((u <? 0) || (Z.of_nat (length vs) <=? u)) = false) by (rewrite Hvl; exact Hub).
  assert (Hubc : ((u <? 0) || (Z.of_nat (length cn) <=? u)) = false) by (rewrite Hcl; exact Hub).
  assert (Hbt : ((b <? 0) || (Z.of_nat (length tbl) <=? b)) = false) by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
  assert (Hmt : m <> tA) by (intro E; subst; rewrite Hm in HtA; discriminate).
  assert (Hmk : m <> kA) by (intro E; subst; rewrite Hm in HkA; discriminate).
  assert (Hmv : m <> vA) by (intro E; subst; rewrite Hm in HvA; discriminate).
  assert (Hmc : m <> cA) by (intro E; subst; rewrite Hm in HcA; discriminate).
  assert (Hkt : kA <> tA) by (intro E; subst; rewrite HkA in HtA; discriminate).
  assert (Hkv : kA <> vA) by (intro E; subst; rewrite HkA in HvA; discriminate).
  assert (Hkc : kA <> cA) by (intro E; subst; rewrite HkA in HcA; discriminate).
  assert (Hvt : vA <> tA) by (intro E; subst; rewrite HvA in HtA; discriminate).
  assert (Hvc : vA <> cA) by (intro E; subst; rewrite HvA in HcA; discriminate).
  assert (Hkk : k <> kA) by (intro E; subst; rewrite Hk in HkA; discriminate).
  assert (Hkm : k <> m) by (intro E; subst; rewrite Hk in Hm; discriminate).
  assert (Hkt2 : k <> tA) by (intro E; subst; rewrite Hk in HtA; discriminate).
  assert (Hkv2 : k <> vA) by (intro E; subst; rewrite Hk in HvA; discriminate).
  assert (Hkc2 : k <> cA) by (intro E; subst; rewrite Hk in HcA; discriminate).
  destruct x5 as [z5|z5|z5|z5| |z5|]; try discriminate Hx5;
  destruct v as [z|z|z|z| |vl|]; try contradiction;
  try (destruct Hv as (o & Ho & Ha); destruct Hvd as [Hvd1 Hvd2]).
  all: lstep; lstep; GET; lstep; lstep; lstep; try rewrite Hu1; PUT; lstep.
  all: lstep; GET; lstep; lstep.
  all: eapply returns_step;
    [ eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hub | hp
                                | reflexivity | apply asg_str | reflexivity ] | try nz ].
  all: lstep; GET; lstep; lstep.
  all: STOREV Hubv Ha.
  all: lstep; lstep; GET; ALEN; lstep; lstep; lstep; try rewrite Hlen; try rewrite Hbk; lstep.
  all: lstep; GET; lstep; lstep; GET; lstep.
  all: eapply returns_step;
    [ eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hbt | exact Hb | reflexivity ]
    | try nz ].
  all: eapply returns_step;
    [ eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hubc | reflexivity ]
    | try nz ].
  all: lstep; GET; lstep; lstep.
  all: eapply returns_step;
    [ eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hbt | reflexivity ]
    | try nz ].
  all: lstep; lstep; GET; lstep; lstep; try rewrite Hs1; PUT; lstep.
  all: eapply returns_now;
    [ eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ] | ].
  all: cbn [with_frames ms_heap ms_next ms_statics ms_inited].
  all: refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj eq_refl (conj eq_refl eq_refl)))))))).
  all: try (intros y Hy1 Hy2 Hy3 Hy4 Hy5).
  all: repeat first [ rewrite upd_same | rewrite upd_other by congruence ]; reflexivity.
Qed.


Ltac lstep2 := eapply returns_step;
  [ eapply mstep_local; [ reflexivity | reflexivity | reflexivity
                        | cbn -[wrap i2c Z.mul iinc cat2 upd Z.pow Z.modulo Z.quot Z.shiftr]; use_hyps;
                          cbn -[wrap i2c Z.mul iinc upd Z.pow Z.modulo Z.quot Z.shiftr]; reflexivity
                        | cbn -[cat2 slots upd]; use_hyps; reflexivity ]
  | try nz ].

Lemma asg_strarr : forall es, assignable cp 64 (runtime_type (OArr (TRef STR) es)) "[Ljava/lang/String;" = Some true.
Proof. reflexivity. Qed.

(** The key is new, no resize is due, every slot is used and more than half of them hold
    keys: the three slot arrays grow by half (Arrays.copyOf), then the key is inserted. *)
Theorem put_grow : forall h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) ->
  tA <> cA ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  length vs = length ks -> length cn = length ks ->
  2 <= Z.of_nat (length ks) -> Z.of_nat (length ks) + Z.of_nat (length ks) / 2 <= MAX_ARRAY ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  nth_z tbl (cih_spec e ku mod 2 ^ pw) = Some (VInt i0) ->
  fi_walk e h ks cn ku i0 (S (length ks)) = Some (-1) ->
  0 <= sz < thr -> thr <= INT_MAX -> u = Z.of_nat (length ks) -> Z.of_nat (length ks) / 2 < sz -> vok h v ->
  (match v with VRef vl => vl <> m /\ vl <> kA /\ vl < n | _ => True end) ->
  m < n -> k < n -> tA < n -> kA < n -> vA < n -> cA < n ->
  let K' := Z.of_nat (length ks) + Z.of_nat (length ks) / 2 in
  let b := cih_spec e ku mod 2 ^ pw in
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some VNull)
    (fun s' => ms_heap s' m = Some (OObj CIM (cim_fields tA n (n + 1) (n + 2) (sz + 1) (u + 1) thr af)) /\
               ms_heap s' n = Some (OArr (TRef STR) (set_nth_z (grow (TRef STR) ks K') u (VRef k))) /\
               ms_heap s' (n + 1) = Some (OArr (TRef OBJ) (set_nth_z (grow (TRef OBJ) vs K') u v)) /\
               ms_heap s' (n + 2) = Some (OArr TInt (set_nth_z (grow TInt cn K') u (VInt i0))) /\
               ms_heap s' tA = Some (OArr TInt (set_nth_z tbl b (VInt u))) /\
               (forall y, y < n -> y <> m -> y <> tA -> ms_heap s' y = h y) /\
               ms_next s' = n + 3 /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0
         Hm HtA HkA HvA HcA Htc Hk Hmax Hlen Hpw Hvl Hcl HK1 HK2 He Hi HK Hb Hw Hsz Hthr Hu Hhalf Hv Hvd
         Hnm Hnk Hnt Hnka Hnv Hnc K' b.
  subst u.
  assert (Hv' : (match v with VNull | VRef _ => true | _ => false end) = true) by (destruct v; try contradiction; reflexivity).
  assert (Hc2 : cat2 v = false) by (destruct v; try discriminate Hv'; reflexivity).
  assert (Hs2 : slots v = 1) by (destruct v; try discriminate Hv'; reflexivity).
  change MAX_ARRAY with 1048576 in HK2.
  assert (Hd : 0 <= (Z.of_nat (length ks)) / 2 <= (Z.of_nat (length ks))) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hq : wrap 32 (Z.quot (Z.of_nat (length ks)) 2) = (Z.of_nat (length ks)) / 2)
    by (rewrite Z.quot_div_nonneg by lia; apply wrap_id; [lia | unfold in_range, MAX_ARRAY in *; cbn; lia]).
  assert (Hsh : wrap 32 (Z.shiftr (Z.of_nat (length ks)) 1) = (Z.of_nat (length ks)) / 2)
    by (rewrite Z.shiftr_div_pow2 by lia; apply wrap_id; [lia | unfold in_range, MAX_ARRAY in *; cbn; lia]).
  assert (HK' : wrap 32 ((Z.of_nat (length ks)) + (Z.of_nat (length ks)) / 2) = K') by (apply wrap_id; [lia | unfold K', in_range, MAX_ARRAY in *; cbn; lia]).
  assert (HKr : 0 <= K' <= MAX_ARRAY) by (unfold K'; change MAX_ARRAY with 1048576; clear -HK2 HK1; Z.div_mod_to_equations; lia).
  assert (HKs : slen_v ks < K') by (unfold K', slen_v; clear -HK1; Z.div_mod_to_equations; lia).
  assert (HKv : slen_v vs < K') by (unfold K', slen_v; rewrite Hvl; clear -HK1; Z.div_mod_to_equations; lia).
  assert (HKc : slen_v cn < K') by (unfold K', slen_v; rewrite Hcl; clear -HK1; Z.div_mod_to_equations; lia).
  assert (E1 : (sz <? thr) = true) by (apply Z.ltb_lt; lia).
  assert (E2 : (Z.of_nat (length ks) <? Z.of_nat (length ks)) = false) by (apply Z.ltb_ge; lia).
  assert (E3 : ((Z.of_nat (length ks)) / 2 <? sz) = true) by (apply Z.ltb_lt; lia).
  assert (Hmt : m <> tA) by (intro E; subst; rewrite Hm in HtA; discriminate).
  assert (Hmk : m <> kA) by (intro E; subst; rewrite Hm in HkA; discriminate).
  assert (Hmv : m <> vA) by (intro E; subst; rewrite Hm in HvA; discriminate).
  assert (Hmc : m <> cA) by (intro E; subst; rewrite Hm in HcA; discriminate).
  assert (Hkm : k <> m) by (intro E; subst; rewrite Hk in Hm; discriminate).
  eapply put_prefix; try eassumption.
  lstep2. lstep2. lstep2.
  lstep2. GET. lstep2. GET. lstep2.
  (* 67: no free slot *)
  lstep2. GET. lstep2. GET. ALEN. lstep2.
  (* 79: size > keys.length / 2: grow *)
  lstep2. GET. lstep2. GET. ALEN. lstep2. lstep2. lstep2.
  (* 100: newCap = keys.length + (keys.length >> 1) *)
  lstep2. GET. ALEN. lstep2. GET. ALEN. lstep2. lstep2. lstep2. lstep2.
  (* 115: keys = Arrays.copyOf(keys, newCap) *)
  pose proof Hd as Hd0. pose proof HK2 as HK20.
  lstep2. lstep2. GET. lstep2.
  eapply returns_step.
  { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
    eapply do_invoke_static_model;
      [ apply err_arr | apply in_arr | exact rf_copyO
      | unfold mdl; apply m_copyO; [ hp | exact HKr | exact HKs ] | reflexivity ]. }
  nz.
  eapply returns_step.
  { eapply mstep_checkcast_ref; [ reflexivity | reflexivity | reflexivity | hp | apply asg_strarr | reflexivity ]. }
  nz. PUT.
  (* 131: values = Arrays.copyOf(values, newCap) *)
  lstep2. lstep2. GET. lstep2.
  eapply returns_step.
  { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
    eapply do_invoke_static_model;
      [ apply err_arr | apply in_arr | exact rf_copyO
      | unfold mdl; apply m_copyO; [ hp | exact HKr | exact HKv ] | reflexivity ]. }
  nz. PUT.
  (* 144: chainNext = Arrays.copyOf(chainNext, newCap) *)
  lstep2. lstep2. GET. lstep2.
  eapply returns_step.
  { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
    eapply do_invoke_static_model;
      [ apply err_arr | apply in_arr | exact rf_copyI
      | unfold mdl; apply m_copyI; [ hp | exact HKr | exact HKc ] | reflexivity ]. }
  nz. PUT.
  assert (En2 : n + 1 + 1 = n + 2) by lia. assert (En3 : n + 1 + 1 + 1 = n + 3) by lia.
  rewrite En3, En2.
  match goal with |- returns _ _ {| ms_heap := ?H1 |} _ _ => set (h1 := H1) end.
  assert (Hgk := grow_length (TRef STR) ks K' ltac:(lia)).
  assert (Hgv := grow_length (TRef OBJ) vs K' ltac:(lia)).
  assert (Hgc := grow_length TInt cn K' ltac:(lia)).
  eapply returns_weaken.
  { apply (put_tail h1 (n + 3) sts ini lk m k ku v (cih_spec e ku) (VInt K') tA n (n + 1) (n + 2) sz (Z.of_nat (length ks)) thr af
             tbl (grow (TRef STR) ks K') (grow (TRef OBJ) vs K') (grow TInt cn K') pw i0); unfold h1.
    - hp.
    - hp.
    - hp.
    - hp.
    - hp.
    - lia.
    - hp.
    - exact Hlen.
    - exact Hpw.
    - apply Nat2Z.inj. rewrite Hgv, Hgk. reflexivity.
    - apply Nat2Z.inj. rewrite Hgc, Hgk. reflexivity.
    - rewrite Hgk. unfold MAX_ARRAY in *; cbn in *; lia.
    - exact Hb.
    - lia.
    - rewrite Hgk. unfold K'. clear -HK1. Z.div_mod_to_equations. lia.
    - destruct v as [z|z|z|z| |vl|]; try contradiction; [exact I|].
      destruct Hv as (o & Ho & Ha). destruct Hvd as (Hv1 & Hv2 & Hv3). exists o. split; [|exact Ha].
      repeat rewrite upd_other by lia. exact Ho.
    - destruct v as [z|z|z|z| |vl|]; try exact I. destruct Hvd as (Hv1 & Hv2 & Hv3). split; lia.
    - reflexivity. }
  cbv zeta. intros s' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  refine (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj _ (conj P7 (conj P8 P9)))))))).
  intros y Hy Hym Hyt. rewrite P6 by lia. unfold h1. repeat rewrite upd_other by lia. reflexivity.
Qed.

End Put2.

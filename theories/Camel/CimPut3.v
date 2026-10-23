(** * CaseInsensitiveMap.put (fix 27aeb4f860d9): the path through compactRemovedSlots. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimPut CimTac CimPut2 CimCompact.
Import ListNotations.
Open Scope Z_scope.

Lemma fill_null_length : forall es f t, 0 <= f <= t -> t <= Z.of_nat (length es) ->
  length (fill_null es f t) = length es.
Proof.
  intros es f t Hf Ht. unfold fill_null. rewrite !app_length, repeat_length, firstn_length, skipn_length. lia.
Qed.

Section Put3.
Variable e : jenv.

Ltac lstep2 := eapply returns_step;
  [ eapply mstep_local; [ reflexivity | reflexivity | reflexivity
                        | cbn -[wrap i2c Z.mul iinc cat2 upd Z.pow Z.modulo Z.quot Z.shiftr]; use_hyps;
                          cbn -[wrap i2c Z.mul iinc upd Z.pow Z.modulo Z.quot Z.shiftr]; reflexivity
                        | cbn -[cat2 slots upd]; use_hyps; reflexivity ]
  | try nz ].

(** The key is new, no resize is due, every slot is used and at most half of them hold
    keys: the removed slots are compacted away, then the key is inserted. *)
Theorem put_compact : forall h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0
                             n' ni tbl' ks' vs' cn' i0',
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) ->
  tA <> cA ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 -> 2 ^ pw <= MAX_ARRAY ->
  length vs = length ks -> length cn = length ks -> Z.of_nat (length ks) <= MAX_ARRAY ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  nth_z tbl (cih_spec e ku mod 2 ^ pw) = Some (VInt i0) ->
  fi_walk e h ks cn ku i0 (S (length ks)) = Some (-1) ->
  0 <= sz < thr -> thr <= INT_MAX -> u = Z.of_nat (length ks) -> sz <= Z.of_nat (length ks) / 2 -> vok h v ->
  (match v with VRef vl => vl <> m /\ vl <> kA /\ vl <> tA /\ vl <> vA /\ vl <> cA /\ vl < n | _ => True end) ->
  m < n -> k < n -> tA < n -> kA < n -> vA < n -> cA < n ->
  (* what compactRemovedSlots computes *)
  c1 ks 0 (Z.to_nat u) 0 (repeat (VInt 0) (Z.to_nat u)) = Some (n', ni) ->
  c2 ni tbl 0 (Z.to_nat (Z.of_nat (length tbl))) = Some tbl' ->
  c3 h kA vA cA n tA ni 0 (Z.to_nat u) ks vs cn = Some (ks', vs', cn') ->
  0 <= n' < u -> length ks' = length ks -> length vs' = length ks -> length cn' = length ks ->
  length tbl' = length tbl ->
  nth_z tbl' (cih_spec e ku mod 2 ^ pw) = Some (VInt i0') ->
  let b := cih_spec e ku mod 2 ^ pw in
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some VNull)
    (fun s' => ms_heap s' m = Some (OObj CIM (cim_fields tA kA vA cA (sz + 1) (n' + 1) thr af)) /\
               ms_heap s' kA = Some (OArr (TRef STR) (set_nth_z (fill_null ks' n' u) n' (VRef k))) /\
               ms_heap s' vA = Some (OArr (TRef OBJ) (set_nth_z (fill_null vs' n' u) n' v)) /\
               ms_heap s' cA = Some (OArr TInt (set_nth_z cn' n' (VInt i0'))) /\
               ms_heap s' tA = Some (OArr TInt (set_nth_z tbl' b (VInt n'))) /\
               (forall y, y < n -> y <> m -> y <> kA -> y <> vA -> y <> cA -> y <> tA -> ms_heap s' y = h y) /\
               ms_next s' = n + 1 /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0 n' ni tbl' ks' vs' cn' i0'
         Hm HtA HkA HvA HcA Htc Hk Hmax Hlen Hpw Hpw2 Hvl Hcl HK2 He Hi HK Hb Hw Hsz Hthr Hu Hhalf Hv Hvd
         Hnm Hnk Hnt Hnka Hnv Hnc Hc1 Hc2 Hc3 Hn' Hlk' Hlv' Hlc' Hlt' Hb' b.
  subst u.
  assert (Hv' : (match v with VNull | VRef _ => true | _ => false end) = true) by (destruct v; try contradiction; reflexivity).
  assert (Hc2v : cat2 v = false) by (destruct v; try discriminate Hv'; reflexivity).
  assert (Hs2 : slots v = 1) by (destruct v; try discriminate Hv'; reflexivity).
  assert (Hd : 0 <= Z.of_nat (length ks) / 2 <= Z.of_nat (length ks)) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (Hq : wrap 32 (Z.quot (Z.of_nat (length ks)) 2) = Z.of_nat (length ks) / 2)
    by (rewrite Z.quot_div_nonneg by lia; apply wrap_id; [lia | unfold in_range, MAX_ARRAY in *; cbn; lia]).
  assert (E1 : (sz <? thr) = true) by (apply Z.ltb_lt; lia).
  assert (E2 : (Z.of_nat (length ks) <? Z.of_nat (length ks)) = false) by (apply Z.ltb_ge; lia).
  assert (E3 : (Z.of_nat (length ks) / 2 <? sz) = false) by (apply Z.ltb_ge; lia).
  assert (Hmt : m <> tA) by (intro E; subst; rewrite Hm in HtA; discriminate).
  assert (Hmk : m <> kA) by (intro E; subst; rewrite Hm in HkA; discriminate).
  assert (Hmv : m <> vA) by (intro E; subst; rewrite Hm in HvA; discriminate).
  assert (Hmc : m <> cA) by (intro E; subst; rewrite Hm in HcA; discriminate).
  assert (Hkm : k <> m) by (intro E; subst; rewrite Hk in Hm; discriminate).
  assert (Hkn : k <> n) by (clear -Hnk; lia).
  assert (Hkt : k <> tA) by (intro E; subst; rewrite Hk in HtA; discriminate).
  assert (Hkk : k <> kA) by (intro E; subst; rewrite Hk in HkA; discriminate).
  assert (Hkv : k <> vA) by (intro E; subst; rewrite Hk in HvA; discriminate).
  assert (Hkc : k <> cA) by (intro E; subst; rewrite Hk in HcA; discriminate).
  eapply put_prefix; try eassumption.
  lstep2. lstep2. lstep2.
  lstep2. GET. lstep2. GET. lstep2.
  lstep2. GET. lstep2. GET. ALEN. lstep2.
  lstep2. GET. lstep2. GET. ALEN. lstep2. lstep2. lstep2.
  (* 93: compactRemovedSlots() *)
  lstep2.
  eapply (call_compact e); try eassumption.
  - reflexivity.
  - reflexivity.
  - clear -HK2. unfold MAX_ARRAY in *; lia.
  - rewrite Hlen. exact Hpw2.
  - clear -Hn'. lia.
  - rewrite Hlk'. lia.
  - rewrite Hlv'. lia.
  - intros h' H1 H2 H3 H4 H5 H6 H7.
    nz. lstep2.
    assert (Hlfk : length (fill_null ks' n' (Z.of_nat (length ks))) = length ks)
      by (rewrite fill_null_length; [exact Hlk' | clear -Hn'; lia | rewrite Hlk'; lia]).
    assert (Hlfv : length (fill_null vs' n' (Z.of_nat (length ks))) = length ks)
      by (rewrite fill_null_length; [exact Hlv' | clear -Hn'; lia | rewrite Hlv'; lia]).
    eapply returns_weaken.
    { apply (put_tail e h' (n + 1) sts ini lk m k ku v (cih_spec e ku) VTop tA kA vA cA sz n' thr af
               tbl' (fill_null ks' n' (Z.of_nat (length ks))) (fill_null vs' n' (Z.of_nat (length ks))) cn' pw i0').
      - exact H1.
      - exact H3.
      - exact H4.
      - exact H5.
      - exact H6.
      - exact Htc.
      - rewrite H7 by assumption. exact Hk.
      - rewrite Hlt'. exact Hlen.
      - exact Hpw.
      - rewrite Hlfv, Hlfk. reflexivity.
      - rewrite Hlc', Hlfk. reflexivity.
      - rewrite Hlfk. clear -HK2. unfold MAX_ARRAY in *; cbn in *; lia.
      - exact Hb'.
      - clear -Hsz Hthr. lia.
      - rewrite Hlfk. clear -Hn'. lia.
      - destruct v as [z|z|z|z| |vl|]; try contradiction; [exact I|].
        destruct Hv as (o & Ho & Ha). destruct Hvd as (V1 & V2 & V3 & V4 & V5 & V6). exists o. split; [|exact Ha].
        assert (V7 : vl <> n) by (clear -V6; lia).
        rewrite H7 by assumption. exact Ho.
      - destruct v as [z|z|z|z| |vl|]; try exact I. destruct Hvd as (V1 & V2 & _). split; assumption.
      - reflexivity. }
    cbv zeta. intros s' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    refine (conj P1 (conj P2 (conj P3 (conj P4 (conj P5 (conj _ (conj P7 (conj P8 P9)))))))).
    intros y Hy Y1 Y2 Y3 Y4 Y5. rewrite P6 by assumption.
    assert (Y6 : y <> n) by (clear -Hy; lia). apply H7; assumption.
Qed.

End Put3.

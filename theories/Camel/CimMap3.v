(** * CaseInsensitiveMap (fix): put of a new key through compaction and through growth,
      at the level of the map. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimPut CimPut2 CimPut3 CimRemove CimCompact CimAbs CimAbs2 CimMap CimMap2.
Import ListNotations.
Open Scope Z_scope.

(** ** List facts *)

Lemma Lv_full : forall ks f i, 0 <= i -> (forall p, i <= p < i + Z.of_nat f -> nonnull (nth_z ks p) = true) ->
  Lv ks i f = map Z.of_nat (seq (Z.to_nat i) f).
Proof.
  intros ks f. induction f as [|f IH]; intros i Hi H; [reflexivity|].
  rewrite Lv_S. rewrite (H i ltac:(lia)). cbn [seq map]. rewrite Z2Nat.id by lia. f_equal.
  rewrite IH; [| lia | intros p Hp; apply H; lia].
  replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. reflexivity.
Qed.

Lemma Lv_ext : forall ks1 ks2 f i, (forall p, i <= p < i + Z.of_nat f -> nth_z ks1 p = nth_z ks2 p) ->
  Lv ks1 i f = Lv ks2 i f.
Proof.
  intros ks1 ks2 f. induction f as [|f IH]; intros i H; [reflexivity|].
  rewrite !Lv_S. rewrite (H i ltac:(lia)). rewrite IH by (intros p Hp; apply H; lia). reflexivity.
Qed.

Lemma key_at_nth : forall h ks1 ks s1 s, nth_z ks1 s1 = nth_z ks s -> key_at h ks1 s1 = key_at h ks s.
Proof. intros h ks1 ks s1 s E. unfold key_at. rewrite E. reflexivity. Qed.

Lemma key_some_ref : forall h ks s u, key_at h ks s = Some u -> exists kl, nth_z ks s = Some (VRef kl) /\ h kl = Some (OStr u).
Proof.
  intros h ks s u H. unfold key_at in H. destruct (nth_z ks s) as [[z|z|z|z| |kl|]|]; try discriminate.
  destruct (h kl) as [[| | u' | | |]|] eqn:E; try discriminate. injection H as <-. eauto.
Qed.

Lemma nth_z_repeat : forall {A} (x : A) f i, 0 <= i < Z.of_nat f -> nth_z (repeat x f) i = Some x.
Proof.
  intros A x f. induction f as [|f IH]; intros i Hi; cbn in *; [lia|].
  destruct (Z.eqb_spec i 0); [reflexivity|]. apply IH. lia.
Qed.

Lemma chain_transfer : forall cn cn2 i L, chain cn i L -> (forall s, In s L -> nth_z cn2 s = nth_z cn s) -> chain cn2 i L.
Proof.
  intros cn cn2 i L H. induction H as [|i j L Hi Hn Hc IH]; intros E; [constructor|].
  econstructor; [exact Hi | rewrite E by (left; reflexivity); exact Hn | apply IH; intros s Hs; apply E; right; exact Hs].
Qed.

Lemma entries_renum : forall ks1 vs1 ks vs S o,
  (forall j p, nth_error S j = Some p -> nth_z ks1 (Z.of_nat (o + j)) = nth_z ks p /\ nth_z vs1 (Z.of_nat (o + j)) = nth_z vs p) ->
  (forall p, In p S -> 0 <= p < Z.of_nat (length vs)) ->
  entries ks1 vs1 (map Z.of_nat (seq o (length S))) = entries ks vs S.
Proof.
  intros ks1 vs1 ks vs S. induction S as [|p S IH]; intros o Hc Hr; [reflexivity|].
  unfold entries in IH |- *. cbn [length seq map]. f_equal.
  - destruct (Hc 0%nat p eq_refl) as (C1 & C2). rewrite Nat.add_0_r in C1, C2. f_equal.
    + unfold key_ref. rewrite C1. reflexivity.
    + destruct (nth_z_exists vs p (Hr p (or_introl eq_refl))) as (x & Ex).
      rewrite (nth_z_nth vs p x VNull Ex). apply nth_z_nth. rewrite C2. exact Ex.
  - apply IH.
    + intros j p' E. replace (Datatypes.S o + j)%nat with (o + Datatypes.S j)%nat by lia. apply (Hc (Datatypes.S j) p'). exact E.
    + intros p' Hp'. apply Hr. right. exact Hp'.
Qed.

Lemma vok_vok_b : forall h v, vok h v -> vok_b h v = true.
Proof.
  intros h v H. destruct v as [z|z|z|z| |l|]; try contradiction; [reflexivity|].
  destruct H as (o & Ho & Ha). unfold vok_b. rewrite Ho, Ha. reflexivity.
Qed.

Lemma not_in4_ref : forall a b c d t l, l <> a -> l <> b -> l <> c -> l <> d -> l <> t -> not_in4 a b c d t (VRef l) = true.
Proof.
  intros a b c d t l H1 H2 H3 H4 H5. unfold not_in4.
  rewrite (proj2 (Z.eqb_neq l a) H1), (proj2 (Z.eqb_neq l b) H2), (proj2 (Z.eqb_neq l c) H3),
          (proj2 (Z.eqb_neq l d) H4), (proj2 (Z.eqb_neq l t) H5). reflexivity.
Qed.

Section Map3.
Variable e : jenv.
Variable good : list Z -> Prop.
Hypothesis eq_sym : forall a b, good a -> good b -> eqic e a b = eqic e b a.
Hypothesis eq_trans : forall a b c, good a -> good b -> good c -> eqic e a b = true -> eqic e b c = true -> eqic e a c = true.
Hypothesis eq_hash : forall a b, good a -> good b -> eqic e a b = true -> cih_spec e a = cih_spec e b.

(** ** The representation, by its lists *)

Definition rl (h : heap) (tbl ks vs cn : list value) (pw u : Z) (K : nat) : Prop :=
  Z.of_nat (length tbl) = 2 ^ pw /\ 0 <= pw <= 20 /\
  length ks = K /\ length vs = K /\ length cn = K /\ Z.of_nat K <= MAX_ARRAY /\
  0 <= u <= Z.of_nat K /\ slots_ok ks 0 (Z.to_nat u) /\
  (forall q, u <= q < Z.of_nat K -> nth_z ks q = Some VNull) /\
  tbl_ok e h ks cn tbl pw (Lv ks 0 (Z.to_nat u)) /\ keys_ok e good h ks (Lv ks 0 (Z.to_nat u)) /\ allrefs vs.

Lemma rep_intro : forall h m A K thr tA kA vA cA sz u af tbl ks vs cn pw,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) -> h tA = Some (OArr TInt tbl) ->
  h kA = Some (OArr (TRef STR) ks) -> h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) -> tA <> cA ->
  rl h tbl ks vs cn pw u K -> sz = Z.of_nat (length (Lv ks 0 (Z.to_nat u))) -> A = entries ks vs (Lv ks 0 (Z.to_nat u)) ->
  cim_rep e good h m A K thr.
Proof.
  intros h m A K thr tA kA vA cA sz u af tbl ks vs cn pw Hm HtA HkA HvA HcA Htc
         (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) Hsz HA.
  exists tA, kA, vA, cA, sz, u, af, tbl, ks, vs, cn, pw.
  exact (conj Hm (conj HtA (conj HkA (conj HvA (conj HcA (conj Htc (conj R1 (conj R2 (conj R3 (conj R4 (conj R5
         (conj R6 (conj R7 (conj R8 (conj R9 (conj Hsz (conj R10 (conj R11 (conj R12 HA))))))))))))))))))).
Qed.

Lemma rep_elim : forall h m A K thr, cim_rep e good h m A K thr ->
  exists tA kA vA cA sz u af tbl ks vs cn pw,
    h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) /\ h tA = Some (OArr TInt tbl) /\
    h kA = Some (OArr (TRef STR) ks) /\ h vA = Some (OArr (TRef OBJ) vs) /\ h cA = Some (OArr TInt cn) /\ tA <> cA /\
    rl h tbl ks vs cn pw u K /\ sz = Z.of_nat (length (Lv ks 0 (Z.to_nat u))) /\ A = entries ks vs (Lv ks 0 (Z.to_nat u)).
Proof.
  intros h m A K thr (tA & kA & vA & cA & sz & u & af & tbl & ks & vs & cn & pw &
                      Hm & HtA & HkA & HvA & HcA & Htc & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & Hsz & R10 & R11 & R12 & HA).
  exists tA, kA, vA, cA, sz, u, af, tbl, ks, vs, cn, pw.
  refine (conj Hm (conj HtA (conj HkA (conj HvA (conj HcA (conj Htc (conj _ (conj Hsz HA)))))))).
  exact (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 (conj R10 (conj R11 R12))))))))))).
Qed.

Lemma rl_same : forall h h' tbl ks vs cn pw u K, same_strings h h' -> rl h tbl ks vs cn pw u K -> rl h' tbl ks vs cn pw u K.
Proof.
  intros h h' tbl ks vs cn pw u K Hs (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
  refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 (conj _ (conj _ R12))))))))))).
  - apply (tbl_ok_same e h h'); assumption.
  - apply (keys_ok_same e good h h'); assumption.
Qed.

(** Putting a new entry into the first unused slot [u]. *)
Lemma rl_insert : forall h tbl ks vs cn pw u K k ku v i0,
  rl h tbl ks vs cn pw u K -> u < Z.of_nat K -> h k = Some (OStr ku) -> good ku ->
  (forall s, ~ holds e h ks (Lv ks 0 (Z.to_nat u)) ku s) ->
  nth_z tbl (bucket e ku pw) = Some (VInt i0) ->
  (match v with VNull | VRef _ => true | _ => false end) = true ->
  rl h (set_nth_z tbl (bucket e ku pw) (VInt u)) (set_nth_z ks u (VRef k)) (set_nth_z vs u v) (set_nth_z cn u (VInt i0)) pw (u + 1) K /\
  Lv (set_nth_z ks u (VRef k)) 0 (Z.to_nat (u + 1)) = app (Lv ks 0 (Z.to_nat u)) [u] /\
  entries (set_nth_z ks u (VRef k)) (set_nth_z vs u v) (app (Lv ks 0 (Z.to_nat u)) [u]) =
    app (entries ks vs (Lv ks 0 (Z.to_nat u))) [(k, v)].
Proof.
  intros h tbl ks vs cn pw u K k ku v i0 (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) Hu Hk Hg Hno Hb Hv.
  set (S := Lv ks 0 (Z.to_nat u)) in *.
  assert (HuS : ~ In u S) by (intro H; apply Lv_range in H; lia).
  assert (HLv' : Lv (set_nth_z ks u (VRef k)) 0 (Z.to_nat (u + 1)) = app S [u]).
  { replace (Z.to_nat (u + 1)) with (Datatypes.S (Z.to_nat u)) by lia. rewrite Lv_snoc.
    replace (0 + Z.of_nat (Z.to_nat u)) with u by lia. rewrite nth_set_same by lia. cbn [nonnull].
    rewrite Lv_set_out by (intros p Hp; lia). reflexivity. }
  refine (conj _ (conj HLv' _)).
  - unfold rl. rewrite HLv'. rewrite !set_nth_len.
    refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj _ _))))))).
    { lia. }
    split.
    { intros q Hq. destruct (Z.eq_dec q u) as [->|Hne].
      - right. exists k. apply nth_set_same. lia.
      - rewrite nth_set_other by congruence. apply R8. lia. }
    split.
    { intros q Hq. rewrite nth_set_other by lia. apply R9. lia. }
    split.
    { apply insert_ok; try assumption; lia. }
    split.
    { apply (insert_keys_ok e good eq_sym h ks S u k ku); try assumption; lia. }
    apply allrefs_set; assumption.
  - unfold entries. rewrite map_app. cbn [map]. f_equal.
    + apply entries_set_other; [lia|]. intros s0 Hs0. pose proof (Lv_range _ _ _ _ Hs0). split; lia.
    + f_equal. f_equal.
      * unfold key_ref. rewrite nth_set_same by lia. reflexivity.
      * apply nth_set_nat_same; lia.
Qed.

(** A key that is not in the map: the bucket head, and findIndex says -1. *)
Lemma absent_walk : forall h ks vs cn tbl pw S ku,
  tbl_ok e h ks cn tbl pw S -> keys_ok e good h ks S -> good ku -> 0 <= pw ->
  (length cn <= length ks)%nat ->
  a_mem e h (entries ks vs S) ku = false ->
  exists i, nth_z tbl (bucket e ku pw) = Some (VInt i) /\ fi_walk e h ks cn ku i (Datatypes.S (length ks)) = Some (-1) /\
            (forall s, ~ holds e h ks S ku s).
Proof.
  intros h ks vs cn tbl pw S ku Htbl Hkeys Hg Hpw Hr Hmem.
  destruct (find_correct e good eq_hash h ks cn tbl pw S ku Htbl Hkeys Hg Hpw) as (i & L & Hb & Hc & HlL & Hres).
  pose proof Htbl as (Hkd & Ht).
  assert (Hbb : 0 <= bucket e ku pw < 2 ^ pw) by (unfold bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (Ht _ Hbb) as (i' & L' & Hb' & Hc' & Hnd' & Hm').
  rewrite Hb in Hb'. injection Hb' as <-. assert (HL : L = L') by (eapply chain_unique; eassumption). subst L'.
  assert (HkL : keyed h ks L) by (intros s Hs; apply Hkd; apply Hm' in Hs; tauto).
  assert (Hno : forall s, ~ holds e h ks S ku s).
  { intros s Hs. assert (Hm2 : a_mem e h (entries ks vs S) ku = true)
      by (apply (a_mem_entries e h ks vs S ku Hkd S (fun x Hx => Hx)); exists s; split; [destruct Hs; assumption | exact Hs]).
    congruence. }
  exists i. split; [exact Hb|]. split; [|exact Hno].
  assert (Hfm : first_match e h ks ku L = -1).
  { destruct Hres as [(H1 & _) | H1]; [exact H1 | exfalso; exact (Hno _ H1)]. }
  rewrite <- Hfm. apply fi_walk_chain; [exact Hc | exact HkL | lia].
Qed.

(** ** Compaction, on the lists *)

Lemma compact_rl : forall h kA vA cA niA tA tbl ks vs cn pw u K n',
  rl h tbl ks vs cn pw u K -> u = Z.of_nat K ->
  (forall p, In p (Lv ks 0 (Z.to_nat u)) -> exists kl vv, nth_z ks p = Some (VRef kl) /\ not_in4 kA vA cA niA tA (VRef kl) = true /\
       nth_z vs p = Some vv /\ vok_b h vv = true /\ not_in4 kA vA cA niA tA vv = true) ->
  n' = Z.of_nat (length (Lv ks 0 (Z.to_nat u))) ->
  exists ni tbl' ks' vs' cn',
    c1 ks 0 (Z.to_nat u) 0 (repeat (VInt 0) (Z.to_nat u)) = Some (n', ni) /\
    c2 ni tbl 0 (Z.to_nat (Z.of_nat (length tbl))) = Some tbl' /\
    c3 h kA vA cA niA tA ni 0 (Z.to_nat u) ks vs cn = Some (ks', vs', cn') /\
    length ks' = K /\ length vs' = K /\ length cn' = K /\ length tbl' = length tbl /\
    rl h tbl' (fill_null ks' n' u) (fill_null vs' n' u) cn' pw n' K /\
    Lv (fill_null ks' n' u) 0 (Z.to_nat n') = map Z.of_nat (seq 0 (length (Lv ks 0 (Z.to_nat u)))) /\
    entries (fill_null ks' n' u) (fill_null vs' n' u) (map Z.of_nat (seq 0 (length (Lv ks 0 (Z.to_nat u))))) =
      entries ks vs (Lv ks 0 (Z.to_nat u)) /\
    (forall q, (forall s, ~ holds e h ks (Lv ks 0 (Z.to_nat u)) q s) ->
       forall s, ~ holds e h (fill_null ks' n' u) (map Z.of_nat (seq 0 (length (Lv ks 0 (Z.to_nat u))))) q s).
Proof.
  intros h kA vA cA niA tA tbl ks vs cn pw u K n' (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) Hu Hgood Hn'.
  set (S := Lv ks 0 (Z.to_nat u)) in *.
  assert (Hvk : length vs = length ks) by congruence.
  assert (Hck : length cn = length ks) by congruence.
  assert (Hnk : forall q, u <= q < Z.of_nat (length ks) -> nth_z ks q = Some VNull) by (rewrite R3; exact R9).
  pose proof (compact_ok e h kA vA cA niA tA ks vs cn tbl pw u Hvk Hck ltac:(lia) R1 ltac:(lia) R8 Hnk R10 Hgood) as Hc.
  cbv zeta in Hc. fold S in Hc. rewrite <- Hn' in Hc.
  destruct Hc as (ni & tbl' & ks' & vs' & cn' & C1 & C2 & C3 & L1 & L2 & L3 & L4 & Hn & Htb & Hcor & Hnl).
  exists ni, tbl', ks', vs', cn'.
  set (ks1 := fill_null ks' n' u) in *. set (vs1 := fill_null vs' n' u) in *.
  set (S1 := map Z.of_nat (seq 0 (length S))) in *.
  assert (Lfk : length ks1 = K) by (unfold ks1; rewrite fill_null_length'; lia).
  assert (Lfv : length vs1 = K) by (unfold vs1; rewrite fill_null_length'; lia).
  assert (HSr : forall p, In p S -> 0 <= p < u) by (intros p Hp; apply Lv_range in Hp; lia).
  assert (HndS : NoDup S) by apply Lv_NoDup.
  assert (Hat : forall j, (j < length S)%nat -> exists p kl, nth_error S j = Some p /\ nth_z ks1 (Z.of_nat j) = Some (VRef kl) /\
                 key_at h ks1 (Z.of_nat j) = key_at h ks p).
  { intros j Hj. destruct (nth_error S j) as [p|] eqn:E; [|apply nth_error_None in E; lia].
    destruct (Hcor j p E) as (C & _). destruct (proj1 R10 p (nth_error_In _ _ E)) as (ku & Hku).
    destruct (key_some_ref h ks p ku Hku) as (kl & Ekl & _). exists p, kl.
    split; [reflexivity|]. split; [rewrite C; exact Ekl | apply key_at_nth; exact C]. }
  assert (Hlv1 : Lv ks1 0 (Z.to_nat n') = S1).
  { rewrite Lv_full; [| lia | ].
    - unfold S1. replace (Z.to_nat n') with (length S) by lia. reflexivity.
    - intros p Hp. destruct (Hat (Z.to_nat p) ltac:(lia)) as (q & kl & _ & Ek & _).
      rewrite Z2Nat.id in Ek by lia. rewrite Ek. reflexivity. }
  assert (HinS1 : forall s, In s S1 -> exists j p, s = Z.of_nat j /\ nth_error S j = Some p).
  { intros s Hs. unfold S1 in Hs. apply in_map_iff in Hs as (j & <- & Hj). apply in_seq in Hj.
    destruct (nth_error S j) as [p|] eqn:E; [eauto | apply nth_error_None in E; lia]. }
  refine (conj C1 (conj C2 (conj C3 (conj _ (conj _ (conj _ (conj L4 _))))))); [lia | lia | lia |].
  split; [|split; [exact Hlv1 | split]].
  - (* the compacted lists are a representation with [n'] slots in use *)
    unfold rl. rewrite Hlv1.
    refine (conj _ (conj R2 (conj Lfk (conj Lfv (conj _ (conj R6 (conj _ _))))))); [rewrite L4; exact R1 | lia | lia |].
    split.
    { intros p Hp. right. destruct (Hat (Z.to_nat p) ltac:(lia)) as (q & kl & _ & Ek & _).
      rewrite Z2Nat.id in Ek by lia. eauto. }
    split.
    { intros q Hq. apply Hnl. lia. }
    split; [exact Htb|].
    split.
    { destruct R11 as (Kg & Kd). split.
      - intros s Hs. destruct (HinS1 s Hs) as (j & p & -> & E). rewrite (key_at_nth h ks1 ks _ p (proj1 (Hcor j p E))).
        apply Kg. apply nth_error_In with j. exact E.
      - intros s1 s2 u1 u2 H1 H2 K1 K2 Eq.
        destruct (HinS1 _ H1) as (j1 & p1 & -> & E1). destruct (HinS1 _ H2) as (j2 & p2 & -> & E2).
        rewrite (key_at_nth h ks1 ks _ p1 (proj1 (Hcor j1 p1 E1))) in K1.
        rewrite (key_at_nth h ks1 ks _ p2 (proj1 (Hcor j2 p2 E2))) in K2.
        assert (Ep : p1 = p2) by (apply (Kd p1 p2 u1 u2); [eapply nth_error_In; eauto | eapply nth_error_In; eauto | auto | auto | auto]).
        subst p2. f_equal. apply (proj1 (NoDup_nth_error S) HndS j1 j2); [apply nth_error_Some; congruence | congruence]. }
    { intros i w Hi. pose proof (nth_z_bounds _ _ _ Hi) as Hib. rewrite Lfv in Hib.
      destruct (Z_lt_le_dec i n') as [Hin|Hin].
      - destruct (nth_error S (Z.to_nat i)) as [p|] eqn:E; [|apply nth_error_None in E; lia].
        destruct (Hcor _ _ E) as (_ & C). rewrite Z2Nat.id in C by lia. rewrite C in Hi. exact (R12 p w Hi).
      - unfold vs1 in Hi. rewrite fill_null_mid in Hi by lia. injection Hi as <-. reflexivity. }
  - (* the same entries, in the same order *)
    apply entries_renum; [intros j p E; exact (Hcor j p E) | intros p Hp; rewrite R4; pose proof (HSr p Hp); lia].
  - (* the key is still absent *)
    intros q Hno s (Hs & uu & Hk & Eq). destruct (HinS1 s Hs) as (j & p & -> & E).
    rewrite (key_at_nth h ks1 ks _ p (proj1 (Hcor j p E))) in Hk.
    apply (Hno p). split; [eapply nth_error_In; eauto | eauto].
Qed.

(** ** Growth, on the lists *)

Lemma grow_rl : forall h tbl ks vs cn pw K K',
  rl h tbl ks vs cn pw (Z.of_nat K) K -> Z.of_nat K <= K' <= MAX_ARRAY ->
  rl h tbl (grow (TRef STR) ks K') (grow (TRef OBJ) vs K') (grow TInt cn K') pw (Z.of_nat K) (Z.to_nat K') /\
  Lv (grow (TRef STR) ks K') 0 (Z.to_nat (Z.of_nat K)) = Lv ks 0 (Z.to_nat (Z.of_nat K)) /\
  entries (grow (TRef STR) ks K') (grow (TRef OBJ) vs K') (Lv ks 0 (Z.to_nat (Z.of_nat K))) = entries ks vs (Lv ks 0 (Z.to_nat (Z.of_nat K))) /\
  (forall q s, holds e h (grow (TRef STR) ks K') (Lv ks 0 (Z.to_nat (Z.of_nat K))) q s -> holds e h ks (Lv ks 0 (Z.to_nat (Z.of_nat K))) q s).
Proof.
  intros h tbl ks vs cn pw K K' (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) HK'.
  set (S := Lv ks 0 (Z.to_nat (Z.of_nat K))) in *.
  set (ks2 := grow (TRef STR) ks K'). set (vs2 := grow (TRef OBJ) vs K'). set (cn2 := grow TInt cn K').
  assert (Lk : Z.of_nat (length ks2) = K') by (apply grow_length; unfold slen_v; lia).
  assert (Lv2 : Z.of_nat (length vs2) = K') by (apply grow_length; unfold slen_v; lia).
  assert (Lc : Z.of_nat (length cn2) = K') by (apply grow_length; unfold slen_v; lia).
  assert (Ek : forall p, 0 <= p < Z.of_nat K -> nth_z ks2 p = nth_z ks p) by (intros p Hp; apply nth_z_app_l; lia).
  assert (Ev : forall p, 0 <= p < Z.of_nat K -> nth_z vs2 p = nth_z vs p) by (intros p Hp; apply nth_z_app_l; lia).
  assert (Ec : forall p, 0 <= p < Z.of_nat K -> nth_z cn2 p = nth_z cn p) by (intros p Hp; apply nth_z_app_l; lia).
  assert (HSr : forall p, In p S -> 0 <= p < Z.of_nat K) by (intros p Hp; apply Lv_range in Hp; lia).
  assert (HkS : forall p, In p S -> key_at h ks2 p = key_at h ks p) by (intros p Hp; apply key_at_nth; apply Ek; apply HSr; exact Hp).
  assert (HLv : Lv ks2 0 (Z.to_nat (Z.of_nat K)) = S) by (apply Lv_ext; intros p Hp; apply Ek; lia).
  refine (conj _ (conj HLv (conj _ _))).
  - unfold rl. rewrite HLv.
    refine (conj R1 (conj R2 (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); [lia | lia | lia | lia | lia |].
    split.
    { intros p Hp. rewrite Ek by lia. apply R8. lia. }
    split.
    { intros q Hq. unfold ks2, grow. rewrite nth_z_app_r by lia. apply nth_z_repeat. unfold slen_v. lia. }
    split.
    { destruct R10 as (Hkd & Ht). split.
      - intros s Hs. rewrite HkS by exact Hs. apply Hkd. exact Hs.
      - intros b Hb. destruct (Ht b Hb) as (x & L & H1 & H2 & H3 & H4). exists x, L.
        assert (HLS : forall s, In s L -> In s S) by (intros s Hs; apply H4 in Hs; tauto).
        refine (conj H1 (conj _ (conj H3 _))).
        + apply (chain_transfer cn); [exact H2|]. intros s Hs. apply Ec. apply HSr. apply HLS. exact Hs.
        + intros s. rewrite H4. split; intros (Hs & Hx); (split; [exact Hs|]); rewrite HkS in * by exact Hs; exact Hx. }
    split.
    { destruct R11 as (Kg & Kd). split.
      - intros s Hs. rewrite HkS by exact Hs. apply Kg. exact Hs.
      - intros s1 s2 u1 u2 H1 H2 K1 K2. rewrite HkS in K1 by exact H1. rewrite HkS in K2 by exact H2. apply Kd; assumption. }
    { intros i w Hi. destruct (Z_lt_le_dec i (Z.of_nat K)) as [Hin|Hin].
      - pose proof (nth_z_bounds _ _ _ Hi) as Hib. rewrite Ev in Hi by lia. exact (R12 i w Hi).
      - unfold vs2, grow in Hi. rewrite nth_z_app_r in Hi by lia.
        pose proof (nth_z_bounds _ _ _ Hi) as Hib. rewrite repeat_length in Hib.
        rewrite nth_z_repeat in Hi by lia. injection Hi as <-. reflexivity. }
  - unfold entries. apply map_ext_in. intros p Hp. pose proof (HSr p Hp) as Hpr. f_equal.
    + unfold key_ref. rewrite Ek by lia. reflexivity.
    + destruct (nth_z_exists vs p ltac:(lia)) as (x & Ex).
      rewrite (nth_z_nth vs p x VNull Ex). apply nth_z_nth. rewrite Ev by lia. exact Ex.
  - intros q s (Hs & uu & Hk & Eq). split; [exact Hs|]. exists uu. rewrite <- HkS by exact Hs. auto.
Qed.

(** ** The stored values *)

(** A value the map may hold: null, or a non-array object other than the map. *)
Definition vgood (h : heap) (m : Z) (v : value) : Prop :=
  match v with VNull => True | VRef l => plain h m l /\ vok h v | _ => False end.

Definition vals_ok (h : heap) (m : Z) (A : list (Z * value)) : Prop := forall kk vv, In (kk, vv) A -> vgood h m vv.

Lemma vgood_ref : forall h m v, vgood h m v -> (match v with VNull | VRef _ => true | _ => false end) = true.
Proof. intros h m v H. destruct v; try contradiction; reflexivity. Qed.

Lemma vgood_vok : forall h m v, vgood h m v -> vok h v.
Proof. intros h m v H. destruct v as [z|z|z|z| |l|]; try contradiction; [exact I | exact (proj2 H)]. Qed.

Lemma vgood_frame : forall h h' m v, (forall y, plain h m y -> h' y = h y) -> vgood h m v -> vgood h' m v.
Proof.
  intros h h' m v Hf H. destruct v as [z|z|z|z| |l|]; try contradiction; [exact I|].
  destruct H as ((Hlm & o & Ho & Hna) & (o' & Ho' & Ha)).
  assert (E : h' l = h l) by (apply Hf; split; [exact Hlm | exists o; auto]).
  split; [split; [exact Hlm | exists o; rewrite E; auto] | exists o'; rewrite E; auto].
Qed.

Lemma vals_ok_frame : forall h h' m A, (forall y, plain h m y -> h' y = h y) -> vals_ok h m A -> vals_ok h' m A.
Proof. intros h h' m A Hf H kk vv Hin. apply (vgood_frame h); [exact Hf | exact (H kk vv Hin)]. Qed.

Lemma fresh_lt : forall h n y o, fresh h n -> h y = Some o -> y < n.
Proof. intros h n y o Hf Hy. destruct (Z_lt_le_dec y n) as [|Hle]; [assumption|]. rewrite (Hf y Hle) in Hy. discriminate. Qed.

(** What compaction needs of the slots in use, from the representation. *)
Lemma slots_good : forall h n m kA vA cA tA tbl ks vs cn pw u K,
  fresh h n -> rl h tbl ks vs cn pw u K -> vals_ok h m (entries ks vs (Lv ks 0 (Z.to_nat u))) ->
  (exists t es, h kA = Some (OArr t es)) -> (exists t es, h vA = Some (OArr t es)) ->
  (exists t es, h cA = Some (OArr t es)) -> (exists t es, h tA = Some (OArr t es)) ->
  forall p, In p (Lv ks 0 (Z.to_nat u)) -> exists kl vv, nth_z ks p = Some (VRef kl) /\ not_in4 kA vA cA n tA (VRef kl) = true /\
       nth_z vs p = Some vv /\ vok_b h vv = true /\ not_in4 kA vA cA n tA vv = true.
Proof.
  intros h n m kA vA cA tA tbl ks vs cn pw u K Hfr (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) Hvals
         (t1 & e1 & HkA) (t2 & e2 & HvA) (t3 & e3 & HcA) (t4 & e4 & HtA) p Hp.
  pose proof (Lv_range _ _ _ _ Hp) as Hpr.
  destruct (proj1 R10 p Hp) as (ku & Hku). destruct (key_some_ref h ks p ku Hku) as (kl & Ekl & Hkl).
  destruct (nth_z_exists vs p ltac:(lia)) as (vv & Evv).
  assert (Hg : vgood h m vv).
  { apply (Hvals (key_ref ks p)). unfold entries. apply in_map_iff. exists p. split; [|exact Hp].
    rewrite (nth_z_nth vs p vv VNull Evv). reflexivity. }
  assert (Hneq : forall y o, h y = Some o -> (forall t es, o <> OArr t es) -> y <> kA /\ y <> vA /\ y <> cA /\ y <> n /\ y <> tA).
  { intros y o Hy Hna. pose proof (fresh_lt h n y o Hfr Hy).
    refine (conj _ (conj _ (conj _ (conj _ _)))); try lia; intro E; subst y; congruence. }
  exists kl, vv. refine (conj Ekl (conj _ (conj Evv (conj (vok_vok_b h vv (vgood_vok h m vv Hg)) _)))).
  - destruct (Hneq kl (OStr ku) Hkl ltac:(discriminate)) as (N1 & N2 & N3 & N4 & N5). apply not_in4_ref; assumption.
  - destruct vv as [z|z|z|z| |l|]; try contradiction; [reflexivity|].
    destruct Hg as ((_ & o & Ho & Hna) & _). destruct (Hneq l o Ho Hna) as (N1 & N2 & N3 & N4 & N5).
    apply not_in4_ref; assumption.
Qed.

(** ** put of a new key when the slot arrays are full and half of them are removed slots:
       compactRemovedSlots, then the new entry goes after the live ones. *)
Theorem put_compact_map : forall h n sts ini lk m k ku v tA kA vA cA sz u af tbl ks vs cn pw thr K,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) -> h tA = Some (OArr TInt tbl) ->
  h kA = Some (OArr (TRef STR) ks) -> h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) -> tA <> cA ->
  rl h tbl ks vs cn pw u K -> sz = Z.of_nat (length (Lv ks 0 (Z.to_nat u))) ->
  fresh h n -> vals_ok h m (entries ks vs (Lv ks 0 (Z.to_nat u))) ->
  u = Z.of_nat K -> sz <= Z.of_nat K / 2 -> (1 <= K)%nat ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> good ku ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  vgood h m v -> a_mem e h (entries ks vs (Lv ks 0 (Z.to_nat u))) ku = false ->
  sz < thr -> thr <= INT_MAX ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some VNull)
    (fun s' => cim_rep e good (ms_heap s') m (app (entries ks vs (Lv ks 0 (Z.to_nat u))) [(k, v)]) K thr /\
               same_strings (ms_heap s') h /\ hframe h (ms_heap s') m n (ms_next s') /\
               ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku v tA kA vA cA sz u af tbl ks vs cn pw thr K
         Hm HtA HkA HvA HcA Htc Hrl Hsz Hfr Hvals Hu Hhalf HK1 Hk Hmax Hg He Hi HK Hv Hmem Hthr Hthr'.
  pose proof Hrl as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
  set (S := Lv ks 0 (Z.to_nat u)) in *.
  assert (Hcnk : (length cn <= length ks)%nat) by lia.
  destruct (absent_walk h ks vs cn tbl pw S ku R10 R11 Hg ltac:(lia) Hcnk Hmem)
    as (i0 & Hb & Hw & Hno).
  assert (Hgood := slots_good h n m kA vA cA tA tbl ks vs cn pw u K Hfr Hrl Hvals
                     ltac:(eauto) ltac:(eauto) ltac:(eauto) ltac:(eauto)).
  destruct (compact_rl h kA vA cA n tA tbl ks vs cn pw u K sz Hrl Hu Hgood Hsz)
    as (ni & tbl' & ks' & vs' & cn' & C1 & C2 & C3 & L1 & L2 & L3 & L4 & Hrl1 & Hlv1 & Hent1 & Hhold1).
  fold S in Hlv1, Hent1, Hhold1.
  set (ks1 := fill_null ks' sz u) in *. set (vs1 := fill_null vs' sz u) in *.
  set (S1 := map Z.of_nat (seq 0 (length S))) in *.
  pose proof Hrl1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
  assert (Hbb : 0 <= bucket e ku pw < 2 ^ pw) by (unfold bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (proj2 Q10 _ Hbb) as (i0' & L' & Hb' & _).
  (* facts for the bytecode-level theorem *)
  assert (Hmn : m < n) by (eapply fresh_lt; eauto). assert (Hkn : k < n) by (eapply fresh_lt; eauto).
  assert (Htn : tA < n) by (eapply fresh_lt; eauto). assert (Hkan : kA < n) by (eapply fresh_lt; eauto).
  assert (Hvn : vA < n) by (eapply fresh_lt; eauto). assert (Hcn : cA < n) by (eapply fresh_lt; eauto).
  assert (Hpw30 : 0 <= pw <= 30) by lia.
  assert (Hpw2 : 2 ^ pw <= MAX_ARRAY)
    by (change MAX_ARRAY with (2 ^ 20); apply Z.pow_le_mono_r; lia).
  assert (Hvl : length vs = length ks) by congruence.
  assert (Hcl : length cn = length ks) by congruence.
  assert (HK2 : Z.of_nat (length ks) <= MAX_ARRAY) by (rewrite R3; exact R6).
  assert (Hsz0 : 0 <= sz < thr) by lia.
  assert (Hu' : u = Z.of_nat (length ks)) by (rewrite R3; exact Hu).
  assert (Hhalf' : sz <= Z.of_nat (length ks) / 2) by (rewrite R3; exact Hhalf).
  assert (Hvok : vok h v) by (eapply vgood_vok; eauto).
  assert (Hvd : match v with VRef vl => vl <> m /\ vl <> kA /\ vl <> tA /\ vl <> vA /\ vl <> cA /\ vl < n | _ => True end).
  { destruct v as [z|z|z|z| |vl|]; try exact I. destruct Hv as ((Hlm & o & Ho & Hna) & _).
    pose proof (fresh_lt h n vl o Hfr Ho).
    refine (conj Hlm (conj _ (conj _ (conj _ (conj _ _))))); try lia; intro E; subst vl; congruence. }
  assert (Hn'u : 0 <= sz < u).
  { split; [lia|]. rewrite Hu. clear -Hhalf HK1. Z.div_mod_to_equations. lia. }
  assert (Hlk' : length ks' = length ks) by congruence.
  assert (Hlv' : length vs' = length ks) by congruence.
  assert (Hlc' : length cn' = length ks) by congruence.
  assert (Hw' : fi_walk e h ks cn ku i0 (Datatypes.S (length ks)) = Some (-1)) by exact Hw.
  eapply returns_weaken.
  { apply (put_compact e h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0 sz ni tbl' ks' vs' cn' i0');
      assumption. }
  cbv zeta. intros s' (P1 & P2 & P3 & P4 & P5 & P6 & Pn & P7 & P8 & P9).
  set (h' := ms_heap s') in *.
  fold ks1 vs1 in P2, P3.
  (* the new entry *)
  assert (Hno1 : forall s, ~ holds e h ks1 (Lv ks1 0 (Z.to_nat sz)) ku s) by (rewrite Hlv1; apply Hhold1; exact Hno).
  destruct (rl_insert h tbl' ks1 vs1 cn' pw sz K k ku v i0' Hrl1 ltac:(lia) Hk Hg Hno1 Hb' (vgood_ref h m v Hv))
    as (Hrl2 & Hlv2 & Hent2).
  (* the strings are the same *)
  assert (Hsame : same_strings h' h).
  { intros y u0. destruct (Z.eq_dec y n) as [->|N0]; [rewrite Pn, (Hfr n ltac:(lia)); split; discriminate|].
    destruct (Z.eq_dec y m) as [->|N1]; [rewrite P1, Hm; split; discriminate|].
    destruct (Z.eq_dec y kA) as [->|N2]; [rewrite P2, HkA; split; discriminate|].
    destruct (Z.eq_dec y vA) as [->|N3]; [rewrite P3, HvA; split; discriminate|].
    destruct (Z.eq_dec y cA) as [->|N4]; [rewrite P4, HcA; split; discriminate|].
    destruct (Z.eq_dec y tA) as [->|N5]; [rewrite P5, HtA; split; discriminate|].
    rewrite P6 by assumption. reflexivity. }
  assert (Hsame' : same_strings h h') by (intros y u0; symmetry; apply Hsame).
  refine (conj _ (conj Hsame (conj _ (conj P8 P9)))).
  - apply (rep_intro h' m _ K thr tA kA vA cA (sz + 1) (sz + 1) af (set_nth_z tbl' (bucket e ku pw) (VInt sz))
             (set_nth_z ks1 sz (VRef k)) (set_nth_z vs1 sz v) (set_nth_z cn' sz (VInt i0')) pw).
    + exact P1.
    + exact P5.
    + exact P2.
    + exact P3.
    + exact P4.
    + exact Htc.
    + apply (rl_same h h'); [exact Hsame' | exact Hrl2].
    + rewrite Hlv2. rewrite app_length. cbn [length]. rewrite Hlv1. unfold S1. rewrite map_length, seq_length. lia.
    + rewrite Hlv2, Hent2. rewrite Hlv1, Hent1. reflexivity.
  - rewrite P7. apply (hframe_gen h h' m n (n + 1) [kA; vA; cA; tA]); [lia | rewrite Hm; discriminate | hfr_arrays |].
    intros y Y1 Y2 Y3. apply P6; [lia | exact Y1 | | | |]; intro E; apply Y2; rewrite E; cbn [In]; tauto.
Qed.

(** ** put of a new key when the slot arrays are full and mostly live: the arrays grow by half. *)
Theorem put_grow_map : forall h n sts ini lk m k ku v tA kA vA cA sz u af tbl ks vs cn pw thr K,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) -> h tA = Some (OArr TInt tbl) ->
  h kA = Some (OArr (TRef STR) ks) -> h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) -> tA <> cA ->
  rl h tbl ks vs cn pw u K -> sz = Z.of_nat (length (Lv ks 0 (Z.to_nat u))) ->
  fresh h n ->
  u = Z.of_nat K -> Z.of_nat K / 2 < sz -> (2 <= K)%nat -> Z.of_nat K + Z.of_nat K / 2 <= MAX_ARRAY ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> good ku ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  vgood h m v -> a_mem e h (entries ks vs (Lv ks 0 (Z.to_nat u))) ku = false ->
  sz < thr -> thr <= INT_MAX ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some VNull)
    (fun s' => cim_rep e good (ms_heap s') m (app (entries ks vs (Lv ks 0 (Z.to_nat u))) [(k, v)])
                 (Z.to_nat (Z.of_nat K + Z.of_nat K / 2)) thr /\
               same_strings (ms_heap s') h /\ hframe h (ms_heap s') m n (ms_next s') /\
               ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku v tA kA vA cA sz u af tbl ks vs cn pw thr K
         Hm HtA HkA HvA HcA Htc Hrl Hsz Hfr Hu Hhalf HK2 HKm Hk Hmax Hg He Hi HK Hv Hmem Hthr Hthr'.
  pose proof Hrl as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
  subst u.
  set (S := Lv ks 0 (Z.to_nat (Z.of_nat K))) in *.
  set (K' := Z.of_nat K + Z.of_nat K / 2) in *.
  assert (Hcnk : (length cn <= length ks)%nat) by lia.
  destruct (absent_walk h ks vs cn tbl pw S ku R10 R11 Hg ltac:(lia) Hcnk Hmem)
    as (i0 & Hb & Hw & Hno).
  assert (HK'r : Z.of_nat K <= K' <= MAX_ARRAY) by (unfold K'; split; [pose proof (Z.div_pos (Z.of_nat K) 2 ltac:(lia) ltac:(lia)); lia | exact HKm]).
  assert (HK'1 : Z.of_nat K < K') by (unfold K'; clear -HK2; Z.div_mod_to_equations; lia).
  destruct (grow_rl h tbl ks vs cn pw K K' Hrl HK'r) as (Hrl1 & Hlv1 & Hent1 & Hhold1).
  fold S in Hlv1, Hent1, Hhold1.
  set (ks2 := grow (TRef STR) ks K') in *. set (vs2 := grow (TRef OBJ) vs K') in *. set (cn2 := grow TInt cn K') in *.
  assert (Hmn : m < n) by (eapply fresh_lt; eauto). assert (Hkn : k < n) by (eapply fresh_lt; eauto).
  assert (Htn : tA < n) by (eapply fresh_lt; eauto). assert (Hkan : kA < n) by (eapply fresh_lt; eauto).
  assert (Hvn : vA < n) by (eapply fresh_lt; eauto). assert (Hcn : cA < n) by (eapply fresh_lt; eauto).
  assert (Hpw30 : 0 <= pw <= 30) by lia.
  assert (Hvl : length vs = length ks) by congruence.
  assert (Hcl : length cn = length ks) by congruence.
  assert (HK2' : 2 <= Z.of_nat (length ks)) by lia.
  assert (HKm' : Z.of_nat (length ks) + Z.of_nat (length ks) / 2 <= MAX_ARRAY) by (rewrite R3; exact HKm).
  assert (Hsz0 : 0 <= sz < thr) by lia.
  assert (Hu' : Z.of_nat K = Z.of_nat (length ks)) by (rewrite R3; reflexivity).
  assert (Hhalf' : Z.of_nat (length ks) / 2 < sz) by (rewrite R3; exact Hhalf).
  assert (Hvok : vok h v) by (eapply vgood_vok; eauto).
  assert (Hvd : match v with VRef vl => vl <> m /\ vl <> kA /\ vl < n | _ => True end).
  { destruct v as [z|z|z|z| |vl|]; try exact I. destruct Hv as ((Hlm & o & Ho & Hna) & _).
    pose proof (fresh_lt h n vl o Hfr Ho).
    refine (conj Hlm (conj _ _)); try lia; intro E; subst vl; congruence. }
  assert (Hw' : fi_walk e h ks cn ku i0 (Datatypes.S (length ks)) = Some (-1)) by exact Hw.
  eapply returns_weaken.
  { apply (put_grow e h n sts ini lk m k v tA kA vA cA sz (Z.of_nat K) thr af tbl ks vs cn pw ku i0); assumption. }
  cbv zeta. intros s' (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  set (h' := ms_heap s') in *.
  rewrite R3 in P2, P3, P4. fold K' ks2 vs2 cn2 in P2, P3, P4.
  assert (Hno1 : forall s, ~ holds e h ks2 (Lv ks2 0 (Z.to_nat (Z.of_nat K))) ku s)
    by (rewrite Hlv1; intros s Hs; apply (Hno s); apply Hhold1; exact Hs).
  destruct (rl_insert h tbl ks2 vs2 cn2 pw (Z.of_nat K) (Z.to_nat K') k ku v i0 Hrl1 ltac:(lia) Hk Hg Hno1 Hb (vgood_ref h m v Hv))
    as (Hrl2 & Hlv2 & Hent2).
  assert (Hsame : same_strings h' h).
  { intros y u0.
    destruct (Z.eq_dec y n) as [->|N0]; [rewrite P2, (Hfr n ltac:(lia)); split; discriminate|].
    destruct (Z.eq_dec y (n + 1)) as [->|N1]; [rewrite P3, (Hfr (n + 1) ltac:(lia)); split; discriminate|].
    destruct (Z.eq_dec y (n + 2)) as [->|N2]; [rewrite P4, (Hfr (n + 2) ltac:(lia)); split; discriminate|].
    destruct (Z.eq_dec y m) as [->|N3]; [rewrite P1, Hm; split; discriminate|].
    destruct (Z.eq_dec y tA) as [->|N4]; [rewrite P5, HtA; split; discriminate|].
    rewrite P6 by assumption. reflexivity. }
  assert (Hsame' : same_strings h h') by (intros y u0; symmetry; apply Hsame).
  refine (conj _ (conj Hsame (conj _ (conj P8 P9)))).
  - apply (rep_intro h' m _ (Z.to_nat K') thr tA n (n + 1) (n + 2) (sz + 1) (Z.of_nat K + 1) af
             (set_nth_z tbl (bucket e ku pw) (VInt (Z.of_nat K))) (set_nth_z ks2 (Z.of_nat K) (VRef k))
             (set_nth_z vs2 (Z.of_nat K) v) (set_nth_z cn2 (Z.of_nat K) (VInt i0)) pw).
    + exact P1.
    + exact P5.
    + exact P2.
    + exact P3.
    + exact P4.
    + lia.
    + apply (rl_same h h'); [exact Hsame' | exact Hrl2].
    + rewrite Hlv2. rewrite app_length, Hlv1. cbn [length]. lia.
    + rewrite Hlv2, Hent2. rewrite Hlv1, Hent1. reflexivity.
  - rewrite P7. apply (hframe_gen h h' m n (n + 3) [tA]); [lia | rewrite Hm; discriminate | hfr_arrays |].
    intros y Y1 Y2 Y3. apply P6; [lia | lia | lia | exact Y1 |]. intro E; apply Y2; rewrite E; cbn [In]; tauto.
Qed.

End Map3.

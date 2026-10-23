(** * CaseInsensitiveMap (fix): the real bytecode behaves as a map.

    [cim_rep]: the heap holds a CaseInsensitiveMap object whose entries, in slot
    order, are the list [A] of (key, value) pairs; the slot arrays have [K] slots.
    Each [*_map] theorem runs one method of the real class on such a heap and gives
    its result in terms of [A] and the representation afterwards. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimPut CimRemove CimAbs CimAbs2.
Import ListNotations.
Open Scope Z_scope.

Lemma chain_unique : forall cn i L1 L2, chain cn i L1 -> chain cn i L2 -> L1 = L2.
Proof.
  intros cn i L1 L2 H1. revert L2. induction H1 as [|i j L Hi Hn Hc IH]; intros L2 H2.
  - inversion H2; [reflexivity | lia].
  - inversion H2 as [Heq|i' j' L' Hi' Hn' Hc']; subst; [lia|].
    rewrite Hn in Hn'. injection Hn' as <-. f_equal. apply IH. exact Hc'.
Qed.

Section Map.
Variable e : jenv.
Variable good : list Z -> Prop.
Hypothesis eq_sym : forall a b, good a -> good b -> eqic e a b = eqic e b a.
Hypothesis eq_trans : forall a b c, good a -> good b -> good c -> eqic e a b = true -> eqic e b c = true -> eqic e a c = true.
Hypothesis eq_hash : forall a b, good a -> good b -> eqic e a b = true -> cih_spec e a = cih_spec e b.

Definition key_ref (ks : list value) (s : Z) : Z := match nth_z ks s with Some (VRef k) => k | _ => -1 end.
Definition entries (ks vs : list value) (S : list Z) : list (Z * value) :=
  map (fun s => (key_ref ks s, nth (Z.to_nat s) vs VNull)) S.

Definition kunits (h : heap) (k : Z) : option (list Z) := match h k with Some (OStr u) => Some u | _ => None end.

(** The abstract map: lookup of the first entry whose key equals [q] ignoring case. *)
Fixpoint a_get (h : heap) (A : list (Z * value)) (q : list Z) : value :=
  match A with
  | [] => VNull
  | (k, v) :: r => match kunits h k with Some u => if eqic e u q then v else a_get h r q | None => a_get h r q end
  end.

Lemma key_at_ref : forall h ks s u, key_at h ks s = Some u -> kunits h (key_ref ks s) = Some u.
Proof.
  intros h ks s u H. unfold key_at in H. unfold key_ref, kunits.
  destruct (nth_z ks s) as [[z|z|z|z| |kl|]|]; try discriminate. exact H.
Qed.

(** On the entries of the used slots, the abstract lookup finds the holding slot's value. *)
Lemma a_get_entries : forall h ks vs S q,
  keys_ok e good h ks S -> keyed h ks S -> good q ->
  forall S', (forall s, In s S' -> In s S) ->
  ((forall s, In s S' -> ~ holds e h ks S q s) -> a_get h (entries ks vs S') q = VNull) /\
  (forall s, In s S' -> holds e h ks S q s -> a_get h (entries ks vs S') q = nth (Z.to_nat s) vs VNull).
Proof.
  intros h ks vs S q Hk Hkd Hq S'. induction S' as [|s0 S' IH]; intros Hsub.
  - split; [reflexivity | intros s []].
  - destruct (IH (fun x Hx => Hsub x (or_intror Hx))) as (IH1 & IH2).
    destruct (Hkd s0 (Hsub s0 (or_introl eq_refl))) as (u0 & Hu0).
    cbn [entries map a_get]. rewrite (key_at_ref h ks s0 u0 Hu0).
    split.
    + intros Hno. destruct (eqic e u0 q) eqn:E.
      * exfalso. apply (Hno s0 (or_introl eq_refl)). split; [apply Hsub; left; reflexivity | exists u0; auto].
      * apply IH1. intros s Hs. apply Hno. right. exact Hs.
    + intros s [<-|Hs] (HS & u & Hu & Eu).
      * rewrite Hu0 in Hu. injection Hu as <-. rewrite Eu. reflexivity.
      * destruct (eqic e u0 q) eqn:E.
        -- (* both s0 and s hold q: they are the same slot *)
           destruct Hk as (Hg & Hd).
           destruct (Hg s0 (Hsub s0 (or_introl eq_refl))) as (u0' & Hu0' & G0). rewrite Hu0 in Hu0'. injection Hu0' as <-.
           destruct (Hg s HS) as (u' & Hu' & G). rewrite Hu in Hu'. injection Hu' as <-.
           assert (E2 : eqic e u0 u = true) by (apply (eq_trans u0 q u); auto; rewrite eq_sym by assumption; exact Eu).
           assert (s0 = s) by (eapply Hd; [apply Hsub; left; reflexivity | exact HS | exact Hu0 | exact Hu | exact E2]).
           subst s0. reflexivity.
        -- apply IH2; [exact Hs | split; [exact HS | exists u; auto]].
Qed.

(** The representation. *)
Definition cim_rep (h : heap) (m : Z) (A : list (Z * value)) (K : nat) (thr : Z) : Prop :=
  exists tA kA vA cA sz u af tbl ks vs cn pw,
    h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) /\
    h tA = Some (OArr TInt tbl) /\ h kA = Some (OArr (TRef STR) ks) /\
    h vA = Some (OArr (TRef OBJ) vs) /\ h cA = Some (OArr TInt cn) /\ tA <> cA /\
    Z.of_nat (length tbl) = 2 ^ pw /\ 0 <= pw <= 30 /\
    length ks = K /\ length vs = K /\ length cn = K /\ Z.of_nat K <= MAX_ARRAY /\
    0 <= u <= Z.of_nat K /\ slots_ok ks 0 (Z.to_nat u) /\
    (forall q, u <= q < Z.of_nat K -> nth_z ks q = Some VNull) /\
    sz = Z.of_nat (length (Lv ks 0 (Z.to_nat u))) /\
    tbl_ok e h ks cn tbl pw (Lv ks 0 (Z.to_nat u)) /\ keys_ok e good h ks (Lv ks 0 (Z.to_nat u)) /\
    allrefs vs /\
    A = entries ks vs (Lv ks 0 (Z.to_nat u)).

Theorem get_map : forall h n sts ini lk m k ku A K thr,
  cim_rep h m A K thr ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> good ku ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [get_frame m k] |}
    (Some (a_get h A ku))
    (fun s' => ms_heap s' = h /\ ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku A K thr Hrep Hk Hmax Hg He Hi.
  destruct Hrep as (tA & kA & vA & cA & sz & u & af & tbl & ks & vs & cn & pw &
                    Hm & HtA & HkA & HvA & HcA & Htc & Hlen & Hpw & Hlk & Hlv & Hlc & HKmax & Hu & Hsl & Hnull & Hsz & Htbl & Hkeys & Hrefs & HA).
  set (S := Lv ks 0 (Z.to_nat u)) in *.
  destruct (find_correct e good eq_hash h ks cn tbl pw S ku Htbl Hkeys Hg ltac:(lia)) as (i & L & Hb & Hc & HlL & Hres).
  assert (Hkd : keyed h ks S) by (destruct Htbl; assumption).
  (* the chain's slots all hold keys *)
  destruct Htbl as (Hkd' & Ht).
  assert (Hbb : 0 <= bucket e ku pw < 2 ^ pw) by (unfold bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (Ht _ Hbb) as (i' & L' & Hb' & Hc' & Hnd' & Hm').
  rewrite Hb in Hb'. injection Hb' as <-.
  assert (HL : L = L') by (eapply chain_unique; eassumption).
  subst L'.
  assert (HkL : keyed h ks L) by (intros s Hs; apply Hkd; apply Hm' in Hs; tauto).
  assert (Hw : fi_walk e h ks cn ku i (Datatypes.S (length ks)) = Some (first_match e h ks ku L))
    by (apply fi_walk_chain; [exact Hc | exact HkL | lia]).
  assert (Hval : (if first_match e h ks ku L =? -1 then VNull else nth (Z.to_nat (first_match e h ks ku L)) vs VNull)
                 = a_get h A ku).
  { subst A. destruct (a_get_entries h ks vs S ku Hkeys Hkd Hg S (fun s Hs => Hs)) as (G1 & G2).
    destruct Hres as [(H1 & H2) | H1].
    - rewrite H1. cbn. symmetry. apply G1. intros s _. apply H2.
    - destruct (Z.eqb_spec (first_match e h ks ku L) (-1)) as [E|E].
      + exfalso. rewrite E in H1. destruct H1 as (HS & _). apply Lv_range in HS. lia.
      + symmetry. apply G2; [destruct H1; assumption | exact H1]. }
  rewrite <- Hval.
  apply (get_spec e h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks vs cn pw i (first_match e h ks ku L));
    try assumption; lia.
Qed.


(** ** remove *)
Fixpoint a_remove (h : heap) (A : list (Z * value)) (q : list Z) : list (Z * value) :=
  match A with
  | [] => []
  | (k, v) :: r => match kunits h k with Some u => if eqic e u q then r else (k, v) :: a_remove h r q | None => (k, v) :: a_remove h r q end
  end.

Lemma a_remove_entries : forall h ks vs S q,
  keys_ok e good h ks S -> keyed h ks S -> good q ->
  forall S', (forall s, In s S' -> In s S) -> NoDup S' ->
  ((forall s, In s S' -> ~ holds e h ks S q s) -> a_remove h (entries ks vs S') q = entries ks vs S') /\
  (forall c, In c S' -> holds e h ks S q c -> a_remove h (entries ks vs S') q = entries ks vs (remove Z.eq_dec c S')).
Proof.
  intros h ks vs S q Hk Hkd Hq S'. induction S' as [|s0 S' IH]; intros Hsub Hnd.
  - split; [reflexivity | intros c []].
  - inversion Hnd as [|x l Hx Hnd']; subst.
    destruct (IH (fun x Hx => Hsub x (or_intror Hx)) Hnd') as (IH1 & IH2).
    destruct (Hkd s0 (Hsub s0 (or_introl eq_refl))) as (u0 & Hu0).
    cbn [entries map a_remove]. rewrite (key_at_ref h ks s0 u0 Hu0).
    split.
    + intros Hno. destruct (eqic e u0 q) eqn:E.
      * exfalso. apply (Hno s0 (or_introl eq_refl)). split; [apply Hsub; left; reflexivity | exists u0; auto].
      * f_equal. apply IH1. intros s Hs. apply Hno. right. exact Hs.
    + intros c [E0|Hc] (HS & u & Hu & Eu).
      * subst c. rewrite Hu0 in Hu. injection Hu as <-. rewrite Eu. cbn [remove].
        destruct (Z.eq_dec s0 s0) as [_|]; [|contradiction]. rewrite notin_remove by exact Hx. reflexivity.
      * destruct (eqic e u0 q) eqn:E.
        -- exfalso. destruct Hk as (Hg & Hd).
           destruct (Hg s0 (Hsub s0 (or_introl eq_refl))) as (u0' & Hu0' & G0). rewrite Hu0 in Hu0'. injection Hu0' as <-.
           destruct (Hg c HS) as (u' & Hu' & G). rewrite Hu in Hu'. injection Hu' as <-.
           assert (E2 : eqic e u0 u = true) by (apply (eq_trans u0 q u); auto; rewrite eq_sym by assumption; exact Eu).
           assert (s0 = c) by (eapply Hd; [apply Hsub; left; reflexivity | exact HS | exact Hu0 | exact Hu | exact E2]).
           subst s0. contradiction.
        -- cbn [remove]. destruct (Z.eq_dec c s0) as [E'|_]; [subst; contradiction|].
           cbn [entries map]. f_equal. apply IH2; [exact Hc | split; [exact HS | exists u; auto]].
Qed.

Lemma Lv_clear : forall ks c f i, Lv (set_nth_z ks c VNull) i f = remove Z.eq_dec c (Lv ks i f).
Proof.
  intros ks c f. induction f as [|f IH]; intros i; [reflexivity|].
  rewrite !Lv_S. destruct (Z.eq_dec i c) as [->|Hne].
  - destruct (Z_lt_le_dec c 0) as [Hneg|Hpos].
    + (* out of range: nothing changes *)
      assert (forall {A} (l : list A) j v, j < 0 -> set_nth_z l j v = l) as Hs.
      { intros A l. induction l as [|x r IHl]; intros j v Hj; cbn; [reflexivity|].
        replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite IHl by lia. reflexivity. }
      rewrite Hs by lia.
      assert (Hn : nth_z ks c = None).
      { destruct (nth_z ks c) eqn:E; [|reflexivity]. apply nth_z_bounds in E. lia. }
      rewrite Hn. cbn [nonnull].
      assert (Hnin : ~ In c (Lv ks (c + 1) f)) by (intro H; apply Lv_range in H; lia).
      rewrite (notin_remove _ _ _ Hnin). reflexivity.
    + destruct (Nat.lt_ge_cases (Z.to_nat c) (length ks)) as [Hlt|Hge].
      * rewrite nth_set_same by lia. cbn [nonnull].
        assert (Hnin : ~ In c (Lv ks (c + 1) f)) by (intro H; apply Lv_range in H; lia).
        rewrite IH. rewrite (notin_remove _ _ _ Hnin).
        destruct (nonnull (nth_z ks c)); cbn [remove]; [destruct (Z.eq_dec c c); [|contradiction]|]; rewrite (notin_remove _ _ _ Hnin); reflexivity.
      * (* beyond the array: nth is None on both sides *)
        assert (Hn1 : nth_z (set_nth_z ks c VNull) c = None).
        { destruct (nth_z (set_nth_z ks c VNull) c) eqn:E; [|reflexivity]. apply nth_z_bounds in E. rewrite set_nth_len in E. lia. }
        assert (Hn2 : nth_z ks c = None).
        { destruct (nth_z ks c) eqn:E; [|reflexivity]. apply nth_z_bounds in E. lia. }
        rewrite Hn1, Hn2. cbn [nonnull]. rewrite IH.
        assert (Hnin : ~ In c (Lv ks (c + 1) f)) by (intro H; apply Lv_range in H; lia).
        rewrite (notin_remove _ _ _ Hnin). reflexivity.
  - rewrite nth_set_other by congruence. rewrite IH.
    destruct (nonnull (nth_z ks i)); cbn [remove]; [|reflexivity].
    destruct (Z.eq_dec c i) as [E|_]; [congruence | reflexivity].
Qed.


Lemma rm_match_first : forall h ks q L prev, keyed h ks L ->
  (rm_match e h ks q prev L = None /\ first_match e h ks q L = -1) \/
  (exists p, rm_match e h ks q prev L = Some (p, first_match e h ks q L)).
Proof.
  intros h ks q L. induction L as [|s L IH]; intros prev Hk; [left; auto|].
  cbn [rm_match first_match]. destruct (Hk s (or_introl eq_refl)) as (u & Hu). rewrite Hu.
  destruct (eqic e u q); [right; eauto|]. apply IH. intros x Hx; apply Hk; right; exact Hx.
Qed.

(** Heaps that hold the same strings. *)
Definition same_strings (h h' : heap) : Prop := forall y u, h y = Some (OStr u) <-> h' y = Some (OStr u).

Lemma key_at_same : forall h h' ks s, same_strings h h' -> key_at h' ks s = key_at h ks s.
Proof.
  intros h h' ks s H. unfold key_at. destruct (nth_z ks s) as [[z|z|z|z| |kl|]|]; try reflexivity.
  destruct (h kl) as [o|] eqn:E1.
  - destruct o; try (destruct (h' kl) as [[]|] eqn:E2; try reflexivity; apply H in E2; congruence).
    apply H in E1. rewrite E1. reflexivity.
  - destruct (h' kl) as [[]|] eqn:E2; try reflexivity. apply H in E2. congruence.
Qed.

Lemma tbl_ok_same : forall h h' ks cn tbl pw S, same_strings h h' -> tbl_ok e h ks cn tbl pw S -> tbl_ok e h' ks cn tbl pw S.
Proof.
  intros h h' ks cn tbl pw S Hs (Hk & Ht). split.
  - intros s Hin. rewrite key_at_same with (h := h) by exact Hs. apply Hk. exact Hin.
  - intros b Hb. destruct (Ht b Hb) as (i & L & H1 & H2 & H3 & H4). exists i, L.
    refine (conj H1 (conj H2 (conj H3 _))). intros s. split.
    + intros Hin. apply H4 in Hin as (HS & ku & Hku & E). split; [exact HS|]. exists ku. rewrite key_at_same with (h := h) by exact Hs. auto.
    + intros (HS & ku & Hku & E). apply H4. split; [exact HS|]. exists ku. rewrite key_at_same with (h := h) in Hku by exact Hs. auto.
Qed.

Lemma keys_ok_same : forall h h' ks S, same_strings h h' -> keys_ok e good h ks S -> keys_ok e good h' ks S.
Proof.
  intros h h' ks S Hs (Hg & Hd). split.
  - intros s Hin. rewrite key_at_same with (h := h) by exact Hs. apply Hg. exact Hin.
  - intros s1 s2 u1 u2 H1 H2 K1 K2 E. rewrite key_at_same with (h := h) in K1, K2 by exact Hs. eapply Hd; eauto.
Qed.

Lemma kunits_same : forall h h' k, same_strings h h' -> kunits h' k = kunits h k.
Proof.
  intros h h' k H. unfold kunits. destruct (h k) as [o|] eqn:E1.
  - destruct o; try (destruct (h' k) as [[]|] eqn:E2; try reflexivity; apply H in E2; congruence).
    apply H in E1. rewrite E1. reflexivity.
  - destruct (h' k) as [[]|] eqn:E2; try reflexivity. apply H in E2. congruence.
Qed.

Lemma same_upd : forall h y o, h y <> None -> (forall u, h y <> Some (OStr u)) -> (forall u, o <> OStr u) -> same_strings h (upd h y o).
Proof.
  intros h y o H1 H2 H3 x u. unfold upd. destruct (Z.eqb_spec x y).
  - subst. split; [intro H; exfalso; exact (H2 u H) | intro H; injection H as E; exact (False_ind _ (H3 u E))].
  - reflexivity.
Qed.

Lemma same_trans : forall h1 h2 h3, same_strings h1 h2 -> same_strings h2 h3 -> same_strings h1 h3.
Proof. intros h1 h2 h3 A B y u. rewrite (A y u). apply B. Qed.

Lemma same_upd_obj : forall h y o o', h y = Some o -> (match o with OStr _ => False | _ => True end) ->
  (match o' with OStr _ => False | _ => True end) -> same_strings h (upd h y o').
Proof.
  intros h y o o' Hy Ho Ho'. apply same_upd.
  - congruence.
  - intros u E. rewrite Hy in E. injection E as ->. exact Ho.
  - intros u ->. exact Ho'.
Qed.


Lemma remove_length_in : forall (l : list Z) x, NoDup l -> In x l -> length (remove Z.eq_dec x l) = (length l - 1)%nat.
Proof.
  induction l as [|y l IH]; intros x Hnd Hin; [destruct Hin|].
  inversion Hnd as [|y' l' Hy Hnd']; subst. cbn [remove].
  destruct (Z.eq_dec x y) as [->|Hne].
  - rewrite notin_remove by exact Hy. cbn. lia.
  - destruct Hin as [->|Hin]; [contradiction|]. cbn [length]. rewrite IH by assumption.
    destruct l; [destruct Hin | cbn; lia].
Qed.

Lemma nth_set_nat_other : forall (l : list value) i j v d, 0 <= i -> 0 <= j -> i <> j ->
  nth (Z.to_nat j) (set_nth_z l i v) d = nth (Z.to_nat j) l d.
Proof.
  induction l as [|x r IH]; intros i j v d Hi Hj Hij; cbn [set_nth_z]; [reflexivity|].
  destruct (Z.eqb_spec i 0) as [->|Hne].
  - destruct (Z.to_nat j) eqn:E; [lia | reflexivity].
  - destruct (Z.to_nat j) eqn:E.
    + reflexivity.
    + cbn. replace n with (Z.to_nat (j - 1)) by lia. apply IH; lia.
Qed.

Lemma entries_set_other : forall ks vs c S v1 v2, 0 <= c -> (forall s, In s S -> 0 <= s /\ s <> c) ->
  entries (set_nth_z ks c v1) (set_nth_z vs c v2) S = entries ks vs S.
Proof.
  intros ks vs c S v1 v2 Hc HS. induction S as [|s S IH]; [reflexivity|].
  cbn [entries map]. destruct (HS s (or_introl eq_refl)) as (Hs & Hsc). f_equal.
  - unfold key_ref. rewrite nth_set_other by congruence. f_equal. apply nth_set_nat_other; lia.
  - apply IH. intros x Hx. apply HS. right. exact Hx.
Qed.

Lemma allrefs_set_null : forall vs c, allrefs vs -> allrefs (set_nth_z vs c VNull).
Proof.
  intros vs c H i v Hi. destruct (Z.eq_dec i c) as [->|Hne].
  - destruct (Z_lt_le_dec c 0).
    + exfalso. apply nth_z_bounds in Hi. lia.
    + destruct (Nat.lt_ge_cases (Z.to_nat c) (length vs)).
      * rewrite nth_set_same in Hi by lia. injection Hi as <-. reflexivity.
      * apply nth_z_bounds in Hi. rewrite set_nth_len in Hi. lia.
  - rewrite nth_set_other in Hi by congruence. apply (H i v Hi).
Qed.

Theorem remove_map : forall h n sts ini lk m k ku A K thr,
  cim_rep h m A K thr ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> good ku ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [rm_frame m k] |}
    (Some (a_get h A ku))
    (fun s' => cim_rep (ms_heap s') m (a_remove h A ku) K thr /\ same_strings h (ms_heap s') /\
               ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku A K thr Hrep Hk Hmax Hg He Hi.
  destruct Hrep as (tA & kA & vA & cA & sz & u & af & tbl & ks & vs & cn & pw &
                    Hm & HtA & HkA & HvA & HcA & Htc & Hlen & Hpw & Hlk & Hlv & Hlc & HKmax & Hu & Hsl & Hnull & Hsz & Htbl & Hkeys & Hrefs & HA).
  set (S := Lv ks 0 (Z.to_nat u)) in *.
  assert (HndS : NoDup S) by apply Lv_NoDup.
  destruct (find_correct e good eq_hash h ks cn tbl pw S ku Htbl Hkeys Hg ltac:(lia)) as (i & L & Hb & Hc & HlL & Hres).
  pose proof Htbl as (Hkd & Ht).
  assert (Hbb : 0 <= bucket e ku pw < 2 ^ pw) by (unfold bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (Ht _ Hbb) as (i' & L' & Hb' & Hc' & Hnd' & Hm').
  rewrite Hb in Hb'. injection Hb' as <-. assert (HL : L = L') by (eapply chain_unique; eassumption). subst L'.
  assert (HkL : keyed h ks L) by (intros s Hs; apply Hkd; apply Hm' in Hs; tauto).
  assert (Hw : rm_walk e h ks cn ku (-1) i (Datatypes.S (length ks)) = Some (rm_match e h ks ku (-1) L))
    by (apply rm_walk_chain; [exact Hc | exact HkL | lia]).
  destruct (a_get_entries h ks vs S ku Hkeys Hkd Hg S (fun s Hs => Hs)) as (G1 & G2).
  destruct (a_remove_entries h ks vs S ku Hkeys Hkd Hg S (fun s Hs => Hs) HndS) as (R1 & R2).
  assert (Hmt : m <> tA) by (intro E; subst; rewrite Hm in HtA; discriminate).
  assert (Hmk : m <> kA) by (intro E; subst; rewrite Hm in HkA; discriminate).
  assert (Hmv : m <> vA) by (intro E; subst; rewrite Hm in HvA; discriminate).
  assert (Hmc : m <> cA) by (intro E; subst; rewrite Hm in HcA; discriminate).
  assert (Hkt : kA <> tA) by (intro E; subst; rewrite HkA in HtA; discriminate).
  assert (Hkv : kA <> vA) by (intro E; subst; rewrite HkA in HvA; discriminate).
  assert (Hkc : kA <> cA) by (intro E; subst; rewrite HkA in HcA; discriminate).
  assert (Hvt : vA <> tA) by (intro E; subst; rewrite HvA in HtA; discriminate).
  assert (Hvc : vA <> cA) by (intro E; subst; rewrite HvA in HcA; discriminate).
  destruct (rm_match_first h ks ku L (-1) HkL) as [(Hn1 & Hf1) | (p & Hp)].
  - (* not present *)
    rewrite Hn1 in Hw.
    assert (Hno : forall s, ~ holds e h ks S ku s).
    { destruct Hres as [(_ & H2) | H1]; [exact H2|]. rewrite Hf1 in H1. destruct H1 as (HS & _). apply Lv_range in HS. lia. }
    assert (Ev : a_get h A ku = VNull) by (subst A; apply G1; intros s _; apply Hno).
    assert (Er : a_remove h A ku = A) by (subst A; apply R1; intros s _; apply Hno).
    rewrite Ev, Er.
    eapply returns_weaken.
    { apply (remove_spec e h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks vs cn pw i None);
        try assumption; try lia.
      pose proof (Lv_length ks (Z.to_nat u) 0). fold S in H. subst sz. change MAX_ARRAY with 1048576 in HKmax.
      change INT_MAX with 2147483647. clear -H Hu HKmax. lia. }
    intros s' (P1 & P2 & P3 & P4). rewrite P4.
    split; [|split; [intros y u0; reflexivity | auto]].
    exists tA, kA, vA, cA, sz, u, af, tbl, ks, vs, cn, pw. repeat (split; [assumption|]). exact HA.
  - (* present in slot c = first_match *)
    set (c := first_match e h ks ku L) in *.
    rewrite Hp in Hw.
    destruct (rm_match_found e h ks ku L (-1) p c Hp) as (HcL & uc & Huc & Euc).
    assert (HcS : In c S) by (apply Hm' in HcL; tauto).
    assert (Hhold : holds e h ks S ku c) by (split; [exact HcS | exists uc; auto]).
    assert (Hcr : 0 <= c < u) by (apply Lv_range in HcS; lia).
    destruct (chain_next cn i L c Hc HcL) as (j & Hj & _).
    destruct (remove_ok e good h ks cn tbl pw S ku i p c j Htbl Hkeys Hg ltac:(lia) ltac:(lia) Hb Hw Hj)
      as (_ & Htbl' & Hkeys').
    assert (Ev : a_get h A ku = nth (Z.to_nat c) vs VNull) by (subst A; apply G2; assumption).
    assert (Er : a_remove h A ku = entries ks vs (remove Z.eq_dec c S)) by (subst A; apply R2; assumption).
    rewrite Ev, Er.
    eapply returns_weaken.
    { apply (remove_spec e h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks vs cn pw i (Some (p, c)));
        try assumption; try lia.
      pose proof (Lv_length ks (Z.to_nat u) 0). fold S in H. subst sz. change MAX_ARRAY with 1048576 in HKmax.
      change INT_MAX with 2147483647. clear -H Hu HKmax. lia. }
    intros s' (P1 & P2 & P3 & (j' & Hj' & P4)). rewrite Hj in Hj'. injection Hj' as <-.
    rewrite P4.
    set (b := cih_spec e ku mod 2 ^ pw) in *.
    set (H' := rm_heap h m tA kA vA cA sz u thr af tbl ks vs cn b p c j).
    set (tbl' := if p =? -1 then set_nth_z tbl b (VInt j) else tbl) in *.
    set (cn' := if p =? -1 then cn else set_nth_z cn p (VInt j)) in *.
    assert (F_m : H' m = Some (OObj CIM (cim_fields tA kA vA cA (sz - 1) u thr af))) by (unfold H', rm_heap; apply upd_same).
    assert (F_v : H' vA = Some (OArr (TRef OBJ) (set_nth_z vs c VNull)))
      by (unfold H', rm_heap; rewrite upd_other by congruence; apply upd_same).
    assert (F_k : H' kA = Some (OArr (TRef STR) (set_nth_z ks c VNull)))
      by (unfold H', rm_heap; rewrite !upd_other by congruence; apply upd_same).
    assert (F_t : H' tA = Some (OArr TInt tbl')).
    { unfold H', rm_heap, tbl'. rewrite !upd_other by congruence. destruct (p =? -1); [apply upd_same | rewrite upd_other by congruence; exact HtA]. }
    assert (F_c : H' cA = Some (OArr TInt cn')).
    { unfold H', rm_heap, cn'. rewrite !upd_other by congruence. destruct (p =? -1); [rewrite upd_other by congruence; exact HcA | apply upd_same]. }
    assert (F_o : forall y, y <> m -> y <> tA -> y <> kA -> y <> vA -> y <> cA -> H' y = h y).
    { intros y Y1 Y2 Y3 Y4 Y5. unfold H', rm_heap. rewrite !upd_other by congruence. destruct (p =? -1); apply upd_other; congruence. }
    assert (Hsame : same_strings h H').
    { intros y u0. destruct (Z.eq_dec y m) as [->|N1]; [rewrite F_m, Hm; split; discriminate|].
      destruct (Z.eq_dec y tA) as [->|N2]; [rewrite F_t, HtA; split; discriminate|].
      destruct (Z.eq_dec y kA) as [->|N3]; [rewrite F_k, HkA; split; discriminate|].
      destruct (Z.eq_dec y vA) as [->|N4]; [rewrite F_v, HvA; split; discriminate|].
      destruct (Z.eq_dec y cA) as [->|N5]; [rewrite F_c, HcA; split; discriminate|].
      rewrite F_o by assumption. reflexivity. }
    assert (HndS' : length (remove Z.eq_dec c S) = (length S - 1)%nat) by (apply remove_length_in; assumption).
    assert (HLv : Lv (set_nth_z ks c VNull) 0 (Z.to_nat u) = remove Z.eq_dec c S) by (apply Lv_clear).
    split; [|split; [exact Hsame | auto]].
    exists tA, kA, vA, cA, (sz - 1), u, af, tbl', (set_nth_z ks c VNull), (set_nth_z vs c VNull), cn', pw.
    refine (conj F_m (conj F_t (conj F_k (conj F_v (conj F_c (conj Htc (conj _ (conj Hpw _)))))))).
    + unfold tbl'. destruct (p =? -1); [rewrite set_nth_len|]; exact Hlen.
    + rewrite !set_nth_len. split; [exact Hlk|]. split; [exact Hlv|]. split.
      { unfold cn'. destruct (p =? -1); [|rewrite set_nth_len]; exact Hlc. }
      split; [exact HKmax|]. split; [exact Hu|]. split.
      { intros q Hq. destruct (Z.eq_dec q c) as [->|Hne].
        - left. apply nth_set_same. rewrite Hlk. lia.
        - rewrite nth_set_other by congruence. apply Hsl. exact Hq. }
      split.
      { intros q Hq. rewrite nth_set_other by lia. apply Hnull. rewrite <- Hlk in Hq |- *. lia. }
      rewrite HLv. split.
      { rewrite HndS'. subst sz. assert (length S > 0)%nat by (destruct S; [destruct HcS | cbn; lia]). lia. }
      split; [apply (tbl_ok_same h H'); assumption|].
      split; [apply (keys_ok_same h H'); assumption|].
      split; [apply allrefs_set_null; exact Hrefs|].
      symmetry. apply entries_set_other; [lia|].
      intros s0 Hs0. apply in_rm_iff in Hs0 as (Hs0 & Hne). apply Lv_range in Hs0. split; [lia | exact Hne].
Qed.


(** ** put *)
Fixpoint a_mem (h : heap) (A : list (Z * value)) (q : list Z) : bool :=
  match A with
  | [] => false
  | (k, _) :: r => match kunits h k with Some u => eqic e u q || a_mem h r q | None => a_mem h r q end
  end.

Fixpoint a_set (h : heap) (A : list (Z * value)) (q : list Z) (v : value) : list (Z * value) :=
  match A with
  | [] => []
  | (k, w) :: r => match kunits h k with Some u => if eqic e u q then (k, v) :: r else (k, w) :: a_set h r q v | None => (k, w) :: a_set h r q v end
  end.

Lemma a_mem_entries : forall h ks vs S q, keyed h ks S ->
  forall S', (forall s, In s S' -> In s S) ->
  (a_mem h (entries ks vs S') q = true <-> exists s, In s S' /\ holds e h ks S q s).
Proof.
  intros h ks vs S q Hkd S'. induction S' as [|s0 S' IH]; intros Hsub.
  - split; [discriminate | intros (s & [] & _)].
  - destruct (Hkd s0 (Hsub s0 (or_introl eq_refl))) as (u0 & Hu0).
    cbn [entries map a_mem]. rewrite (key_at_ref h ks s0 u0 Hu0).
    specialize (IH (fun x Hx => Hsub x (or_intror Hx))).
    rewrite orb_true_iff, IH. split.
    + intros [E|(s & Hs & Hh)]; [exists s0; split; [left; reflexivity | split; [apply Hsub; left; reflexivity | exists u0; auto]] | exists s; split; [right; exact Hs | exact Hh]].
    + intros (s & [<-|Hs] & Hh); [left; destruct Hh as (_ & u & Hu & E); rewrite Hu0 in Hu; injection Hu as <-; exact E | right; exists s; auto].
Qed.

Lemma nth_set_nat_same : forall (l : list value) i w d, 0 <= i -> (Z.to_nat i < length l)%nat ->
  nth (Z.to_nat i) (set_nth_z l i w) d = w.
Proof.
  induction l as [|x r IHl]; intros i w d Hi Hil; cbn in Hil; [lia|]. cbn [set_nth_z].
  destruct (Z.eqb_spec i 0) as [->|Hne']; [reflexivity|].
  replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. cbn. apply IHl; lia.
Qed.

Lemma a_set_entries : forall h ks vs S q v,
  keys_ok e good h ks S -> keyed h ks S -> good q ->
  forall S', (forall s, In s S' -> In s S) -> (forall s, In s S' -> 0 <= s) -> NoDup S' ->
  forall c, In c S' -> holds e h ks S q c -> (Z.to_nat c < length vs)%nat ->
  a_set h (entries ks vs S') q v = entries ks (set_nth_z vs c v) S'.
Proof.
  intros h ks vs S q v Hk Hkd Hq S'. induction S' as [|s0 S' IH]; intros Hsub Hpos Hnd c Hc Hh Hcl; [destruct Hc|].
  inversion Hnd as [|x l Hx Hnd']; subst.
  destruct (Hkd s0 (Hsub s0 (or_introl eq_refl))) as (u0 & Hu0).
  cbn [entries map a_set]. rewrite (key_at_ref h ks s0 u0 Hu0).
  pose proof Hh as (HS & u & Hu & Eu).
  assert (Hrest : forall S'', (forall s, In s S'' -> 0 <= s /\ s <> c) -> entries ks (set_nth_z vs c v) S'' = entries ks vs S'').
  { intros S''. induction S'' as [|s1 S'' IH2]; intros H2; [reflexivity|]. cbn [entries map].
    destruct (H2 s1 (or_introl eq_refl)) as (P1 & P2). f_equal.
    - f_equal. apply nth_set_nat_other; [apply Hpos; exact Hc | exact P1 | congruence].
    - apply IH2. intros x0 Hx0. apply H2. right. exact Hx0. }
  destruct (Z.eq_dec s0 c) as [->|Hne].
  - rewrite Hu0 in Hu. injection Hu as <-. rewrite Eu. f_equal.
    + f_equal. symmetry. apply nth_set_nat_same; [apply Hpos; left; reflexivity | exact Hcl].
    + symmetry. apply Hrest. intros x0 Hx0. split; [apply Hpos; right; exact Hx0 | intro E; subst; contradiction].
  - destruct (eqic e u0 q) eqn:E.
    + exfalso. destruct Hk as (Hg & Hd).
      destruct (Hg s0 (Hsub s0 (or_introl eq_refl))) as (u0' & Hu0' & G0). rewrite Hu0 in Hu0'. injection Hu0' as <-.
      destruct (Hg c HS) as (u' & Hu' & G). rewrite Hu in Hu'. injection Hu' as <-.
      assert (E2 : eqic e u0 u = true) by (apply (eq_trans u0 q u); auto; rewrite eq_sym by assumption; exact Eu).
      apply Hne. eapply Hd; [apply Hsub; left; reflexivity | exact HS | exact Hu0 | exact Hu | exact E2].
    + f_equal.
      * f_equal. symmetry. apply nth_set_nat_other; [apply Hpos; exact Hc | apply Hpos; left; reflexivity | congruence].
      * apply IH; try assumption.
        -- intros x0 Hx0. apply Hsub. right. exact Hx0.
        -- intros x0 Hx0. apply Hpos. right. exact Hx0.
        -- destruct Hc as [E'|Hc]; [congruence | exact Hc].
Qed.


Lemma allrefs_set : forall vs c v, allrefs vs -> (match v with VNull | VRef _ => true | _ => false end) = true ->
  allrefs (set_nth_z vs c v).
Proof.
  intros vs c v H Hv i w Hi. destruct (Z.eq_dec i c) as [->|Hne].
  - destruct (Z_lt_le_dec c 0).
    + exfalso. apply nth_z_bounds in Hi. lia.
    + destruct (Nat.lt_ge_cases (Z.to_nat c) (length vs)).
      * rewrite nth_set_same in Hi by lia. injection Hi as <-. exact Hv.
      * apply nth_z_bounds in Hi. rewrite set_nth_len in Hi. lia.
  - rewrite nth_set_other in Hi by congruence. apply (H i w Hi).
Qed.

Theorem put_present_map : forall h n sts ini lk m k ku v A K thr,
  cim_rep h m A K thr ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> good ku ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  vok h v -> a_mem h A ku = true ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some (a_get h A ku))
    (fun s' => cim_rep (ms_heap s') m (a_set h A ku v) K thr /\ same_strings h (ms_heap s') /\
               ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku v A K thr Hrep Hk Hmax Hg He Hi HK Hv Hmem.
  destruct Hrep as (tA & kA & vA & cA & sz & u & af & tbl & ks & vs & cn & pw &
                    Hm & HtA & HkA & HvA & HcA & Htc & Hlen & Hpw & Hlk & Hlv & Hlc & HKmax & Hu & Hsl & Hnull & Hsz & Htbl & Hkeys & Hrefs & HA).
  set (S := Lv ks 0 (Z.to_nat u)) in *.
  assert (HndS : NoDup S) by apply Lv_NoDup.
  destruct (find_correct e good eq_hash h ks cn tbl pw S ku Htbl Hkeys Hg ltac:(lia)) as (i & L & Hb & Hc & HlL & Hres).
  pose proof Htbl as (Hkd & Ht).
  assert (Hbb : 0 <= bucket e ku pw < 2 ^ pw) by (unfold bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (Ht _ Hbb) as (i' & L' & Hb' & Hc' & Hnd' & Hm').
  rewrite Hb in Hb'. injection Hb' as <-. assert (HL : L = L') by (eapply chain_unique; eassumption). subst L'.
  assert (HkL : keyed h ks L) by (intros s Hs; apply Hkd; apply Hm' in Hs; tauto).
  assert (Hw : fi_walk e h ks cn ku i (Datatypes.S (length ks)) = Some (first_match e h ks ku L))
    by (apply fi_walk_chain; [exact Hc | exact HkL | lia]).
  subst A. apply (a_mem_entries h ks vs S ku Hkd S (fun s Hs => Hs)) in Hmem as (c0 & Hc0 & Hh0).
  set (c := first_match e h ks ku L) in *.
  assert (Hhold : holds e h ks S ku c) by (destruct Hres as [(_ & H2) | H1]; [exfalso; exact (H2 c0 Hh0) | exact H1]).
  assert (HcS : In c S) by (destruct Hhold; assumption).
  assert (Hcr : 0 <= c < u) by (apply Lv_range in HcS; lia).
  destruct (nth_z_exists vs c ltac:(rewrite Hlv; lia)) as (old & Hold).
  assert (Hval : nth (Z.to_nat c) vs VNull = old) by (apply nth_z_nth; exact Hold).
  destruct (a_get_entries h ks vs S ku Hkeys Hkd Hg S (fun s Hs => Hs)) as (_ & G2).
  rewrite (G2 c HcS Hhold), Hval.
  assert (Hvr : (match v with VNull | VRef _ => true | _ => false end) = true) by (destruct v; try contradiction; reflexivity).
  eapply returns_weaken.
  { apply (put_present e h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i c old); try assumption.
    - lia.
    - exact (Hrefs c old Hold). }
  intros s' (P1 & P2 & P3 & P4). rewrite P1.
  assert (Hmv : m <> vA) by (intro E; subst; rewrite Hm in HvA; discriminate).
  assert (Htv : tA <> vA) by (intro E; subst; rewrite HtA in HvA; discriminate).
  assert (Hkv : kA <> vA) by (intro E; subst; rewrite HkA in HvA; discriminate).
  assert (Hcv : cA <> vA) by (intro E; subst; rewrite HcA in HvA; discriminate).
  split; [|split; [apply (same_upd_obj h vA (OArr (TRef OBJ) vs)); [exact HvA | exact I | exact I] | auto]].
  exists tA, kA, vA, cA, sz, u, af, tbl, ks, (set_nth_z vs c v), cn, pw.
  set (X := OArr (TRef OBJ) (set_nth_z vs c v)).
  assert (F1 : upd h vA X m = h m) by (apply upd_other; exact Hmv).
  assert (F2 : upd h vA X tA = h tA) by (apply upd_other; exact Htv).
  assert (F3 : upd h vA X kA = h kA) by (apply upd_other; exact Hkv).
  assert (F4 : upd h vA X cA = h cA) by (apply upd_other; exact Hcv).
  rewrite F1, F2, F3, F4, upd_same.
  refine (conj Hm (conj HtA (conj HkA (conj eq_refl (conj HcA (conj Htc (conj Hlen (conj Hpw (conj Hlk _))))))))).
  rewrite set_nth_len. refine (conj Hlv (conj Hlc (conj HKmax (conj Hu (conj Hsl (conj Hnull (conj Hsz _))))))).
  split; [apply (tbl_ok_same h); [apply same_upd_obj with (OArr (TRef OBJ) vs); [exact HvA | exact I | exact I] | exact Htbl]|].
  split; [apply (keys_ok_same h); [apply same_upd_obj with (OArr (TRef OBJ) vs); [exact HvA | exact I | exact I] | exact Hkeys]|].
  split; [apply allrefs_set; assumption|].
  apply (a_set_entries h ks vs S ku v Hkeys Hkd Hg S (fun s Hs => Hs)); try assumption.
  - intros s0 Hs0. apply Lv_range in Hs0. lia.
  - rewrite Hlv. lia.
Qed.

End Map.

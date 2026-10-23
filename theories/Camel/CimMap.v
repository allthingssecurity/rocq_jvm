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
Definition cim_rep (h : heap) (m : Z) (A : list (Z * value)) (K : nat) : Prop :=
  exists tA kA vA cA sz u thr af tbl ks vs cn pw,
    h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) /\
    h tA = Some (OArr TInt tbl) /\ h kA = Some (OArr (TRef STR) ks) /\
    h vA = Some (OArr (TRef OBJ) vs) /\ h cA = Some (OArr TInt cn) /\ tA <> cA /\
    Z.of_nat (length tbl) = 2 ^ pw /\ 0 <= pw <= 30 /\
    length ks = K /\ length vs = K /\ length cn = K /\
    0 <= u <= Z.of_nat K /\ slots_ok ks 0 (Z.to_nat u) /\
    (forall q, u <= q < Z.of_nat K -> nth_z ks q = Some VNull) /\
    sz = Z.of_nat (length (Lv ks 0 (Z.to_nat u))) /\
    tbl_ok e h ks cn tbl pw (Lv ks 0 (Z.to_nat u)) /\ keys_ok e good h ks (Lv ks 0 (Z.to_nat u)) /\
    allrefs vs /\
    A = entries ks vs (Lv ks 0 (Z.to_nat u)).

Theorem get_map : forall h n sts ini lk m k ku A K,
  cim_rep h m A K ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> good ku ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [get_frame m k] |}
    (Some (a_get h A ku))
    (fun s' => ms_heap s' = h /\ ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku A K Hrep Hk Hmax Hg He Hi.
  destruct Hrep as (tA & kA & vA & cA & sz & u & thr & af & tbl & ks & vs & cn & pw &
                    Hm & HtA & HkA & HvA & HcA & Htc & Hlen & Hpw & Hlk & Hlv & Hlc & Hu & Hsl & Hnull & Hsz & Htbl & Hkeys & Hrefs & HA).
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

End Map.

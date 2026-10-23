(** * CaseInsensitiveMap (fix): what the three loops of compactRemovedSlots compute.

    [c1_ok]: loop 1 numbers the used slots 0, 1, 2, ... in slot order.
    [c2_ok]: loop 2 renumbers every bucket head. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Semantics Machine.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimRemove CimCompact CimAbs.
Import ListNotations.
Open Scope Z_scope.

Definition nonnull (o : option value) : bool := match o with Some (VRef _) => true | _ => false end.

(** The used slots among [i, i + f), in order. *)
Definition Lv (ks : list value) (i : Z) (f : nat) : list Z :=
  filter (fun p => nonnull (nth_z ks p)) (map (fun k => i + Z.of_nat k) (seq 0 f)).

Lemma map_shift : forall i f, map (fun k => i + Z.of_nat k) (seq 1 f) = map (fun k => (i + 1) + Z.of_nat k) (seq 0 f).
Proof.
  intros i f. rewrite <- seq_shift, map_map. apply map_ext. intros k. lia.
Qed.

Lemma Lv_S : forall ks i f, Lv ks i (S f) = if nonnull (nth_z ks i) then i :: Lv ks (i + 1) f else Lv ks (i + 1) f.
Proof.
  intros ks i f. unfold Lv. cbn [seq map filter]. rewrite Z.add_0_r, map_shift. reflexivity.
Qed.

Lemma Lv_range : forall ks f i p, In p (Lv ks i f) -> i <= p < i + Z.of_nat f.
Proof.
  intros ks f i p H. unfold Lv in H. apply filter_In in H as (H & _).
  apply in_map_iff in H as (k & <- & Hk). apply in_seq in Hk. lia.
Qed.

Lemma Lv_nonnull : forall ks f i p, In p (Lv ks i f) -> nonnull (nth_z ks p) = true.
Proof. intros ks f i p H. unfold Lv in H. apply filter_In in H. tauto. Qed.

Lemma Lv_complete : forall ks f i p, i <= p < i + Z.of_nat f -> nonnull (nth_z ks p) = true -> In p (Lv ks i f).
Proof.
  intros ks f i p Hp Hn. unfold Lv. apply filter_In. split; [|exact Hn].
  apply in_map_iff. exists (Z.to_nat (p - i)). split; [lia|]. apply in_seq. lia.
Qed.

(** Every slot in range holds a key or null. *)
Definition slots_ok (ks : list value) (i : Z) (f : nat) : Prop :=
  forall p, i <= p < i + Z.of_nat f -> nth_z ks p = Some VNull \/ exists kl, nth_z ks p = Some (VRef kl).

Lemma c1_ok : forall ks f i cnt ni,
  slots_ok ks i f -> 0 <= i -> i + Z.of_nat f <= Z.of_nat (length ni) ->
  exists ni', c1 ks i f cnt ni = Some (cnt + Z.of_nat (length (Lv ks i f)), ni') /\
    length ni' = length ni /\
    (forall j p, nth_error (Lv ks i f) j = Some p -> nth_z ni' p = Some (VInt (cnt + Z.of_nat j))) /\
    (forall p, ~ In p (Lv ks i f) -> nth_z ni' p = nth_z ni p).
Proof.
  intros ks f. induction f as [|f IH]; intros i cnt ni Hs Hi Hl.
  - exists ni. cbn. rewrite Z.add_0_r. split; [reflexivity|]. split; [reflexivity|].
    split; [intros [|j] p H; discriminate | reflexivity].
  - cbn [c1]. rewrite Lv_S.
    assert (Hs' : slots_ok ks (i + 1) f) by (intros p Hp; apply Hs; lia).
    destruct (Hs i ltac:(lia)) as [E|(kl & E)]; rewrite E; cbn [nonnull].
    + destruct (IH (i + 1) cnt ni Hs' ltac:(lia) ltac:(lia)) as (ni' & H1 & H2 & H3 & H4).
      exists ni'. auto.
    + replace ((0 <=? i) && (i <? Z.of_nat (length ni))) with true
        by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      destruct (IH (i + 1) (cnt + 1) (set_nth_z ni i (VInt cnt)) Hs' ltac:(lia) ltac:(rewrite set_nth_len; lia))
        as (ni' & H1 & H2 & H3 & H4).
      exists ni'. split; [rewrite H1; f_equal; f_equal; cbn [length]; rewrite Nat2Z.inj_succ; lia|].
      split; [rewrite H2, set_nth_len; reflexivity|].
      split.
      * intros [|j] p Hj; cbn in Hj.
        -- injection Hj as <-. rewrite H4.
           ++ rewrite nth_set_same by lia. f_equal. f_equal. lia.
           ++ intro Hin. apply Lv_range in Hin. lia.
        -- rewrite (H3 j p Hj). f_equal. f_equal. lia.
      * intros p Hp. rewrite H4 by (intro Hin; apply Hp; right; exact Hin).
        apply nth_set_other. intro E'; apply Hp; left; exact E'.
Qed.

(** The renumbering of a slot index (-1 stays -1). *)
Definition rn (ni : list value) (x : Z) : option Z :=
  if x =? -1 then Some (-1) else match nth_z ni x with Some (VInt y) => Some y | _ => None end.

Lemma c2_ok : forall ni f tbl b,
  (forall p, b <= p < b + Z.of_nat f -> exists x y, nth_z tbl p = Some (VInt x) /\ rn ni x = Some y) ->
  exists tbl', c2 ni tbl b f = Some tbl' /\ length tbl' = length tbl /\
    (forall p, b <= p < b + Z.of_nat f -> exists x y, nth_z tbl p = Some (VInt x) /\ rn ni x = Some y /\ nth_z tbl' p = Some (VInt y)) /\
    (forall p, ~ (b <= p < b + Z.of_nat f) -> nth_z tbl' p = nth_z tbl p).
Proof.
  intros ni f. induction f as [|f IH]; intros tbl b Hv.
  - exists tbl. cbn. split; [reflexivity|]. split; [reflexivity|]. split; [intros p Hp; lia | reflexivity].
  - cbn [c2]. destruct (Hv b ltac:(lia)) as (x & y & Ex & Ey). rewrite Ex.
    unfold rn in Ey.
    destruct (x =? -1) eqn:Ex1.
    + injection Ey as <-.
      destruct (IH tbl (b + 1) ltac:(intros p Hp; apply Hv; lia)) as (t' & H1 & H2 & H3 & H4).
      exists t'. split; [exact H1|]. split; [exact H2|]. split.
      * intros p Hp. destruct (Z.eq_dec p b) as [->|Hne].
        -- exists x, (-1). split; [exact Ex|]. split; [unfold rn; rewrite Ex1; reflexivity|].
           rewrite H4 by lia. rewrite Ex. apply Z.eqb_eq in Ex1. subst x. reflexivity.
        -- apply H3. lia.
      * intros p Hp. apply H4. lia.
    + destruct (nth_z ni x) as [[y'|z|z|z| |z|]|] eqn:Ey'; try discriminate. injection Ey as <-.
      destruct (IH (set_nth_z tbl b (VInt y')) (b + 1)) as (t' & H1 & H2 & H3 & H4).
      { intros p Hp. rewrite nth_set_other by lia. apply Hv. lia. }
      exists t'. split; [exact H1|]. split; [rewrite H2, set_nth_len; reflexivity|]. split.
      * intros p Hp. destruct (Z.eq_dec p b) as [->|Hne].
        -- exists x, y'. split; [exact Ex|]. split; [unfold rn; rewrite Ex1, Ey'; reflexivity|].
           rewrite H4 by lia. apply nth_set_same. pose proof (nth_z_bounds _ _ _ Ex). lia.
        -- destruct (H3 p ltac:(lia)) as (x2 & y2 & E1 & E2 & E3). exists x2, y2.
           rewrite nth_set_other in E1 by lia. auto.
      * intros p Hp. rewrite H4 by lia. apply nth_set_other. lia.
Qed.

Section C3.
Variables (h : heap) (kA vA cA niA tA : Z) (ni ks0 vs0 cn0 : list value).

(** What loop 3 needs about a used slot [p]. *)
Definition slot_good (p : Z) : Prop :=
  exists j kl ku nx y vv,
    nth_z ni p = Some (VInt j) /\ 0 <= j <= p /\
    j < Z.of_nat (length ks0) /\ j < Z.of_nat (length vs0) /\ j < Z.of_nat (length cn0) /\
    nth_z ks0 p = Some (VRef kl) /\ h kl = Some (OStr ku) /\ not_in4 kA vA cA niA tA (VRef kl) = true /\
    nth_z cn0 p = Some (VInt nx) /\ rn ni nx = Some y /\
    nth_z vs0 p = Some vv /\ vok_b h vv = true /\ not_in4 kA vA cA niA tA vv = true.

Definition rank_of (p : Z) : Z := match nth_z ni p with Some (VInt j) => j | _ => -1 end.
Definition next_of (p : Z) : Z :=
  match nth_z cn0 p with Some (VInt nx) => match rn ni nx with Some y => y | None => -1 end | _ => -1 end.

Lemma c3_ok : forall f i ksc vsc cnc,
  (forall p, i <= p -> nth_z ksc p = nth_z ks0 p /\ nth_z vsc p = nth_z vs0 p /\ nth_z cnc p = nth_z cn0 p) ->
  length ksc = length ks0 -> length vsc = length vs0 -> length cnc = length cn0 ->
  slots_ok ks0 i f -> (forall p, In p (Lv ks0 i f) -> slot_good p) ->
  (forall p q, In p (Lv ks0 i f) -> In q (Lv ks0 i f) -> rank_of p = rank_of q -> p = q) ->
  exists ks' vs' cn', c3 h kA vA cA niA tA ni i f ksc vsc cnc = Some (ks', vs', cn') /\
    length ks' = length ks0 /\ length vs' = length vs0 /\ length cn' = length cn0 /\
    (forall p, In p (Lv ks0 i f) -> nth_z ks' (rank_of p) = nth_z ks0 p /\ nth_z vs' (rank_of p) = nth_z vs0 p /\
                                    nth_z cn' (rank_of p) = Some (VInt (next_of p))) /\
    (forall q, (forall p, In p (Lv ks0 i f) -> rank_of p <> q) ->
       nth_z ks' q = nth_z ksc q /\ nth_z vs' q = nth_z vsc q /\ nth_z cn' q = nth_z cnc q).
Proof.
  intros f. induction f as [|f IH]; intros i ksc vsc cnc Hsame Hlk Hlv Hlc Hs Hg Hinj.
  - exists ksc, vsc, cnc. refine (conj eq_refl (conj Hlk (conj Hlv (conj Hlc (conj _ _))))); [intros p [] | intros q _; auto].
  - cbn [c3].
    assert (Hs' : slots_ok ks0 (i + 1) f) by (intros p Hp; apply Hs; lia).
    destruct (Hsame i ltac:(lia)) as (Ek & Ev & Ec).
    pose proof (Lv_S ks0 i f) as HL.
    destruct (Hs i ltac:(lia)) as [E|(kl & E)].
    + (* empty slot *)
      rewrite Ek, E. rewrite E in HL. cbn [nonnull] in HL. rewrite HL in Hg, Hinj |- *.
      apply IH; try assumption. intros p Hp. apply Hsame. lia.
    + rewrite E in HL. cbn [nonnull] in HL. rewrite HL in Hg, Hinj |- *.
      destruct (Hg i (or_introl eq_refl)) as (j & kl' & ku & nx & y & vv & Hj & Hj0 & Hjk & Hjv & Hjc & Ekl & Hku & Hn1 & Enx & Ey & Evv & Hvok & Hn2).
      rewrite E in Ekl. injection Ekl as <-.
      rewrite Ek, E, Hj. rewrite Ec, Enx. rewrite Ev, Evv. rewrite Hku.
      unfold rn in Ey.
      assert (Hny : (if nx =? -1 then Some (-1) else match nth_z ni nx with Some (VInt y0) => Some y0 | _ => None end) = Some y) by exact Ey.
      rewrite Hny.
      replace ((0 <=? j) && (j <? Z.of_nat (length cnc)) && (j <? Z.of_nat (length ksc)) && (j <? Z.of_nat (length vsc))
               && vok_b h vv && not_in4 kA vA cA niA tA vv && not_in4 kA vA cA niA tA (VRef kl)) with true
        by (symmetry; rewrite Hlc, Hlk, Hlv, Hvok, Hn1, Hn2;
            repeat rewrite andb_true_r; repeat (apply andb_true_iff; split); try apply Z.leb_le; try apply Z.ltb_lt; lia).
      destruct (IH (i + 1) (set_nth_z ksc j (VRef kl)) (set_nth_z vsc j vv) (set_nth_z cnc j (VInt y)))
        as (ks' & vs' & cn' & H1 & H2 & H3 & H4 & H5 & H6).
      * intros p Hp. rewrite !nth_set_other by lia. apply Hsame. lia.
      * rewrite set_nth_len. exact Hlk.
      * rewrite set_nth_len. exact Hlv.
      * rewrite set_nth_len. exact Hlc.
      * exact Hs'.
      * intros p Hp. apply Hg. right. exact Hp.
      * intros p q Hp Hq. apply Hinj; right; assumption.
      * exists ks', vs', cn'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
        assert (Hrank : rank_of i = j) by (unfold rank_of; rewrite Hj; reflexivity).
        assert (Hnotr : forall p, In p (Lv ks0 (i + 1) f) -> rank_of p <> j).
        { intros p Hp Hr. assert (p = i) by (apply Hinj; [right; exact Hp | left; reflexivity | rewrite Hrank; exact Hr]).
          subst p. apply Lv_range in Hp. lia. }
        split.
        -- intros p [<-|Hp].
           ++ rewrite Hrank. destruct (H6 j Hnotr) as (K1 & K2 & K3).
              rewrite K1, K2, K3. rewrite !nth_set_same by lia.
              split; [rewrite E; reflexivity|]. split; [rewrite Evv; reflexivity|].
              unfold next_of. rewrite Enx. unfold rn. rewrite Hny. reflexivity.
           ++ apply H5. exact Hp.
        -- intros q Hq. destruct (H6 q (fun p Hp => Hq p (or_intror Hp))) as (K1 & K2 & K3).
           assert (Hqj : q <> j) by (intro E'; subst q; apply (Hq i (or_introl eq_refl)); exact Hrank).
           rewrite K1, K2, K3. rewrite !nth_set_other by congruence. auto.
Qed.

End C3.

Lemma Lv_nth_ge : forall ks f i j p, nth_error (Lv ks i f) j = Some p -> i + Z.of_nat j <= p.
Proof.
  intros ks f. induction f as [|f IH]; intros i j p H; [destruct j; discriminate|].
  rewrite Lv_S in H. destruct (nonnull (nth_z ks i)).
  - destruct j as [|j]; cbn in H.
    + injection H as <-. lia.
    + apply IH in H. lia.
  - apply IH in H. lia.
Qed.

Lemma Lv_NoDup : forall ks f i, NoDup (Lv ks i f).
Proof.
  intros ks f. induction f as [|f IH]; intros i; [constructor|].
  rewrite Lv_S. destruct (nonnull (nth_z ks i)); [|apply IH].
  constructor; [|apply IH]. intro Hin. apply Lv_range in Hin. lia.
Qed.

(** In a chain, the successor of a slot is -1 or the next slot of the chain. *)
Lemma chain_next : forall cn i L p, chain cn i L -> In p L ->
  exists nx, nth_z cn p = Some (VInt nx) /\ (nx = -1 \/ In nx L).
Proof.
  intros cn i L p H. induction H as [|i j L Hi Hn Hc IH]; intros Hp; [destruct Hp|].
  destruct Hp as [<-|Hp].
  - exists j. split; [exact Hn|]. destruct Hc as [|j' j'' L' Hj' Hn' Hc']; [left; reflexivity | right; right; left; reflexivity].
  - destruct (IH Hp) as (nx & H1 & [H2|H2]); exists nx; split; auto. right; right; exact H2.
Qed.

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

(** ** fill_null *)
Lemma nth_z_app_l : forall {A} (l1 l2 : list A) i, 0 <= i < Z.of_nat (length l1) -> nth_z (app l1 l2) i = nth_z l1 i.
Proof.
  intros A l1. induction l1 as [|x r IH]; intros l2 i Hi; cbn in *; [lia|].
  destruct (Z.eqb_spec i 0); [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_z_app_r : forall {A} (l1 l2 : list A) i, Z.of_nat (length l1) <= i -> nth_z (app l1 l2) i = nth_z l2 (i - Z.of_nat (length l1)).
Proof.
  intros A l1. induction l1 as [|x r IH]; intros l2 i Hi; cbn in *; [f_equal; lia|].
  replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite IH by lia. f_equal. lia.
Qed.

Lemma nth_z_firstn : forall {A} (l : list A) n i, 0 <= i < Z.of_nat n -> nth_z (firstn n l) i = nth_z l i.
Proof.
  intros A l. induction l as [|x r IH]; intros n i Hi; destruct n; cbn in *; try lia; try reflexivity.
  destruct (Z.eqb_spec i 0); [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_z_skipn : forall {A} (l : list A) n i, 0 <= i -> nth_z (skipn n l) i = nth_z l (i + Z.of_nat n).
Proof.
  intros A l. induction l as [|x r IH]; intros n i Hi; destruct n; cbn [skipn]; try reflexivity.
  - f_equal. lia.
  - rewrite Nat2Z.inj_succ. cbn [nth_z]. destruct (Z.eqb_spec (i + Z.succ (Z.of_nat n)) 0); [lia|].
    rewrite IH by lia. f_equal. lia.
Qed.

Lemma fill_null_lo : forall es f t q, 0 <= f <= t -> t <= Z.of_nat (length es) -> 0 <= q < f ->
  nth_z (fill_null es f t) q = nth_z es q.
Proof.
  intros es f t q Hf Ht Hq. unfold fill_null.
  rewrite nth_z_app_l by (rewrite firstn_length; lia). apply nth_z_firstn. lia.
Qed.

Lemma fill_null_hi : forall es f t q, 0 <= f <= t -> t <= Z.of_nat (length es) -> t <= q ->
  nth_z (fill_null es f t) q = nth_z es q.
Proof.
  intros es f t q Hf Ht Hq. unfold fill_null.
  rewrite nth_z_app_r by (rewrite firstn_length; lia). rewrite firstn_length.
  rewrite nth_z_app_r by (rewrite repeat_length; lia). rewrite repeat_length.
  rewrite nth_z_skipn by lia. f_equal. lia.
Qed.

Lemma fill_null_length' : forall es f t, 0 <= f <= t -> t <= Z.of_nat (length es) -> length (fill_null es f t) = length es.
Proof. intros es f t Hf Ht. unfold fill_null. rewrite !app_length, repeat_length, firstn_length, skipn_length. lia. Qed.

Lemma fill_null_mid : forall es f t q, 0 <= f <= q -> q < t -> t <= Z.of_nat (length es) ->
  nth_z (fill_null es f t) q = Some VNull.
Proof.
  intros es f t q Hf Hq Ht. unfold fill_null.
  assert (Hgen2 : forall {A} (l1 l2 : list A) i, Z.of_nat (length l1) <= i -> nth_z (app l1 l2) i = nth_z l2 (i - Z.of_nat (length l1))).
  { intros A l1. induction l1 as [|x r IH]; intros l2 i Hi; cbn in *; [f_equal; lia|].
    replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite IH by lia. f_equal. lia. }
  assert (Hgen : forall {A} (l1 l2 : list A) i, 0 <= i < Z.of_nat (length l1) -> nth_z (app l1 l2) i = nth_z l1 i).
  { intros A l1. induction l1 as [|x r IH]; intros l2 i Hi; cbn in *; [lia|].
    destruct (Z.eqb_spec i 0); [reflexivity|]. apply IH. lia. }
  rewrite Hgen2 by (rewrite firstn_length; lia). rewrite firstn_length. replace (Nat.min (Z.to_nat f) (length es)) with (Z.to_nat f) by lia.
  rewrite Hgen by (rewrite repeat_length; lia).
  assert (Hrep : forall n i, 0 <= i < Z.of_nat n -> nth_z (repeat VNull n) i = Some VNull).
  { intros n. induction n as [|n IH]; intros i Hi; cbn in *; [lia|]. destruct (Z.eqb_spec i 0); [reflexivity|]. apply IH. lia. }
  apply Hrep. lia.
Qed.

Lemma Lv_length : forall ks f i, (length (Lv ks i f) <= f)%nat.
Proof. intros. unfold Lv. etransitivity; [apply filter_length_le|]. rewrite map_length, seq_length. lia. Qed.

Lemma rn_some : forall ni x y, rn ni x = Some y -> (x = -1 /\ y = -1) \/ (x <> -1 /\ nth_z ni x = Some (VInt y)).
Proof.
  intros ni x y H. unfold rn in H. destruct (Z.eqb_spec x (-1)).
  - injection H as <-. left; auto.
  - destruct (nth_z ni x) as [[z|z|z|z| |z|]|] eqn:E; try discriminate. injection H as <-. right; auto.
Qed.

(** ** Compaction keeps the table invariant, the entries and their order *)
Section Compaction.
Variable e : jenv.
Variables (h : heap) (kA vA cA niA tA : Z).

Lemma map_rank_NoDup : forall (rk : Z -> Z) (S L : list Z),
  (forall p q, In p S -> In q S -> rk p = rk q -> p = q) -> (forall s, In s L -> In s S) -> NoDup L -> NoDup (map rk L).
Proof.
  intros rk S L Hinj Hsub Hnd. induction Hnd as [|x l Hx Hnd IH]; cbn; constructor.
  - intro Hin. apply in_map_iff in Hin as (y & Ey & Hy). apply Hx.
    replace x with y; [exact Hy|]. apply Hinj; [apply Hsub; right; exact Hy | apply Hsub; left; reflexivity | exact Ey].
  - apply IH. intros s Hs. apply Hsub. right. exact Hs.
Qed.

Theorem compact_ok : forall ks0 vs0 cn0 tbl pw u,
  length vs0 = length ks0 -> length cn0 = length ks0 -> 0 <= u <= Z.of_nat (length ks0) ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw ->
  slots_ok ks0 0 (Z.to_nat u) ->
  (forall q, u <= q < Z.of_nat (length ks0) -> nth_z ks0 q = Some VNull) ->
  tbl_ok e h ks0 cn0 tbl pw (Lv ks0 0 (Z.to_nat u)) ->
  (forall p, In p (Lv ks0 0 (Z.to_nat u)) -> exists kl vv, nth_z ks0 p = Some (VRef kl) /\ not_in4 kA vA cA niA tA (VRef kl) = true /\
       nth_z vs0 p = Some vv /\ vok_b h vv = true /\ not_in4 kA vA cA niA tA vv = true) ->
  let S := Lv ks0 0 (Z.to_nat u) in
  let n' := Z.of_nat (length S) in
  exists ni tbl' ks' vs' cn',
    c1 ks0 0 (Z.to_nat u) 0 (repeat (VInt 0) (Z.to_nat u)) = Some (n', ni) /\
    c2 ni tbl 0 (Z.to_nat (Z.of_nat (length tbl))) = Some tbl' /\
    c3 h kA vA cA niA tA ni 0 (Z.to_nat u) ks0 vs0 cn0 = Some (ks', vs', cn') /\
    length ks' = length ks0 /\ length vs' = length ks0 /\ length cn' = length ks0 /\ length tbl' = length tbl /\
    0 <= n' <= u /\
    tbl_ok e h (fill_null ks' n' u) cn' tbl' pw (map Z.of_nat (seq 0 (length S))) /\
    (forall j p, nth_error S j = Some p ->
       nth_z (fill_null ks' n' u) (Z.of_nat j) = nth_z ks0 p /\ nth_z (fill_null vs' n' u) (Z.of_nat j) = nth_z vs0 p) /\
    (forall q, n' <= q < Z.of_nat (length ks0) -> nth_z (fill_null ks' n' u) q = Some VNull).
Proof.
  intros ks0 vs0 cn0 tbl pw u Hlv Hlc Hu Hlt Hpw Hsl Hnull (Hkd & Ht) Hgood S n'.
  assert (HS : (length S <= Z.to_nat u)%nat) by apply Lv_length.
  assert (Hn' : 0 <= n' <= u) by (unfold n'; lia).
  (* loop 1 *)
  destruct (c1_ok ks0 (Z.to_nat u) 0 0 (repeat (VInt 0) (Z.to_nat u)) Hsl ltac:(lia) ltac:(rewrite repeat_length; lia))
    as (ni & Hc1 & Hlni & Hrank & Hrest).
  rewrite Z.add_0_l in Hc1. fold S in Hc1, Hrank, Hrest. fold n' in Hc1.
  assert (Hrk : forall j p, nth_error S j = Some p -> rank_of ni p = Z.of_nat j)
    by (intros j p Hj; unfold rank_of; rewrite (Hrank j p Hj); reflexivity).
  assert (HinS : forall p, In p S -> exists j, nth_error S j = Some p) by (intros p Hp; apply In_nth_error; exact Hp).
  assert (Hnd : NoDup S) by apply Lv_NoDup.
  assert (Hinj : forall p q, In p S -> In q S -> rank_of ni p = rank_of ni q -> p = q).
  { intros p q Hp Hq E. destruct (HinS p Hp) as (j1 & H1). destruct (HinS q Hq) as (j2 & H2).
    rewrite (Hrk _ _ H1), (Hrk _ _ H2) in E. apply Nat2Z.inj in E. subst j2. rewrite H1 in H2. injection H2 as ->. reflexivity. }
  assert (Hrn : forall x, x = -1 \/ In x S -> rn ni x = Some (if x =? -1 then -1 else rank_of ni x)).
  { intros x [->|Hx]; [reflexivity|].
    destruct (HinS x Hx) as (j & Hj). unfold rn, rank_of. rewrite (Hrank j x Hj).
    assert (Hx0 : x <> -1) by (apply Lv_range in Hx; lia). replace (x =? -1) with false by (symmetry; apply Z.eqb_neq; exact Hx0).
    reflexivity. }
  (* every bucket head is -1 or a used slot *)
  assert (Hhead : forall b, 0 <= b < 2 ^ pw -> exists x L, nth_z tbl b = Some (VInt x) /\ chain cn0 x L /\ NoDup L /\
             (forall s, In s L <-> In s S /\ exists ku, key_at h ks0 s = Some ku /\ bucket e ku pw = b) /\ (x = -1 \/ In x S)).
  { intros b Hb. destruct (Ht b Hb) as (x & L & H1 & H2 & H3 & H4). exists x, L.
    refine (conj H1 (conj H2 (conj H3 (conj H4 _)))).
    destruct (chain_head cn0 x L H2) as [(-> & _) | (L' & -> & _)];
      [left; reflexivity | right; exact (proj1 (proj1 (H4 x) (or_introl eq_refl)))]. }
  (* loop 2 *)
  destruct (c2_ok ni (Z.to_nat (Z.of_nat (length tbl))) tbl 0) as (tbl' & Hc2 & Hlt' & Hnew & _).
  { intros p Hp. destruct (Hhead p ltac:(lia)) as (x & L & H1 & _ & _ & _ & H5). exists x, (if x =? -1 then -1 else rank_of ni x).
    split; [exact H1 | apply Hrn; exact H5]. }
  (* loop 3 *)
  assert (Hsg : forall p, In p S -> slot_good h kA vA cA niA tA ni ks0 vs0 cn0 p).
  { intros p Hp. destruct (Hgood p Hp) as (kl & vv & Ek & Nk & Ev & Vv & Nv).
    destruct (Hkd p Hp) as (ku & Hku). unfold key_at in Hku. rewrite Ek in Hku.
    destruct (h kl) as [[| | ku' | | |]|] eqn:Ekl; try discriminate. injection Hku as Hku'. subst ku'.
    destruct (HinS p Hp) as (j & Hj).
    pose proof (Lv_nth_ge ks0 (Z.to_nat u) 0 j p Hj) as Hjp.
    assert (Hjlt : (j < length S)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    pose proof (Lv_range ks0 (Z.to_nat u) 0 p Hp) as Hpr.
    (* the successor of p *)
    assert (Hbk : 0 <= bucket e ku pw < 2 ^ pw) by (unfold bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
    destruct (Ht _ Hbk) as (x & L & _ & Hch & _ & Hm).
    assert (HpL : In p L) by (apply Hm; split; [exact Hp | exists ku; split; [unfold key_at; rewrite Ek, Ekl; reflexivity | reflexivity]]).
    destruct (chain_next cn0 x L p Hch HpL) as (nx & Enx & Hnx).
    assert (Hnx' : nx = -1 \/ In nx S) by (destruct Hnx as [->|Hnx]; [left; reflexivity | right; apply Hm in Hnx; tauto]).
    exists (Z.of_nat j), kl, ku, nx, (if nx =? -1 then -1 else rank_of ni nx), vv.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Ek (conj Ekl (conj Nk (conj Enx (conj _ (conj Ev (conj Vv Nv)))))))))))).
    - apply Hrank. exact Hj.
    - lia.
    - lia.
    - rewrite Hlv. lia.
    - rewrite Hlc. lia.
    - apply Hrn. exact Hnx'. }
  destruct (c3_ok h kA vA cA niA tA ni ks0 vs0 cn0 (Z.to_nat u) 0 ks0 vs0 cn0) as (ks' & vs' & cn' & Hc3 & Hlk' & Hlv' & Hlc' & Hmov & Hkeep).
  { intros p _. auto. }
  { reflexivity. } { reflexivity. } { reflexivity. }
  { exact Hsl. } { exact Hsg. } { exact Hinj. }
  exists ni, tbl', ks', vs', cn'.
  assert (Hlfk : length (fill_null ks' n' u) = length ks0) by (rewrite fill_null_length' by lia; exact Hlk').
  assert (HKS : forall j p, nth_error S j = Some p -> key_at h (fill_null ks' n' u) (Z.of_nat j) = key_at h ks0 p).
  { intros j p Hj. assert (Hjlt : (j < length S)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    unfold key_at. rewrite fill_null_lo by lia. rewrite <- (Hrk j p Hj).
    destruct (Hmov p ltac:(apply nth_error_In with j; exact Hj)) as (M1 & _). rewrite M1. reflexivity. }
  split; [exact Hc1|]. split; [exact Hc2|]. split; [exact Hc3|].
  split; [exact Hlk'|]. split; [rewrite Hlv'; exact Hlv|]. split; [rewrite Hlc'; exact Hlc|]. split; [exact Hlt'|].
  split; [exact Hn'|].
  split; [|split].
  - (* the new table invariant *)
    split.
    + intros t Ht'. apply in_map_iff in Ht' as (j & <- & Hj). apply in_seq in Hj.
      destruct (nth_error S j) as [p|] eqn:Ep; [|apply nth_error_None in Ep; lia].
      rewrite (HKS j p Ep). apply Hkd. apply nth_error_In with j. exact Ep.
    + intros b Hb. destruct (Hhead b Hb) as (x & L & H1 & H2 & H3 & H4 & H5).
      destruct (Hnew b ltac:(lia)) as (x' & y & E1 & E2 & E3). rewrite H1 in E1. injection E1 as <-.
      exists y, (map (rank_of ni) L). split; [exact E3|].
      assert (HLS : forall s, In s L -> In s S) by (intros s Hs; apply H4 in Hs; tauto).
      split.
      * (* the renumbered chain *)
        clear -Hrn HLS Hmov H2 E2 Hinj HinS Hrk.
        revert y E2. induction H2 as [|p j0 L' Hp Hn Hc IH]; intros y E2.
        -- cbn in E2. injection E2 as <-. constructor.
        -- assert (HpS : In p S) by (apply HLS; left; reflexivity).
           rewrite (Hrn p (or_intror HpS)) in E2. injection E2 as <-.
           replace (p =? -1) with false by (symmetry; apply Z.eqb_neq; lia).
           destruct (Hmov p HpS) as (_ & _ & M3).
           assert (Hj0 : j0 = -1 \/ In j0 S) by (destruct Hc as [|j1 j2 L2 Hj1 Hn1 Hc1]; [left; reflexivity | right; apply HLS; right; left; reflexivity]).
           cbn [map]. econstructor.
           ++ destruct (HinS p HpS) as (jj & Hjj). rewrite (Hrk jj p Hjj). lia.
           ++ rewrite M3. unfold next_of. rewrite Hn. rewrite (Hrn j0 Hj0). reflexivity.
           ++ apply IH; [intros s Hs; apply HLS; right; exact Hs | apply Hrn; exact Hj0].
      * split; [apply (map_rank_NoDup (rank_of ni) S L Hinj HLS H3)|].
        intros t. split.
        -- intros Ht'. apply in_map_iff in Ht' as (p & <- & Hp).
           assert (HpS : In p S) by (apply HLS; exact Hp). destruct (HinS p HpS) as (j & Hj).
           rewrite (Hrk j p Hj). split.
           ++ apply in_map. apply in_seq. assert ((j < length S)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). lia.
           ++ rewrite (HKS j p Hj). apply H4 in Hp. tauto.
        -- intros (Ht' & ku & Hku & Eb). apply in_map_iff in Ht' as (j & <- & Hj). apply in_seq in Hj.
           destruct (nth_error S j) as [p|] eqn:Ep; [|apply nth_error_None in Ep; lia].
           rewrite (HKS j p Ep) in Hku. apply in_map_iff. exists p. split; [apply Hrk; exact Ep|].
           apply H4. split; [apply nth_error_In with j; exact Ep | exists ku; auto].
  - intros j p Hj.
    assert (Hjlt : (j < length S)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    split.
    { rewrite fill_null_lo by lia. rewrite <- (Hrk j p Hj).
      destruct (Hmov p ltac:(apply nth_error_In with j; exact Hj)) as (M1 & _). exact M1. }
    rewrite fill_null_lo by lia. rewrite <- (Hrk j p Hj).
    destruct (Hmov p ltac:(apply nth_error_In with j; exact Hj)) as (_ & M2 & _). exact M2.
  - intros q Hq. destruct (Z_lt_le_dec q u) as [Hqu|Hqu].
    + apply fill_null_mid; lia.
    + rewrite fill_null_hi by lia.
      destruct (Hkeep q) as (K1 & _ & _).
      { intros p Hp E. destruct (HinS p Hp) as (j & Hj). rewrite (Hrk j p Hj) in E.
        assert ((j < length S)%nat) by (apply nth_error_Some; rewrite Hj; discriminate). lia. }
      rewrite K1. apply Hnull. lia.
Qed.

End Compaction.

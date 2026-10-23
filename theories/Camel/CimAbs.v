(** * CaseInsensitiveMap (fix): the chains of the hash table, as lists.

    [chain cn i L]: following [chainNext] from slot [i] visits exactly the slots [L]
    and ends with -1.  This file proves what the walks of findIndex and remove
    compute on a chain, and how the stores of put and remove change the chains. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Semantics Machine.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimRemove.
Import ListNotations.
Open Scope Z_scope.

Inductive chain (cn : list value) : Z -> list Z -> Prop :=
| chain_nil : chain cn (-1) []
| chain_cons : forall i j L, 0 <= i -> nth_z cn i = Some (VInt j) -> chain cn j L -> chain cn i (i :: L).

Lemma chain_head : forall cn i L, chain cn i L -> (i = -1 /\ L = []) \/ (exists L', L = i :: L' /\ 0 <= i).
Proof. intros cn i L H. destruct H; [left; auto | right; eauto]. Qed.

Lemma chain_bounds : forall cn i L, chain cn i L -> forall s, In s L -> 0 <= s < Z.of_nat (length cn).
Proof.
  intros cn i L H. induction H as [|i j L Hi Hn Hc IH]; intros s Hs; [destruct Hs|].
  destruct Hs as [<-|Hs]; [|auto]. pose proof (nth_z_bounds cn i (VInt j) Hn). lia.
Qed.

Lemma nth_set_other : forall {A} (l : list A) i j v, i <> j -> nth_z (set_nth_z l i v) j = nth_z l j.
Proof.
  induction l as [|x r IH]; intros i j v Hij; cbn; [reflexivity|].
  destruct (Z.eqb_spec i 0); cbn.
  - replace (j =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
  - destruct (j =? 0); [reflexivity|]. apply IH. lia.
Qed.

Lemma nth_set_same : forall {A} (l : list A) i v, 0 <= i < Z.of_nat (length l) -> nth_z (set_nth_z l i v) i = Some v.
Proof.
  induction l as [|x r IH]; intros i v Hi; cbn in *; [lia|].
  destruct (Z.eqb_spec i 0); cbn.
  - subst. reflexivity.
  - replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; assumption). apply IH. lia.
Qed.

Lemma set_nth_len : forall {A} (l : list A) i v, length (set_nth_z l i v) = length l.
Proof. induction l as [|x r IH]; intros i v; cbn; [reflexivity|]. destruct (i =? 0); cbn; [reflexivity|]. now rewrite IH. Qed.

Lemma chain_set_out : forall cn i L x v, chain cn i L -> ~ In x L -> chain (set_nth_z cn x v) i L.
Proof.
  intros cn i L x v H. induction H as [|i j L Hi Hn Hc IH]; intros Hx; [constructor|].
  econstructor; [exact Hi | | apply IH; intro; apply Hx; right; assumption].
  rewrite nth_set_other; [exact Hn|]. intro E; apply Hx; left; symmetry; exact E.
Qed.

(** Pushing slot [u] on the front of a chain. *)
Lemma chain_push : forall cn i L u, chain cn i L -> 0 <= u < Z.of_nat (length cn) -> ~ In u L ->
  chain (set_nth_z cn u (VInt i)) u (u :: L).
Proof.
  intros cn i L u H Hu Hn. econstructor; [lia | apply nth_set_same; exact Hu | apply chain_set_out; assumption].
Qed.

Section Walks.
Variable e : jenv.

(** The key at slot [s]. *)
Definition key_at (h : heap) (ks : list value) (s : Z) : option (list Z) :=
  match nth_z ks s with Some (VRef kl) => match h kl with Some (OStr u) => Some u | _ => None end | _ => None end.

Definition eqic (a b : list Z) : bool := equals_ignore_case (j_u e) a b.

(** Every slot of the chain holds a key. *)
Definition keyed (h : heap) (ks : list value) (L : list Z) : Prop := forall s, In s L -> exists u, key_at h ks s = Some u.

(** findIndex on a chain: the first slot whose key equalsIgnoreCase [q], or -1. *)
Fixpoint first_match (h : heap) (ks : list value) (q : list Z) (L : list Z) : Z :=
  match L with
  | [] => -1
  | s :: r => match key_at h ks s with Some u => if eqic u q then s else first_match h ks q r | None => -1 end
  end.

Lemma fi_walk_chain : forall h ks cn q i L f, chain cn i L -> keyed h ks L -> (length L < f)%nat ->
  fi_walk e h ks cn q i f = Some (first_match h ks q L).
Proof.
  intros h ks cn q i L f H. revert f. induction H as [|i j L Hi Hn Hc IH]; intros f Hk Hf.
  - destruct f; [lia|]. reflexivity.
  - destruct f as [|f]; [cbn in Hf; lia|]. cbn [fi_walk first_match].
    replace (i =? -1) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Hk i (or_introl eq_refl)) as (u & Hu). unfold key_at in Hu. unfold key_at at 1, eqic.
    destruct (nth_z ks i) as [[z|z|z|z| |kl|]|]; try discriminate.
    destruct (h kl) as [[| | u' | | |]|]; try discriminate. injection Hu as ->.
    rewrite ?Hn.
    destruct (equals_ignore_case (j_u e) u q) eqn:E.
    + reflexivity.
    + apply IH; [intros s Hs; apply Hk; right; exact Hs | cbn in Hf; lia].
Qed.

(** remove's walk on a chain: the slot found and its predecessor. *)
Fixpoint rm_match (h : heap) (ks : list value) (q : list Z) (prev : Z) (L : list Z) : option (Z * Z) :=
  match L with
  | [] => None
  | s :: r => match key_at h ks s with Some u => if eqic u q then Some (prev, s) else rm_match h ks q s r | None => None end
  end.

Lemma rm_walk_chain : forall h ks cn q i L f prev, chain cn i L -> keyed h ks L -> (length L < f)%nat ->
  rm_walk e h ks cn q prev i f = Some (rm_match h ks q prev L).
Proof.
  intros h ks cn q i L f prev H. revert f prev. induction H as [|i j L Hi Hn Hc IH]; intros f prev Hk Hf.
  - destruct f; [lia|]. reflexivity.
  - destruct f as [|f]; [cbn in Hf; lia|]. cbn [rm_walk rm_match].
    replace (i =? -1) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Hk i (or_introl eq_refl)) as (u & Hu). unfold key_at in Hu. unfold key_at at 1, eqic.
    destruct (nth_z ks i) as [[z|z|z|z| |kl|]|]; try discriminate.
    destruct (h kl) as [[| | u' | | |]|]; try discriminate. injection Hu as ->.
    rewrite Hn.
    destruct (equals_ignore_case (j_u e) u q) eqn:E; [reflexivity|].
    apply IH; [intros s Hs; apply Hk; right; exact Hs | cbn in Hf; lia].
Qed.

End Walks.

Lemma nodup_len_bound : forall (L : list Z) n, NoDup L -> (forall s, In s L -> 0 <= s < Z.of_nat n) -> (length L <= n)%nat.
Proof.
  intros L n Hnd Hb.
  rewrite <- (seq_length n 0), <- (map_length Z.of_nat (seq 0 n)).
  apply NoDup_incl_length; [exact Hnd|].
  intros s Hs. apply in_map_iff. exists (Z.to_nat s). split; [specialize (Hb s Hs); lia|].
  apply in_seq. specialize (Hb s Hs). lia.
Qed.

(** ** The table invariant *)
Section Table.
Variable e : jenv.

Definition bucket (q : list Z) (pw : Z) : Z := cih_spec e q mod 2 ^ pw.

(** [S] are the slots in use; every bucket's chain visits exactly the slots of [S] whose
    key falls in the bucket. *)
Definition tbl_ok (h : heap) (ks cn tbl : list value) (pw : Z) (S : list Z) : Prop :=
  keyed h ks S /\
  forall b, 0 <= b < 2 ^ pw -> exists i L, nth_z tbl b = Some (VInt i) /\ chain cn i L /\ NoDup L /\
    (forall s, In s L <-> In s S /\ exists ku, key_at h ks s = Some ku /\ bucket ku pw = b).

(** Assumptions on the case-insensitive equality for the keys in play. *)
Variable good : list Z -> Prop.
Hypothesis eq_sym : forall a b, good a -> good b -> eqic e a b = eqic e b a.
Hypothesis eq_trans : forall a b c, good a -> good b -> good c -> eqic e a b = true -> eqic e b c = true -> eqic e a c = true.
Hypothesis eq_hash : forall a b, good a -> good b -> eqic e a b = true -> cih_spec e a = cih_spec e b.

(** The keys in use are good and pairwise not equal ignoring case. *)
Definition keys_ok (h : heap) (ks : list value) (S : list Z) : Prop :=
  (forall s, In s S -> exists u, key_at h ks s = Some u /\ good u) /\
  (forall s1 s2 u1 u2, In s1 S -> In s2 S -> key_at h ks s1 = Some u1 -> key_at h ks s2 = Some u2 ->
     eqic e u1 u2 = true -> s1 = s2).

(** The slot that holds the key equal (ignoring case) to [q], if any. *)
Definition holds (h : heap) (ks : list value) (S : list Z) (q : list Z) (s : Z) : Prop :=
  In s S /\ exists u, key_at h ks s = Some u /\ eqic e u q = true.

Lemma first_match_spec : forall h ks S q L,
  keys_ok h ks S -> good q -> (forall s, In s L -> In s S) -> keyed h ks L ->
  (first_match e h ks q L = -1 /\ forall s, In s L -> ~ holds h ks S q s) \/
  (holds h ks S q (first_match e h ks q L) /\ In (first_match e h ks q L) L).
Proof.
  intros h ks S q L Hk Hq. induction L as [|s L IH]; intros Hsub Hkeyed.
  - left. split; [reflexivity | intros s []].
  - cbn [first_match]. destruct (Hkeyed s (or_introl eq_refl)) as (u & Hu). rewrite Hu.
    destruct (eqic e u q) eqn:E.
    + right. split; [split; [apply Hsub; left; reflexivity | exists u; auto] | left; reflexivity].
    + destruct IH as [(H1 & H2) | (H1 & H2)].
      * intros x Hx; apply Hsub; right; exact Hx.
      * intros x Hx; apply Hkeyed; right; exact Hx.
      * left. split; [exact H1|]. intros x [<-|Hx]; [|apply H2; exact Hx].
        intros (_ & u' & Hu' & E'). rewrite Hu in Hu'. injection Hu' as <-. congruence.
      * right. split; [exact H1 | right; exact H2].
Qed.

(** findIndex finds the slot holding the key, or -1 if no slot holds it. *)
Theorem find_correct : forall h ks cn tbl pw S q,
  tbl_ok h ks cn tbl pw S -> keys_ok h ks S -> good q -> 0 <= pw ->
  exists i L, nth_z tbl (bucket q pw) = Some (VInt i) /\ chain cn i L /\ (length L <= length cn)%nat /\
    ((first_match e h ks q L = -1 /\ forall s, ~ holds h ks S q s) \/
     holds h ks S q (first_match e h ks q L)).
Proof.
  intros h ks cn tbl pw S q (Hkd & Ht) Hk Hq Hpw.
  assert (Hb : 0 <= bucket q pw < 2 ^ pw) by (unfold bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (Ht _ Hb) as (i & L & Hi & Hc & Hnd & Hmem).
  exists i, L. split; [exact Hi|]. split; [exact Hc|]. split.
  { apply nodup_len_bound; [exact Hnd | apply (chain_bounds cn i L Hc)]. }
  assert (Hsub : forall s, In s L -> In s S) by (intros s Hs; apply Hmem in Hs; tauto).
  destruct (first_match_spec h ks S q L Hk Hq Hsub (fun s Hs => Hkd s (Hsub s Hs))) as [(H1 & H2) | (H1 & H2)].
  - left. split; [exact H1|]. intros s Hs. apply (H2 s); [|exact Hs].
    destruct Hs as (HS & u & Hu & E). apply Hmem. split; [exact HS|]. exists u. split; [exact Hu|].
    destruct Hk as (Hg & _). destruct (Hg s HS) as (u' & Hu' & Hgu). rewrite Hu in Hu'. injection Hu' as <-.
    unfold bucket. rewrite (eq_hash u q Hgu Hq E). reflexivity.
  - right. exact H1.
Qed.


Lemma key_at_set_other : forall h ks s x v, s <> x -> key_at h (set_nth_z ks x v) s = key_at h ks s.
Proof. intros. unfold key_at. rewrite nth_set_other by congruence. reflexivity. Qed.

Lemma key_at_set_same : forall h ks x k ku, 0 <= x < Z.of_nat (length ks) -> h k = Some (OStr ku) ->
  key_at h (set_nth_z ks x (VRef k)) x = Some ku.
Proof. intros. unfold key_at. rewrite nth_set_same by assumption. rewrite H0. reflexivity. Qed.

(** put of a new key: slot [u] gets the key and goes to the front of its bucket's chain. *)
Theorem insert_ok : forall h ks cn tbl pw S u k ku i0,
  tbl_ok h ks cn tbl pw S -> ~ In u S -> 0 <= u < Z.of_nat (length ks) -> u < Z.of_nat (length cn) ->
  h k = Some (OStr ku) -> Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw ->
  nth_z tbl (bucket ku pw) = Some (VInt i0) ->
  tbl_ok h (set_nth_z ks u (VRef k)) (set_nth_z cn u (VInt i0)) (set_nth_z tbl (bucket ku pw) (VInt u)) pw (S ++ [u]).
Proof.
  intros h ks cn tbl pw S u k ku i0 (Hkd & Ht) Hu Huk Huc Hk Hlen Hpw Hb.
  set (b := bucket ku pw) in *.
  assert (Hbb : 0 <= b < 2 ^ pw) by (unfold b, bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  split.
  - intros s Hs. apply in_app_or in Hs as [Hs|[<-|[]]].
    + destruct (Hkd s Hs) as (us & Hus). exists us. rewrite key_at_set_other; [exact Hus|].
      intro E; subst; contradiction.
    + exists ku. apply key_at_set_same; assumption.
  - intros b' Hb'. destruct (Ht b' Hb') as (i & L & Hi & Hc & Hnd & Hmem).
    assert (HuL : ~ In u L) by (intro H; apply Hmem in H; tauto).
    destruct (Z.eq_dec b' b) as [->|Hne].
    + rewrite Hb in Hi. injection Hi as <-.
      exists u, (u :: L). split; [apply nth_set_same; lia|]. split; [apply chain_push; [exact Hc | lia | exact HuL]|].
      split; [constructor; assumption|].
      intros s. split.
      * intros [<-|Hs]. { split; [apply in_or_app; right; left; reflexivity | exists ku; split; [apply key_at_set_same; assumption | reflexivity]]. }
        apply Hmem in Hs as (HS & us & Hus & Eb). split; [apply in_or_app; left; exact HS|].
        exists us. split; [|exact Eb]. rewrite key_at_set_other; [exact Hus|]. intro E; subst; contradiction.
      * intros (HS & us & Hus & Eb). apply in_app_or in HS as [HS|[<-|[]]]; [|left; reflexivity].
        right. apply Hmem. split; [exact HS|]. exists us. split; [|exact Eb].
        rewrite key_at_set_other in Hus; [exact Hus|]. intro E; subst; contradiction.
    + exists i, L. split; [rewrite nth_set_other by congruence; exact Hi|].
      split; [apply chain_set_out; assumption|]. split; [exact Hnd|].
      intros s. split.
      * intros Hs. assert (Hsu : s <> u) by (intro E; subst; contradiction).
        apply Hmem in Hs as (HS & us & Hus & Eb). split; [apply in_or_app; left; exact HS|].
        exists us. rewrite key_at_set_other by exact Hsu. auto.
      * intros (HS & us & Hus & Eb). apply in_app_or in HS as [HS|[<-|[]]].
        -- assert (Hsu : s <> u) by (intro E; subst; contradiction).
           apply Hmem. split; [exact HS|]. exists us. rewrite key_at_set_other in Hus by exact Hsu. auto.
        -- rewrite (key_at_set_same _ _ _ _ ku) in Hus by assumption. injection Hus as <-. fold b in Eb. congruence.
Qed.

Theorem insert_keys_ok : forall h ks S u k ku,
  keys_ok h ks S -> ~ In u S -> 0 <= u < Z.of_nat (length ks) -> h k = Some (OStr ku) -> good ku ->
  (forall s, ~ holds h ks S ku s) ->
  keys_ok h (set_nth_z ks u (VRef k)) (S ++ [u]).
Proof.
  intros h ks S u k ku (Hg & Hd) Hu Huk Hk Hgk Habs. split.
  - intros s Hs. apply in_app_or in Hs as [Hs|[<-|[]]].
    + rewrite key_at_set_other by (intro E; subst; contradiction). apply Hg. exact Hs.
    + exists ku. rewrite (key_at_set_same _ _ _ _ ku) by assumption. auto.
  - intros s1 s2 u1 u2 H1 H2 K1 K2 E.
    apply in_app_or in H1 as [H1|[<-|[]]]; apply in_app_or in H2 as [H2|[<-|[]]].
    + rewrite key_at_set_other in K1 by (intro E'; subst; contradiction).
      rewrite key_at_set_other in K2 by (intro E'; subst; contradiction). eapply Hd; eauto.
    + exfalso. rewrite key_at_set_other in K1 by (intro E'; subst; contradiction).
      rewrite (key_at_set_same _ _ _ _ ku) in K2 by assumption. injection K2 as <-.
      apply (Habs s1). split; [exact H1 | exists u1; auto].
    + exfalso. rewrite (key_at_set_same _ _ _ _ ku) in K1 by assumption. injection K1 as <-.
      rewrite key_at_set_other in K2 by (intro E'; subst; contradiction).
      destruct (Hg s2 H2) as (u2' & K2' & G2). rewrite K2 in K2'. injection K2' as <-.
      apply (Habs s2). split; [exact H2 | exists u2; split; [exact K2|]]. rewrite eq_sym by assumption. exact E.
    + reflexivity.
Qed.


(** ** remove *)
Lemma rm_match_shape : forall h ks q L prev p c, rm_match e h ks q prev L = Some (p, c) ->
  (exists L', L = c :: L' /\ p = prev) \/ (exists A L', L = app A (p :: c :: L')).
Proof.
  intros h ks q L. induction L as [|s L IH]; intros prev p c H; cbn in H; [discriminate|].
  destruct (key_at h ks s) as [u|]; [|discriminate].
  destruct (eqic e u q).
  - injection H as <- <-. left. eauto.
  - destruct (IH s p c H) as [(L' & -> & ->) | (A & L' & ->)].
    + right. exists [], L'. reflexivity.
    + right. exists (s :: A), L'. reflexivity.
Qed.

Lemma rm_match_found : forall h ks q L prev p c, rm_match e h ks q prev L = Some (p, c) ->
  In c L /\ exists u, key_at h ks c = Some u /\ eqic e u q = true.
Proof.
  intros h ks q L. induction L as [|s L IH]; intros prev p c H; cbn in H; [discriminate|].
  destruct (key_at h ks s) as [u|] eqn:Ek; [|discriminate].
  destruct (eqic e u q) eqn:E.
  - injection H as <- <-. split; [left; reflexivity | eauto].
  - destruct (IH s p c H) as (H1 & H2). split; [right; exact H1 | exact H2].
Qed.

Lemma chain_inv : forall cn i L, chain cn i L -> 0 <= i -> exists j L', L = i :: L' /\ nth_z cn i = Some (VInt j) /\ chain cn j L'.
Proof. intros cn i L H Hi. inversion H; subst; [lia | eauto]. Qed.

Lemma chain_unlink_mid : forall cn A p c L' i j,
  chain cn i (app A (p :: c :: L')) -> NoDup (app A (p :: c :: L')) -> nth_z cn c = Some (VInt j) ->
  chain (set_nth_z cn p (VInt j)) i (app A (p :: L')).
Proof.
  induction A as [|a A IH]; intros p c L' i j H Hnd Hc; cbn in *.
  - inversion H as [|i0 j0 L0 Hi Hn Hch]; subst.
    inversion Hch as [|i1 j1 L1 Hi1 Hn1 Hch1]; subst.
    rewrite Hc in Hn1. injection Hn1 as <-.
    inversion Hnd as [|x l Hx Hnd']; subst. inversion Hnd' as [|y l' Hy Hnd'']; subst.
    econstructor; [exact Hi | apply nth_set_same; pose proof (nth_z_bounds _ _ _ Hn); lia |].
    apply chain_set_out; [exact Hch1 | intro Hin; apply Hx; right; exact Hin].
  - inversion H as [|i0 j0 L0 Hi Hn Hch]; subst.
    inversion Hnd as [|x l Hx Hnd']; subst.
    econstructor; [exact Hi | | eapply IH; [exact Hch | exact Hnd' | exact Hc]].
    rewrite nth_set_other; [exact Hn|]. intro E; subst. apply Hx. apply in_or_app. right. left. reflexivity.
Qed.

Lemma NoDup_app_remove_mid : forall (A : list Z) x L, NoDup (app A (x :: L)) -> NoDup (app A L) /\ ~ In x (app A L).
Proof.
  intros A x L H. split.
  - eapply NoDup_remove_1. exact H.
  - eapply NoDup_remove_2. exact H.
Qed.


Lemma in_rm_iff : forall (S : list Z) c s, In s (remove Z.eq_dec c S) <-> In s S /\ s <> c.
Proof. intros. split; [intro H; split; [eapply in_remove; exact H | intro E; subst; eapply remove_In; exact H] | intros (H1 & H2); apply in_in_remove; assumption]. Qed.

(** remove of a present key: the slot is unlinked from its chain and cleared. *)
Theorem remove_ok : forall h ks cn tbl pw S q i p c j,
  tbl_ok h ks cn tbl pw S -> keys_ok h ks S -> good q -> 0 <= pw -> (length cn <= length ks)%nat ->
  nth_z tbl (bucket q pw) = Some (VInt i) ->
  rm_walk e h ks cn q (-1) i (Datatypes.S (length ks)) = Some (Some (p, c)) ->
  nth_z cn c = Some (VInt j) ->
  holds h ks S q c /\
  tbl_ok h (set_nth_z ks c VNull)
    (if p =? -1 then cn else set_nth_z cn p (VInt j))
    (if p =? -1 then set_nth_z tbl (bucket q pw) (VInt j) else tbl) pw (remove Z.eq_dec c S) /\
  keys_ok h (set_nth_z ks c VNull) (remove Z.eq_dec c S).
Proof.
  intros h ks cn tbl pw S q i p c j (Hkd & Ht) Hk Hq Hpw Hlc Hi Hw Hj.
  set (b := bucket q pw) in *.
  assert (Hbb : 0 <= b < 2 ^ pw) by (unfold b, bucket; apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia).
  destruct (Ht b Hbb) as (i' & L & Hi' & Hc & Hnd & Hmem). rewrite Hi in Hi'. injection Hi' as <-.
  assert (Hsub : forall s, In s L -> In s S) by (intros s Hs; apply Hmem in Hs; tauto).
  assert (HkL : keyed h ks L) by (intros s Hs; apply Hkd, Hsub, Hs).
  assert (HlenL : (length L < Datatypes.S (length ks))%nat).
  { pose proof (nodup_len_bound L (length cn) Hnd (chain_bounds cn i L Hc)). lia. }
  rewrite (rm_walk_chain e h ks cn q i L (Datatypes.S (length ks)) (-1) Hc HkL HlenL) in Hw. injection Hw as Hw.
  destruct (rm_match_found h ks q L (-1) p c Hw) as (HcL & uc & Huc & Euc).
  assert (HcS : In c S) by (apply Hsub; exact HcL).
  assert (Hcb : bucket uc pw = b).
  { apply Hmem in HcL as (_ & u' & Hu' & Eb). rewrite Huc in Hu'. injection Hu' as <-. exact Eb. }
  assert (Hkey : forall s, s <> c -> key_at h (set_nth_z ks c VNull) s = key_at h ks s)
    by (intros s Hs; apply key_at_set_other; exact Hs).
  assert (Hnokey : forall s, In s L -> s <> c -> In s (remove Z.eq_dec c S)).
  { intros s Hs Hsc. apply in_rm_iff. split; [apply Hsub; exact Hs | exact Hsc]. }
  (* membership of the other buckets does not involve c *)
  assert (Hother : forall b', 0 <= b' < 2 ^ pw -> b' <> b -> forall i2 L2, nth_z tbl b' = Some (VInt i2) -> chain cn i2 L2 ->
             (forall s, In s L2 <-> In s S /\ exists ku, key_at h ks s = Some ku /\ bucket ku pw = b') ->
             ~ In c L2 /\ (forall s, In s L2 <-> In s (remove Z.eq_dec c S) /\ exists ku, key_at h (set_nth_z ks c VNull) s = Some ku /\ bucket ku pw = b')).
  { intros b' Hb' Hne i2 L2 Hi2 Hc2 Hm2.
    assert (HcL2 : ~ In c L2).
    { intro H. apply Hm2 in H as (_ & u' & Hu' & Eb). rewrite Huc in Hu'. injection Hu' as <-. congruence. }
    split; [exact HcL2|]. intros s. split.
    - intros Hs. assert (Hsc : s <> c) by (intro E; subst; contradiction).
      apply Hm2 in Hs as (HS & ku & Hku & Eb). split; [apply in_rm_iff; auto|]. rewrite Hkey by exact Hsc. eauto.
    - intros (HS & ku & Hku & Eb). apply in_rm_iff in HS as (HS & Hsc). rewrite Hkey in Hku by exact Hsc.
      apply Hm2. eauto. }
  split; [split; [exact HcS | exists uc; auto]|].
  split.
  - split.
    + intros s Hs. apply in_rm_iff in Hs as (Hs & Hsc). rewrite Hkey by exact Hsc. apply Hkd. exact Hs.
    + intros b' Hb'.
      destruct (rm_match_shape h ks q L (-1) p c Hw) as [(L' & HL & ->) | (A & L' & HL)].
      * (* c was the head of the chain *)
        cbn [Z.eqb Pos.eqb]. subst L.
        assert (Hic : i = c) by (inversion Hc; reflexivity). subst i.
        destruct (Z.eq_dec b' b) as [->|Hne].
        -- exists j, L'. split; [apply nth_set_same; pose proof (nth_z_bounds _ _ _ Hi); lia|].
           destruct (chain_inv cn c (c :: L') Hc ltac:(inversion Hc; lia)) as (j' & L'' & HE & Hn & Hc').
           injection HE as <-. rewrite Hj in Hn. injection Hn as <-.
           split; [exact Hc'|]. inversion Hnd as [|x l Hx Hnd']; subst. split; [exact Hnd'|].
           intros s. split.
           ++ intros Hs. assert (Hsc : s <> c) by (intro E; subst; contradiction).
              assert (Hs' : In s (c :: L')) by (right; exact Hs). apply Hmem in Hs' as (HS & ku & Hku & Eb).
              split; [apply in_rm_iff; auto|]. rewrite Hkey by exact Hsc. eauto.
           ++ intros (HS & ku & Hku & Eb). apply in_rm_iff in HS as (HS & Hsc). rewrite Hkey in Hku by exact Hsc.
              assert (Hs' : In s (c :: L')) by (apply Hmem; eauto). destruct Hs' as [E|Hs']; [congruence | exact Hs'].
        -- destruct (Ht b' Hb') as (i2 & L2 & Hi2 & Hc2 & Hnd2 & Hm2).
           exists i2, L2. split; [cbn [Pos.eqb]; rewrite nth_set_other by congruence; exact Hi2|].
           split; [exact Hc2|]. split; [exact Hnd2|].
           apply (Hother b' Hb' Hne i2 L2 Hi2 Hc2 Hm2).
      * (* c follows p *)
        assert (Hp : 0 <= p) by (pose proof (chain_bounds cn i L Hc p ltac:(rewrite HL; apply in_or_app; right; left; reflexivity)); lia).
        replace (p =? -1) with false by (symmetry; apply Z.eqb_neq; lia).
        assert (HpL : In p L) by (rewrite HL; apply in_or_app; right; left; reflexivity).
        destruct (Z.eq_dec b' b) as [->|Hne].
        -- exists i, (app A (p :: L')). split; [exact Hi|].
           split; [apply (chain_unlink_mid cn A p c L' i j); [rewrite <- HL; exact Hc | rewrite <- HL; exact Hnd | exact Hj]|].
           assert (Hnd3 : NoDup (app (app A [p]) (c :: L'))) by (rewrite <- app_assoc; cbn; rewrite <- HL; exact Hnd).
           destruct (NoDup_app_remove_mid (app A [p]) c L' Hnd3) as (Hnd4 & Hcn).
           rewrite <- app_assoc in Hnd4, Hcn. cbn in Hnd4, Hcn.
           split; [exact Hnd4|].
           intros s. split.
           ++ intros Hs. assert (Hsc : s <> c) by (intro E; subst; contradiction).
              assert (Hs' : In s L) by (rewrite HL; apply in_app_or in Hs as [Hs|[<-|Hs]]; apply in_or_app;
                                        [left; exact Hs | right; left; reflexivity | right; right; right; exact Hs]).
              apply Hmem in Hs' as (HS & ku & Hku & Eb).
              split; [apply in_rm_iff; auto|]. rewrite Hkey by exact Hsc. eauto.
           ++ intros (HS & ku & Hku & Eb). apply in_rm_iff in HS as (HS & Hsc). rewrite Hkey in Hku by exact Hsc.
              assert (Hs' : In s L) by (apply Hmem; eauto). rewrite HL in Hs'.
              apply in_app_or in Hs' as [Hs'|[<-|[E|Hs']]]; apply in_or_app;
                [left; exact Hs' | right; left; reflexivity | congruence | right; right; exact Hs'].
        -- destruct (Ht b' Hb') as (i2 & L2 & Hi2 & Hc2 & Hnd2 & Hm2).
           exists i2, L2. split; [exact Hi2|].
           assert (HpL2 : ~ In p L2).
           { intro H. apply Hm2 in H as (_ & u2 & Hu2 & Eb2). apply Hmem in HpL as (_ & u3 & Hu3 & Eb3).
             rewrite Hu2 in Hu3. injection Hu3 as <-. congruence. }
           split; [apply chain_set_out; assumption|]. split; [exact Hnd2|].
           apply (Hother b' Hb' Hne i2 L2 Hi2 Hc2 Hm2).
  - destruct Hk as (Hg & Hd). split.
    + intros s Hs. apply in_rm_iff in Hs as (Hs & Hsc). rewrite Hkey by exact Hsc. apply Hg. exact Hs.
    + intros s1 s2 u1 u2 H1 H2 K1 K2 E. apply in_rm_iff in H1 as (H1 & H1c). apply in_rm_iff in H2 as (H2 & H2c).
      rewrite Hkey in K1 by exact H1c. rewrite Hkey in K2 by exact H2c. eapply Hd; eauto.
Qed.

End Table.

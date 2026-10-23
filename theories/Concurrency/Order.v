(* ===================================================================== *)
(*  JVM.Concurrency.Order                                                *)
(*                                                                       *)
(*  Finite-order utilities for the memory-model development:            *)
(*    - topological sorting of a decidable acyclic relation on [0,n)     *)
(*      (every finite acyclic relation has a linear extension);          *)
(*    - filters over [seq 0 n] (prefixes, appending a maximum,           *)
(*      sortedness);                                                     *)
(*    - least elements of decidable predicates on nat.                   *)
(*                                                                       *)
(*  Plain stdlib; no axioms.                                             *)
(* ===================================================================== *)

From Stdlib Require Import List Arith Bool Lia Relations ListDec.
Open Scope bool_scope.
Import ListNotations.

(** * Acyclicity *)

Definition acyclic (R : nat -> nat -> Prop) : Prop :=
  forall i, ~ clos_trans nat R i i.

Lemma clos_trans_mono (R S : nat -> nat -> Prop) :
  (forall i j, R i j -> S i j) ->
  forall i j, clos_trans nat R i j -> clos_trans nat S i j.
Proof.
  intros H i j Hc. induction Hc.
  - apply t_step. auto.
  - eapply t_trans; eauto.
Qed.

(** A relation contained in a strict order given by a ranking function. *)
Lemma clos_trans_rank (R : nat -> nat -> Prop) (f : nat -> nat) :
  (forall i j, R i j -> f i < f j) ->
  forall i j, clos_trans nat R i j -> f i < f j.
Proof.
  intros H i j Hc. induction Hc; [auto | lia].
Qed.

(** * Chains and the minimal-element lemma *)

Section Topo.
  Variable R : nat -> nat -> Prop.
  Variable Rdec : forall i j, {R i j} + {~ R i j}.

  (* [chain [a0; a1; ...; ak]] : R a0 a1, R a1 a2, ... *)
  Fixpoint chain (p : list nat) : Prop :=
    match p with
    | [] => True
    | a :: t =>
        match t with
        | [] => True
        | b :: _ => R a b /\ chain t
        end
    end.

  Lemma chain_ct a t b : chain (a :: t) -> In b t -> clos_trans nat R a b.
  Proof.
    revert a. induction t as [|c t IH]; intros a Hc Hin; [destruct Hin|].
    destruct Hc as [Hac Hc]. destruct Hin as [<-|Hin].
    - apply t_step; exact Hac.
    - eapply t_trans; [apply t_step; exact Hac|]. apply IH; auto.
  Qed.

  Lemma chain_app_r l1 l2 : chain (l1 ++ l2) -> chain l2.
  Proof.
    induction l1 as [|a l1 IH]; simpl; auto.
    intros H. apply IH. destruct l1 as [|b l1]; simpl in *.
    - destruct l2; [exact I| tauto].
    - tauto.
  Qed.

  (* If every element of [l] has an R-predecessor in [l], there are
     arbitrarily long backward chains inside [l]. *)
  Lemma long_chains (l : list nat) :
    (forall x, In x l -> exists y, In y l /\ R y x) ->
    forall x0, In x0 l ->
    forall k, exists a t, length (a :: t) = S k /\ incl (a :: t) l /\ chain (a :: t).
  Proof.
    intros Hpred x0 Hx0 k. induction k as [|k IH].
    - exists x0, []. repeat split; simpl; auto.
      intros y [<-|[]]; exact Hx0.
    - destruct IH as (a & t & Hlen & Hincl & Hch).
      destruct (Hpred a (Hincl a (or_introl eq_refl))) as (y & Hy & Rya).
      exists y, (a :: t). repeat split.
      + simpl in *. lia.
      + intros z [<-|Hz]; [exact Hy | apply Hincl; exact Hz].
      + exact Rya.
      + exact Hch.
  Qed.

  Lemma acyclic_has_pred_false (l : list nat) :
    acyclic R ->
    (forall x, In x l -> exists y, In y l /\ R y x) ->
    l <> [] -> False.
  Proof.
    intros Hac Hpred Hne. destruct l as [|x0 l0]; [contradiction|].
    destruct (long_chains (x0 :: l0) Hpred x0 (or_introl eq_refl) (length (x0 :: l0)))
      as (a & t & Hlen & Hincl & Hch).
    assert (Hnd : ~ NoDup (a :: t)).
    { intros Hnd. pose proof (NoDup_incl_length Hnd Hincl). lia. }
    apply not_NoDup in Hnd.
    2:{ intros u v. destruct (Nat.eq_dec u v); [left|right]; auto. }
    destruct Hnd as (b & l1 & l2 & l3 & Heq).
    rewrite Heq in Hch. apply chain_app_r in Hch.
    apply (Hac b). eapply chain_ct; [exact Hch|].
    apply in_or_app. right. left. reflexivity.
  Qed.

  (* Decide whether [x] has a predecessor in [l]. *)
  Lemma pred_dec (l : list nat) (x : nat) :
    {forall y, In y l -> ~ R y x} + {exists y, In y l /\ R y x}.
  Proof.
    induction l as [|a l IH].
    - left. intros y [].
    - destruct (Rdec a x) as [Hax|Hax].
      + right. exists a. split; [left; reflexivity | exact Hax].
      + destruct IH as [IH|IH].
        * left. intros y [<-|Hy]; auto.
        * right. destruct IH as (y & Hy & Ryx). exists y. split; [right|]; auto.
  Qed.

  Lemma min_dec (l0 l : list nat) :
    {x | In x l0 /\ forall y, In y l -> ~ R y x} +
    {forall x, In x l0 -> exists y, In y l /\ R y x}.
  Proof.
    induction l0 as [|a l0 IH].
    - right. intros x [].
    - destruct (pred_dec l a) as [Ha|Ha].
      + left. exists a. split; [left; reflexivity | exact Ha].
      + destruct IH as [[x [Hx Hmin]]|IH].
        * left. exists x. split; [right; exact Hx | exact Hmin].
        * right. intros x [<-|Hx]; auto.
  Qed.

  Lemma acyclic_minimal (l : list nat) :
    acyclic R -> l <> [] ->
    {x | In x l /\ forall y, In y l -> ~ R y x}.
  Proof.
    intros Hac Hne. destruct (min_dec l l) as [H|H]; [exact H|].
    exfalso. exact (acyclic_has_pred_false l Hac H Hne).
  Qed.

  (** Linear extension of R on the elements of a list. *)
  Lemma topo_list (l : list nat) :
    acyclic R ->
    exists ord : nat -> nat,
      (forall i j, In i l -> In j l -> ord i = ord j -> i = j) /\
      (forall i j, In i l -> In j l -> R i j -> ord i < ord j).
  Proof.
    intros Hac.
    remember (length l) as k eqn:Hk. revert l Hk.
    induction k as [k IH] using lt_wf_ind. intros l Hk.
    destruct l as [|a l0].
    { exists (fun i => i). split; intros i j [] . }
    destruct (acyclic_minimal (a :: l0) Hac ltac:(discriminate)) as [x [Hx Hmin]].
    set (l' := remove Nat.eq_dec x (a :: l0)).
    assert (Hlt : length l' < k).
    { subst k. apply remove_length_lt. exact Hx. }
    destruct (IH (length l') Hlt l' eq_refl) as (ord' & Hinj & Hresp).
    exists (fun i => if Nat.eq_dec i x then 0 else S (ord' i)).
    split.
    - intros i j Hi Hj.
      destruct (Nat.eq_dec i x) as [->|Hix]; destruct (Nat.eq_dec j x) as [->|Hjx];
        try reflexivity; try discriminate.
      intros Heq. injection Heq as Heq.
      apply Hinj; auto; apply in_in_remove; auto.
    - intros i j Hi Hj Rij.
      destruct (Nat.eq_dec j x) as [->|Hjx].
      { exfalso. exact (Hmin i Hi Rij). }
      destruct (Nat.eq_dec i x) as [->|Hix]; [lia|].
      apply -> Nat.succ_lt_mono. apply Hresp; auto; apply in_in_remove; auto.
  Qed.

End Topo.

(** Every decidable acyclic relation on [0,n) has a linear extension
    given by an injective ranking function. *)
Theorem toposort (n : nat) (R : nat -> nat -> Prop)
  (Rdec : forall i j, {R i j} + {~ R i j})
  (Rbound : forall i j, R i j -> i < n /\ j < n)
  (Racyc : acyclic R) :
  exists ord : nat -> nat,
    (forall i j, i < n -> j < n -> ord i = ord j -> i = j) /\
    (forall i j, R i j -> ord i < ord j).
Proof.
  destruct (topo_list R Rdec (seq 0 n) Racyc) as (ord & Hinj & Hresp).
  exists ord. split.
  - intros i j Hi Hj. apply Hinj; apply in_seq; lia.
  - intros i j Rij. destruct (Rbound i j Rij).
    apply Hresp; auto; apply in_seq; lia.
Qed.

(** * Least elements *)

Lemma bounded_dec (P : nat -> Prop) (Pdec : forall k, {P k} + {~ P k}) j :
  {exists k, k < j /\ P k} + {forall k, k < j -> ~ P k}.
Proof.
  induction j as [|j IH].
  - right. intros k Hk. lia.
  - destruct IH as [IH|IH].
    + left. destruct IH as (k & Hk & Pk). exists k. split; [lia|exact Pk].
    + destruct (Pdec j) as [Pj|Pj].
      * left. exists j. split; [lia|exact Pj].
      * right. intros k Hk. destruct (Nat.eq_dec k j) as [->|Hkj]; [exact Pj|].
        apply IH. lia.
Qed.

Lemma least_nat (P : nat -> Prop) (Pdec : forall k, {P k} + {~ P k}) j :
  P j -> exists f, f <= j /\ P f /\ forall k, k < f -> ~ P k.
Proof.
  induction j as [j IH] using lt_wf_ind. intros Pj.
  destruct (bounded_dec P Pdec j) as [(k & Hk & Pk)|Hnone].
  - destruct (IH k Hk Pk) as (f & Hf & Pf & Hmin).
    exists f. repeat split; [lia|exact Pf|exact Hmin].
  - exists j. repeat split; [lia|exact Pj|exact Hnone].
Qed.

(** * Filters over [seq] *)

Section Filters.

  Lemma filter_nil {A} (f : A -> bool) (l : list A) :
    (forall x, In x l -> f x = false) -> filter f l = [].
  Proof.
    induction l as [|a l IH]; intros H; simpl; auto.
    rewrite (H a (or_introl eq_refl)). apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  (** If [f] selects a subset of [g] that is downward closed (among the
      elements selected by [g]), then [filter f] is a prefix of
      [filter g]. *)
  Lemma filter_seq_prefix (f g : nat -> bool) len a :
    (forall x, f x = true -> g x = true) ->
    (forall i j, i < j -> g i = true -> f j = true -> f i = true) ->
    exists suf, filter g (seq a len) = filter f (seq a len) ++ suf.
  Proof.
    intros Hfg Hdown. revert a. induction len as [|len IH]; intros a.
    - exists []. reflexivity.
    - simpl. destruct (f a) eqn:Fa.
      + rewrite (Hfg a Fa). destruct (IH (S a)) as [suf Hsuf].
        exists suf. rewrite Hsuf. reflexivity.
      + destruct (g a) eqn:Ga.
        * (* no later element is selected by f *)
          assert (Hnil : filter f (seq (S a) len) = []).
          { apply filter_nil. intros x Hx.
            apply in_seq in Hx. destruct (f x) eqn:Fx; [|reflexivity].
            rewrite (Hdown a x ltac:(lia) Ga Fx) in Fa. discriminate. }
          rewrite Hnil. exists (a :: filter g (seq (S a) len)). reflexivity.
        * exact (IH (S a)).
  Qed.

  Lemma filter_nil_seq (f : nat -> bool) len a :
    (forall x, a <= x < a + len -> f x = false) -> filter f (seq a len) = [].
  Proof.
    intros H. apply filter_nil. intros x Hx. apply in_seq in Hx. apply H. lia.
  Qed.

  (** Adding a new maximum [r] to the selected set appends [r]. *)
  Lemma filter_seq_snoc (f f' : nat -> bool) n r :
    r < n ->
    (forall x, f x = true -> x < r) ->
    (forall x, f' x = f x || Nat.eqb x r) ->
    filter f' (seq 0 n) = filter f (seq 0 n) ++ [r].
  Proof.
    intros Hr Hlt Hf'.
    replace n with (S r + (n - S r)) by lia.
    rewrite !seq_app, !filter_app, seq_S, !filter_app.
    assert (H1 : filter f (seq (0 + S r) (n - S r)) = []).
    { apply filter_nil_seq. intros x Hx. destruct (f x) eqn:Fx; [|reflexivity].
      apply Hlt in Fx. lia. }
    assert (H2 : filter f' (seq (0 + S r) (n - S r)) = []).
    { apply filter_nil_seq. intros x Hx. rewrite Hf'. destruct (f x) eqn:Fx.
      - apply Hlt in Fx. lia.
      - simpl. apply Nat.eqb_neq. lia. }
    rewrite H1, H2.
    simpl. rewrite Hf'.
    destruct (f r) eqn:Fr; [apply Hlt in Fr; lia|]. rewrite Nat.eqb_refl. simpl.
    rewrite !app_nil_r. f_equal.
    apply filter_ext_in. intros x Hx. apply in_seq in Hx.
    rewrite Hf'. replace (Nat.eqb x r) with false by (symmetry; apply Nat.eqb_neq; lia).
    apply orb_false_r.
  Qed.

  (** Elements of a filtered [seq] appear in increasing order. *)
  Lemma filter_seq_sorted (f : nat -> bool) len a pre i post :
    filter f (seq a len) = pre ++ i :: post ->
    forall j, In j pre -> j < i.
  Proof.
    revert a pre. induction len as [|len IH]; intros a pre Heq j Hj.
    - destruct pre; discriminate.
    - simpl in Heq. destruct (f a) eqn:Fa.
      + destruct pre as [|b pre].
        * destruct Hj.
        * simpl in Heq. injection Heq as Hab Heq. subst b.
          destruct Hj as [<-|Hj].
          -- assert (Hi : In i (filter f (seq (S a) len))).
             { rewrite Heq. apply in_or_app. right. left. reflexivity. }
             apply filter_In in Hi as [Hi _]. apply in_seq in Hi. lia.
          -- eapply IH; eauto.
      + eapply IH; eauto.
  Qed.

End Filters.

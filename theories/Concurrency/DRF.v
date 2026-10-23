(* ===================================================================== *)
(*  JVM.Concurrency.DRF                                                  *)
(*                                                                       *)
(*  Data-race-freedom theorems for the happens-before model.             *)
(*                                                                       *)
(*  (a) [drf_execution_sc]: a well-formed, hb-consistent execution that  *)
(*      has no data race is sequentially consistent (Aspinall-Sevcik     *)
(*      Lemma 2; the core of every JMM DRF proof).  The SC order is the  *)
(*      presentation order of the execution.                             *)
(*                                                                       *)
(*  (b) [drf_sc_no_thin_air]: program-level DRF-SC for the model         *)
(*      "hb-consistency + acyclic(po U so U rf)": if a program is        *)
(*      correctly synchronized (all its SC executions are race-free),    *)
(*      every well-formed, hb-consistent execution of it whose           *)
(*      po U so U rf is acyclic is sequentially consistent (and          *)
(*      race-free).  This model is strictly stronger than the JMM        *)
(*      (it forbids load buffering), so (b) does not by itself give      *)
(*      DRF-SC for the JLS 17.4.8 model.  Examples.v shows that without  *)
(*      the acyclicity condition the statement is false.                 *)
(* ===================================================================== *)

From Stdlib Require Import List Arith Bool Lia Relations.
From JVM.Concurrency Require Import Events Order Executions.
Import ListNotations.
Open Scope bool_scope.

Section DRF.
  Context {L V M C X : Type}.
  Variable vol : L -> bool.
  Variable init : L -> V.
  Variable M_eq_dec : forall m m' : M, {m = m'} + {m <> m'}.

  Abbreviation execution := (execution L V M C X).
  Abbreviation wf := (wf vol init M_eq_dec).
  Abbreviation sees_last := (sees_last init).
  Abbreviation sc_order := (sc_order init).
  Abbreviation sequentially_consistent := (sequentially_consistent init).

  (* ------------------------------------------------------------------- *)
  (** * Theorem (a): per-execution DRF lemma *)

  Lemma not_not_and (A B : Prop) : ~ ~ A -> ~ ~ B -> ~ (A /\ B) -> False.
  Proof. tauto. Qed.

  Section A.
    Variable E : execution.
    Hypothesis Hwf : wf E.
    Hypothesis Hhb : hb_consistent E.
    Hypothesis Hrf : race_free E.

    (* Two distinct plain accesses to [l], one of them a write, are
       ordered by hb (in the negated form usable constructively). *)
    Lemma ordered_access i j l vi vj :
      D E i -> D E j -> i <> j ->
      act E i = AWrite l vi ->
      (act E j = AWrite l vj \/ act E j = ARead l vj) ->
      ~ hb E i j -> ~ hb E j i -> False.
    Proof.
      intros Di Dj Hij Ai Aj Hn1 Hn2. apply (Hrf i j).
      repeat split; auto.
      - exists l. rewrite Ai. destruct Aj as [Aj|Aj]; rewrite Aj; auto.
      - left. rewrite Ai. reflexivity.
    Qed.

    Lemma reads_see_last_in_presentation r : D E r -> sees_last E (fun i => i) r.
    Proof.
      intros Dr l v Hread.
      pose proof (wf_ws _ _ _ _ Hwf r l v Dr Hread) as Hws.
      pose proof (Hhb r l v Dr Hread) as Hc.
      destruct (read_of_cases _ _ _ Hread) as [Ar|Ar].
      - (* plain read *)
        assert (Hvol : vol l = false).
        { pose proof (wf_vol _ _ _ _ Hwf r Dr) as H. rewrite Ar in H. exact H. }
        destruct (ex_ws E r) as [w|] eqn:Hw.
        + destruct Hws as [Dw Ww]. destruct Hc as [Hnrw Hnbetween].
          assert (Hwl : write_loc (act E w) = Some l) by (eapply write_of_loc; eauto).
          destruct (plain_write _ _ _ _ Hwf w l Dw Hwl Hvol) as [vw Aw].
          assert (Hwr : w <> r) by (intros ->; congruence).
          assert (Hlt : w < r).
          { destruct (lt_dec w r) as [H|H]; [exact H|]. exfalso.
            apply (ordered_access w r l vw v Dw Dr Hwr Aw (or_intror Ar)); auto.
            intros Hb. apply (hb_lt _ _ _ _ Hwf) in Hb. lia. }
          repeat split; auto.
          intros w' Dw' Hw'l Hw'r.
          destruct (le_lt_dec w' w) as [H|H]; [exact H|]. exfalso.
          destruct (plain_write _ _ _ _ Hwf w' l Dw' Hw'l Hvol) as [vw' Aw'].
          apply (not_not_and (hb E w w') (hb E w' r)); [| |apply Hnbetween; auto].
          * intros Hn. apply (ordered_access w w' l vw vw' Dw Dw' ltac:(lia) Aw (or_introl Aw') Hn).
            intros Hb. apply (hb_lt _ _ _ _ Hwf) in Hb. lia.
          * intros Hn. apply (ordered_access w' r l vw' v Dw' Dr ltac:(lia) Aw' (or_intror Ar) Hn).
            intros Hb. apply (hb_lt _ _ _ _ Hwf) in Hb. lia.
        + split; [exact Hws|].
          intros w' Dw' Hw'l Hw'r.
          destruct (plain_write _ _ _ _ Hwf w' l Dw' Hw'l Hvol) as [vw' Aw'].
          apply (ordered_access w' r l vw' v Dw' Dr ltac:(lia) Aw' (or_intror Ar)).
          * apply Hc. exact Hw'l.
          * intros Hb. apply (hb_lt _ _ _ _ Hwf) in Hb. lia.
      - (* volatile read: synchronization-order consistency *)
        pose proof (wf_so_vol _ _ _ _ Hwf r l v Dr Ar) as Hso.
        destruct (ex_ws E r) as [w|] eqn:Hw.
        + destruct Hws as [Dw Ww]. destruct Hso as [Hlt Hnb].
          repeat split; auto.
          intros w' Dw' Hw'l Hw'r.
          destruct (le_lt_dec w' w) as [H|H]; [exact H|].
          exfalso. apply (Hnb w'); auto.
        + split; [exact Hws|]. exact Hso.
    Qed.

    (** Theorem (a), with the presentation order as the witness. *)
    Theorem drf_execution_sc_order : sc_order E (fun i => i).
    Proof.
      constructor.
      - auto.
      - intros i j H. apply H.
      - intros i j H. apply H.
      - apply reads_see_last_in_presentation.
    Qed.
  End A.

  (** Theorem (a): a well-formed, hb-consistent, race-free execution is
      sequentially consistent. *)
  Theorem drf_execution_sc (E : execution) :
    wf E -> hb_consistent E -> race_free E -> sequentially_consistent E.
  Proof.
    intros Hwf Hhb Hrf. exists (fun i => i). apply drf_execution_sc_order; auto.
  Qed.

  (* ------------------------------------------------------------------- *)
  (** * Sub-executions

      [sub E' E]: E' is obtained from E by keeping a set of events that
      is closed under po- and so-predecessors, and possibly changing the
      values of some plain reads (and what they see). *)

  Record sub (E' E : execution) : Prop := {
    sub_n : ex_n E' = ex_n E;
    sub_dom : forall i, D E' i -> D E i;
    sub_tid : forall i, D E' i -> tid_of E' i = tid_of E i;
    sub_act : forall i, D E' i -> act E' i = act E i \/
      exists l v v', act E i = ARead l v /\ act E' i = ARead l v';
    sub_po_closed : forall i j, D E' j -> D E i -> i < j ->
      tid_of E i = tid_of E j -> D E' i;
    sub_so_closed : forall i j, D E' j -> D E i -> i < j -> sync E i -> sync E j -> D E' i;
    sub_ws_vol : forall r l v, D E' r -> act E' r = AVRead l v -> ex_ws E' r = ex_ws E r
  }.

  Section Sub.
    Variables E' E : execution.
    Hypothesis Hs : sub E' E.

    Lemma sub_D i : D E' i -> D E i.
    Proof. apply (sub_dom _ _ Hs). Qed.

    Lemma sub_act_from i a : D E' i -> act E i = a -> (forall l v, a <> ARead l v) ->
      act E' i = a.
    Proof.
      intros Di Ai Ha. destruct (sub_act _ _ Hs i Di) as [H|(l & v & v' & H1 & H2)].
      - congruence.
      - exfalso. apply (Ha l v). congruence.
    Qed.

    Lemma sub_act_to i a : D E' i -> act E' i = a -> (forall l v, a <> ARead l v) ->
      act E i = a.
    Proof.
      intros Di Ai Ha. destruct (sub_act _ _ Hs i Di) as [H|(l & v & v' & H1 & H2)].
      - congruence.
      - exfalso. apply (Ha l v'). congruence.
    Qed.

    Lemma sub_sync i : D E' i -> sync E' i -> sync E i /\ act E' i = act E i.
    Proof.
      unfold sync. intros Di Hsy. destruct (sub_act _ _ Hs i Di) as [H|(l & v & v' & H1 & H2)].
      - rewrite <- H. auto.
      - rewrite H2 in Hsy. discriminate.
    Qed.

    Lemma sub_sync' i : D E' i -> sync E i -> sync E' i.
    Proof.
      unfold sync. intros Di Hsy. destruct (sub_act _ _ Hs i Di) as [H|(l & v & v' & H1 & H2)].
      - rewrite H. auto.
      - rewrite H1 in Hsy. discriminate.
    Qed.

    Lemma sub_write_loc w l : D E' w -> write_loc (act E' w) = Some l ->
      write_loc (act E w) = Some l /\ act E' w = act E w.
    Proof.
      intros Dw Hw. destruct (sub_act _ _ Hs w Dw) as [H|(l' & v & v' & H1 & H2)].
      - rewrite <- H. auto.
      - rewrite H2 in Hw. discriminate.
    Qed.

    Lemma sub_po i j : po E' i j -> po E i j.
    Proof.
      intros (Di & Dj & Hij & Ht). repeat split; auto using sub_D.
      rewrite <- (sub_tid _ _ Hs i Di), <- (sub_tid _ _ Hs j Dj). exact Ht.
    Qed.

    Lemma sub_so i j : so E' i j -> so E i j.
    Proof.
      intros (Di & Dj & Hij & Si & Sj).
      repeat split; auto using sub_D; [apply (sub_sync i)|apply (sub_sync j)]; auto.
    Qed.

    Lemma sub_sw i j : sw E' i j -> sw E i j.
    Proof.
      intros (Di & Dj & H). split; [apply (sub_dom _ _ Hs); auto|].
      split; [apply (sub_dom _ _ Hs); auto|].
      rewrite <- (sub_tid _ _ Hs i Di), <- (sub_tid _ _ Hs j Dj).
      destruct (sub_act _ _ Hs i Di) as [Ai|(l & v & v' & _ & Ai)].
      2:{ rewrite Ai in H. simpl in H. contradiction. }
      destruct (sub_act _ _ Hs j Dj) as [Aj|(l & v & v' & _ & Aj)].
      2:{ rewrite Aj in H. destruct (act E' i); simpl in H; contradiction. }
      rewrite <- Ai, <- Aj. exact H.
    Qed.

    Lemma sub_hb i j : hb E' i j -> hb E i j.
    Proof.
      apply clos_trans_mono. intros a b [H|H]; [left; apply sub_po | right; apply sub_sw]; auto.
    Qed.

    (* counting synchronization actions below a synchronization action *)
    Lemma sub_count (q : action L V M C X -> bool) i t :
      (forall a, q a = true -> is_sync a = true) ->
      (forall l v, q (ARead l v) = false) ->
      D E' i -> sync E i ->
      count_before E' (fun j => Nat.eqb (tid_of E' j) t && q (act E' j)) i =
      count_before E (fun j => Nat.eqb (tid_of E j) t && q (act E j)) i.
    Proof.
      intros Hq Hqr Di Si. unfold count_before. f_equal.
      apply filter_ext_in. intros j Hj. apply in_seq in Hj.
      destruct (ex_dom E' j) eqn:Dj'.
      - assert (Dj : D E j) by (apply (sub_dom _ _ Hs); exact Dj').
        unfold D in Dj. rewrite Dj. simpl.
        rewrite (sub_tid _ _ Hs j Dj').
        destruct (sub_act _ _ Hs j Dj') as [Aj|(l & v & v' & A1 & A2)].
        + rewrite Aj. reflexivity.
        + rewrite A1, A2, !Hqr. reflexivity.
      - simpl. destruct (ex_dom E j) eqn:Dj; [|reflexivity]. simpl.
        destruct (Nat.eqb (tid_of E j) t && q (act E j)) eqn:Hqj; [|reflexivity].
        exfalso. apply andb_true_iff in Hqj as [_ Hqj].
        assert (D E' j) as Hc.
        { apply (sub_so_closed _ _ Hs j i); auto; [lia|]. unfold sync. auto. }
        unfold D in Hc. congruence.
    Qed.

    Lemma wf_sub :
      wf E ->
      (forall r l v, D E' r -> read_of (act E' r) = Some (l, v) ->
        match ex_ws E' r with
        | Some w => D E' w /\ write_of (act E' w) = Some (l, v)
        | None => v = init l
        end) ->
      (forall i, D E' i -> read_of (act E' i) = None -> ex_ws E' i = None) ->
      wf E'.
    Proof.
      intros Hwf Hws Hwsn. constructor; auto.
      - intros i Di. rewrite (sub_n _ _ Hs). apply (wf_bound _ _ _ _ Hwf). apply (sub_dom _ _ Hs); auto.
      - intros i Di. pose proof (wf_vol _ _ _ _ Hwf i (sub_dom _ _ Hs i Di)) as H.
        destruct (sub_act _ _ Hs i Di) as [Ai|(l & v & v' & A1 & A2)].
        + rewrite Ai. exact H.
        + rewrite A2. rewrite A1 in H. exact H.
      - intros r l v Dr Ar.
        assert (Ar' : act E r = AVRead l v) by (apply (sub_act_to r); auto; discriminate).
        rewrite (sub_ws_vol _ _ Hs r l v Dr Ar).
        pose proof (wf_so_vol _ _ _ _ Hwf r l v (sub_dom _ _ Hs r Dr) Ar') as H.
        destruct (ex_ws E r) as [w|].
        + destruct H as [H1 H2]. split; auto.
          intros w' Dw' Hw'. apply H2; [apply (sub_dom _ _ Hs); auto|].
          apply (sub_write_loc w'); auto.
        + intros w' Dw' Hw'. apply H; [apply (sub_dom _ _ Hs); auto|].
          apply (sub_write_loc w'); auto.
      - intros i m t Di Ai Ht.
        assert (Ai' : act E i = ALock m) by (apply (sub_act_to i); auto; discriminate).
        assert (Si : sync E i) by (unfold sync; rewrite Ai'; reflexivity).
        unfold locks_before, unlocks_before.
        rewrite !(sub_count _ i t); auto.
        + apply (wf_mutex _ _ _ _ Hwf i m t (sub_dom _ _ Hs i Di) Ai').
          rewrite <- (sub_tid _ _ Hs i Di). exact Ht.
        + apply is_unlock_of_sync.
        + apply is_lock_of_sync.
      - intros i m Di Ai.
        assert (Ai' : act E i = AUnlock m) by (apply (sub_act_to i); auto; discriminate).
        assert (Si : sync E i) by (unfold sync; rewrite Ai'; reflexivity).
        unfold locks_before, unlocks_before.
        rewrite !(sub_count _ i (tid_of E' i)); auto.
        + rewrite (sub_tid _ _ Hs i Di).
          apply (wf_unlock _ _ _ _ Hwf i m (sub_dom _ _ Hs i Di) Ai').
        + apply is_lock_of_sync.
        + apply is_unlock_of_sync.
      - intros i Di Hfirst.
        apply (sub_act_from i); auto; [|discriminate].
        apply (wf_start_first _ _ _ _ Hwf i (sub_dom _ _ Hs i Di)).
        intros j Dj Hji Ht.
        assert (Dj' : D E' j) by (apply (sub_po_closed _ _ Hs j i); auto).
        apply (Hfirst j Dj' Hji).
        rewrite (sub_tid _ _ Hs j Dj'), (sub_tid _ _ Hs i Di). exact Ht.
      - intros i j Di Dj Aj Ht.
        apply (wf_start_only_first _ _ _ _ Hwf i j); auto using sub_D.
        + apply (sub_act_to j); auto. discriminate.
        + rewrite <- (sub_tid _ _ Hs i Di), <- (sub_tid _ _ Hs j Dj). exact Ht.
      - intros i j Di Dj Ai Ht.
        apply (wf_finish_last _ _ _ _ Hwf i j); auto using sub_D.
        + apply (sub_act_to i); auto. discriminate.
        + rewrite <- (sub_tid _ _ Hs i Di), <- (sub_tid _ _ Hs j Dj). exact Ht.
      - intros i j t c Di Dj Ai Ht.
        apply (wf_spawn_before _ _ _ _ Hwf i j t c); auto using sub_D.
        + apply (sub_act_to i); auto. discriminate.
        + rewrite <- (sub_tid _ _ Hs j Dj). exact Ht.
      - intros j t Dj Aj.
        assert (Aj' : act E j = AJoin t) by (apply (sub_act_to j); auto; discriminate).
        destruct (wf_join_after _ _ _ _ Hwf j t (sub_dom _ _ Hs j Dj) Aj')
          as (i & Di & Hij & Hti & Ai).
        assert (Di' : D E' i).
        { apply (sub_so_closed _ _ Hs i j); auto; unfold sync; [rewrite Ai|rewrite Aj']; reflexivity. }
        exists i. repeat split; auto.
        + rewrite (sub_tid _ _ Hs i Di'). exact Hti.
        + apply (sub_act_from i); auto. discriminate.
    Qed.

    Lemma thread_ids_sub t : exists suf, thread_ids E t = thread_ids E' t ++ suf.
    Proof.
      unfold thread_ids. rewrite (sub_n _ _ Hs). apply filter_seq_prefix.
      - intros x Hx. apply andb_true_iff in Hx as [Dx Hx].
        rewrite (sub_tid _ _ Hs x Dx) in Hx. apply (sub_dom _ _ Hs) in Dx.
        unfold D in Dx. rewrite Dx, Hx. reflexivity.
      - intros i j Hij Hi Hj.
        apply andb_true_iff in Hi as [Di Hi]. apply andb_true_iff in Hj as [Dj Hj].
        rewrite (sub_tid _ _ Hs j Dj) in Hj.
        apply Nat.eqb_eq in Hi, Hj.
        assert (Di' : D E' i) by (apply (sub_po_closed _ _ Hs i j); auto; congruence).
        unfold D in Di'. rewrite Di'. simpl. rewrite (sub_tid _ _ Hs i Di').
        apply Nat.eqb_eq. exact Hi.
    Qed.

    Lemma thread_init_sub (P : program L V M C X) t s0 :
      wf E -> thread_init P E t s0 -> (exists j, D E' j /\ tid_of E' j = t) ->
      thread_init P E' t s0.
    Proof.
      intros Hwf [Hmain|(Hne & i & c & Di & Ai & Hinit)] (j & Dj & Hj); [left; exact Hmain|].
      right. split; [exact Hne|].
      assert (Pdec : forall k, {D E k /\ tid_of E k = t} + {~ (D E k /\ tid_of E k = t)}).
      { intros k. unfold D. destruct (ex_dom E k); [|right; intros [H _]; discriminate].
        destruct (Nat.eq_dec (tid_of E k) t); [left|right]; tauto. }
      rewrite (sub_tid _ _ Hs j Dj) in Hj.
      destruct (least_nat _ Pdec j (conj (sub_dom _ _ Hs j Dj) Hj)) as (f & Hfj & [Df Hf] & Hmin).
      assert (Df' : D E' f).
      { destruct (Nat.eq_dec f j) as [->|Hne']; [exact Dj|].
        apply (sub_po_closed _ _ Hs f j); auto; [lia|congruence]. }
      assert (Af : act E f = AStart).
      { apply (wf_start_first _ _ _ _ Hwf f Df). intros k Dk Hk Ht.
        apply (Hmin k Hk). split; congruence. }
      assert (Hif : i < f) by (apply (wf_spawn_before _ _ _ _ Hwf i f t c); auto).
      assert (Di' : D E' i).
      { apply (sub_so_closed _ _ Hs i f); auto; unfold sync; [rewrite Ai|rewrite Af]; reflexivity. }
      exists i, c. repeat split; auto.
      apply (sub_act_from i); auto. discriminate.
    Qed.

    (** Restriction preserves "reads see the last write" for a read
        whose earlier events are all kept. *)
    Lemma sees_last_sub (ord : nat -> nat) r :
      D E' r -> act E' r = act E r -> ex_ws E' r = ex_ws E r ->
      (forall w, D E w -> ord w < ord r -> D E' w /\ act E' w = act E w) ->
      sees_last E ord r -> sees_last E' ord r.
    Proof.
      intros Dr Ar Wr Hclosed H l v Hread. rewrite Ar in Hread.
      specialize (H l v Hread). rewrite Wr.
      destruct (ex_ws E r) as [w|].
      - destruct H as (Dw & Ww & Hwr & Hmax).
        destruct (Hclosed w Dw Hwr) as [Dw1 Aw].
        repeat split; auto.
        + rewrite Aw. exact Ww.
        + intros w' Dw' Hw' Hlt. destruct (sub_write_loc w' l Dw' Hw') as [Hw'' _].
          apply Hmax; auto. apply (sub_dom _ _ Hs); auto.
      - destruct H as [Hv Hnone]. split; auto.
        intros w' Dw' Hw'. destruct (sub_write_loc w' l Dw' Hw') as [Hw'' _].
        apply Hnone; auto. apply (sub_dom _ _ Hs); auto.
    Qed.
  End Sub.

  (* ------------------------------------------------------------------- *)
  (** * Theorem (b) *)

  Lemma and_dec (A B : Prop) : {A} + {~ A} -> {B} + {~ B} -> {A /\ B} + {~ (A /\ B)}.
  Proof. intros [a|a] [b|b]; [left|right|right|right]; tauto. Qed.

  Lemma or_dec (A B : Prop) : {A} + {~ A} -> {B} + {~ B} -> {A \/ B} + {~ (A \/ B)}.
  Proof. intros [a|a] [b|b]; [left|left|left|right]; tauto. Qed.

  Lemma D_dec (E : execution) i : {D E i} + {~ D E i}.
  Proof. unfold D. destruct (ex_dom E i); [left|right]; congruence. Qed.

  Lemma sync_dec (E : execution) i : {sync E i} + {~ sync E i}.
  Proof. unfold sync. destruct (is_sync (act E i)); [left|right]; congruence. Qed.

  Lemma po_dec (E : execution) i j : {po E i j} + {~ po E i j}.
  Proof.
    unfold po. repeat apply and_dec; auto using D_dec, lt_dec, Nat.eq_dec.
  Qed.

  Lemma so_dec (E : execution) i j : {so E i j} + {~ so E i j}.
  Proof.
    unfold so. repeat apply and_dec; auto using D_dec, lt_dec, sync_dec.
  Qed.

  Lemma rf_dec (E : execution) i j : {rf E i j} + {~ rf E i j}.
  Proof.
    unfold rf. apply and_dec; [apply D_dec|].
    destruct (ex_ws E j) as [w|]; [|right; discriminate].
    destruct (Nat.eq_dec w i) as [->|H]; [left; reflexivity|right; congruence].
  Qed.

  Section B.
    Variable L_eq_dec : forall l l' : L, {l = l'} + {l <> l'}.
    Variable P : program L V M C X.
    Hypothesis Hrec : receptive (p_lts P).
    Hypothesis Hcs : correctly_synchronized vol init M_eq_dec P.
    Variable E : execution.
    Hypothesis Hwf : wf E.
    Hypothesis Hex : exec_of P E.
    Hypothesis Hhb : hb_consistent E.
    (* a linear extension of po U so U rf *)
    Variable T : nat -> nat.
    Hypothesis Tinj : forall i j, i < ex_n E -> j < ex_n E -> T i = T j -> i = j.
    Hypothesis Tpo : forall i j, po E i j -> T i < T j.
    Hypothesis Tso : forall i j, so E i j -> T i < T j.
    Hypothesis Trf : forall w r, rf E w r -> T w < T r.

    Lemma T_hb i j : hb E i j -> T i < T j.
    Proof.
      apply clos_trans_rank. intros a b [H|H]; [apply Tpo; exact H|].
      apply Tso. apply (sw_so _ _ _ _ Hwf). exact H.
    Qed.

    Lemma T_inj_D i j : D E i -> D E j -> T i = T j -> i = j.
    Proof. intros Di Dj. apply Tinj; apply (wf_bound _ _ _ _ Hwf); auto. Qed.

    Lemma rf_T r w : D E r -> ex_ws E r = Some w -> T w < T r.
    Proof. intros Dr Hw. apply Trf. split; auto. Qed.

    (** ** The latest write before a point of T *)

    Definition wloc_is (l : L) (a : action L V M C X) : bool :=
      match write_loc a with
      | Some l' => if L_eq_dec l l' then true else false
      | None => false
      end.

    Lemma wloc_is_iff l a : wloc_is l a = true <-> write_loc a = Some l.
    Proof.
      unfold wloc_is. destruct (write_loc a) as [l'|]; [|split; discriminate].
      destruct (L_eq_dec l l') as [->|Hne]; split; congruence.
    Qed.

    Fixpoint latest_in (l : L) (k : nat) (cs : list nat) : option nat :=
      match cs with
      | [] => None
      | i :: cs' =>
          let b := latest_in l k cs' in
          if ex_dom E i && wloc_is l (act E i) && Nat.ltb (T i) k then
            match b with
            | Some j => if Nat.ltb (T j) (T i) then Some i else Some j
            | None => Some i
            end
          else b
      end.

    Lemma latest_in_spec l k cs :
      match latest_in l k cs with
      | Some w => In w cs /\ D E w /\ write_loc (act E w) = Some l /\ T w < k /\
          forall w', In w' cs -> D E w' -> write_loc (act E w') = Some l -> T w' < k ->
            T w' <= T w
      | None => forall w', In w' cs -> D E w' -> write_loc (act E w') = Some l -> ~ T w' < k
      end.
    Proof.
      induction cs as [|i cs IH]; simpl.
      - intros w' [].
      - destruct (ex_dom E i && wloc_is l (act E i) && Nat.ltb (T i) k) eqn:Hi.
        + apply andb_true_iff in Hi as [Hi Hk]. apply andb_true_iff in Hi as [Di Hl].
          apply wloc_is_iff in Hl. apply Nat.ltb_lt in Hk.
          revert IH. destruct (latest_in l k cs) as [j|]; intros IH.
          * destruct IH as (Hj & Dj & Hjl & Hjk & Hmax).
            destruct (Nat.ltb (T j) (T i)) eqn:Hji.
            -- apply Nat.ltb_lt in Hji. repeat split; auto.
               intros w' [<-|Hw'] Dw' Hw'l Hw'k; [lia|].
               specialize (Hmax w' Hw' Dw' Hw'l Hw'k). lia.
            -- apply Nat.ltb_ge in Hji. repeat split; auto.
               intros w' [<-|Hw'] Dw' Hw'l Hw'k; [lia|]. auto.
          * repeat split; auto.
            intros w' [<-|Hw'] Dw' Hw'l Hw'k; [lia|].
            exfalso. exact (IH w' Hw' Dw' Hw'l Hw'k).
        + assert (Hni : D E i -> write_loc (act E i) = Some l -> ~ T i < k).
          { intros Di Hl Hk. unfold D in Di. apply wloc_is_iff in Hl.
            apply Nat.ltb_lt in Hk. rewrite Di, Hl, Hk in Hi. discriminate. }
          revert IH. destruct (latest_in l k cs) as [j|]; intros IH.
          * destruct IH as (Hj & Dj & Hjl & Hjk & Hmax). repeat split; auto.
            intros w' [<-|Hw'] Dw' Hw'l Hw'k; [exfalso; apply (Hni Dw' Hw'l Hw'k)|auto].
          * intros w' [<-|Hw'] Dw' Hw'l; [apply Hni; auto|]. apply IH; auto.
    Qed.

    Lemma in_events i : D E i -> In i (seq 0 (ex_n E)).
    Proof. intros Di. apply in_seq. pose proof (wf_bound _ _ _ _ Hwf i Di). lia. Qed.

    (** ** Cutting E before r (in T) *)

    Definition cut (r : nat) : execution :=
      mkExec (ex_n E) (fun i => ex_dom E i && Nat.ltb (T i) (T r)) (ex_lab E) (ex_ws E).

    Lemma D_cut r i : D (cut r) i <-> D E i /\ T i < T r.
    Proof.
      unfold D, cut. simpl. rewrite andb_true_iff, Nat.ltb_lt. tauto.
    Qed.

    Lemma sub_cut r : sub (cut r) E.
    Proof.
      constructor.
      - reflexivity.
      - intros i Di. apply D_cut in Di. apply Di.
      - reflexivity.
      - intros i Dj. left. reflexivity.
      - intros i j Dj Di Hij Ht. apply D_cut in Dj as [Dj Hj]. apply D_cut.
        split; auto. assert (T i < T j) by (apply Tpo; repeat split; auto). lia.
      - intros i j Dj Di Hij Si Sj. apply D_cut in Dj as [Dj Hj]. apply D_cut.
        split; auto. assert (T i < T j) by (apply Tso; repeat split; auto). lia.
      - reflexivity.
    Qed.

    Lemma wf_cut r : wf (cut r).
    Proof.
      apply (wf_sub _ _ (sub_cut r) Hwf).
      - intros r' l v Dr' Hread. apply D_cut in Dr' as [Dr' Hr'].
        pose proof (wf_ws _ _ _ _ Hwf r' l v Dr' Hread) as H. simpl in *.
        destruct (ex_ws E r') as [w|] eqn:Hw; [|exact H].
        destruct H as [Dw Ww]. split; auto. apply D_cut. split; auto.
        pose proof (rf_T r' w Dr' Hw). lia.
      - intros i Di Hread. apply D_cut in Di as [Di _].
        apply (wf_ws_none _ _ _ _ Hwf i Di Hread).
    Qed.

    Lemma exec_cut r : exec_of P (cut r).
    Proof.
      intros t (j & Dj & Hj).
      assert (Dj0 : D E j) by (apply D_cut in Dj; apply Dj).
      destruct (Hex t (ex_intro _ j (conj Dj0 Hj))) as (s0 & s & Hinit & Hrun).
      exists s0. destruct (thread_ids_sub _ _ (sub_cut r) t) as [suf Hsuf].
      unfold proj in Hrun. rewrite Hsuf, map_app in Hrun.
      apply trun_app_inv in Hrun as (s1 & Hrun & _).
      exists s1. split.
      - apply (thread_init_sub _ _ (sub_cut r)); auto. exists j. auto.
      - exact Hrun.
    Qed.

    Lemma sc_cut r :
      (forall i, D E i -> T i < T r -> sees_last E T i) -> sc_order (cut r) T.
    Proof.
      intros IH. constructor.
      - intros i j Di Dj. apply D_cut in Di, Dj. apply T_inj_D; tauto.
      - intros i j H. apply Tpo, (sub_po _ _ (sub_cut r)), H.
      - intros i j H. apply Tso, (sub_so _ _ (sub_cut r)), H.
      - intros i Di. pose proof Di as Di'. apply D_cut in Di' as [Di0 Hi].
        apply (sees_last_sub _ _ (sub_cut r)); auto.
        + intros w Dw Hw. split; [apply D_cut; split; [auto|lia]|reflexivity].
    Qed.

    Lemma race_free_cut r :
      (forall i, D E i -> T i < T r -> sees_last E T i) -> race_free (cut r).
    Proof.
      intros IH. apply Hcs; [apply wf_cut|apply exec_cut|]. exists T. apply sc_cut; auto.
    Qed.

    (** ** Redirecting the read r to the latest write x *)

    Definition redirect (r : nat) (l : L) (v : V) (x : nat) : execution :=
      mkExec (ex_n E)
        (fun i => ex_dom E i && (Nat.ltb (T i) (T r) || Nat.eqb i r))
        (fun i => if Nat.eqb i r then mkEv (tid_of E r) (ARead l v) else ex_lab E i)
        (fun i => if Nat.eqb i r then Some x else ex_ws E i).

    Section Redirect.
      Variables (r : nat) (l : L) (v0 vx : V) (x : nat).
      Hypothesis Dr : D E r.
      Hypothesis Ar : act E r = ARead l v0.
      Hypothesis Dx : D E x.
      Hypothesis Txr : T x < T r.
      Hypothesis Ax : act E x = AWrite l vx.
      Hypothesis Xmax : forall w', D E w' -> write_loc (act E w') = Some l -> T w' < T r ->
        T w' <= T x.
      Hypothesis IH : forall i, D E i -> T i < T r -> sees_last E T i.

      Let R := redirect r l vx x.

      Lemma D_red i : D R i <-> D E i /\ (T i < T r \/ i = r).
      Proof.
        unfold D, R, redirect. simpl. rewrite andb_true_iff, orb_true_iff, Nat.ltb_lt, Nat.eqb_eq.
        tauto.
      Qed.

      Lemma act_red_r : act R r = ARead l vx.
      Proof. unfold act, R, redirect. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

      Lemma act_red_ne i : i <> r -> act R i = act E i.
      Proof.
        intros H. unfold act, R, redirect. simpl.
        apply Nat.eqb_neq in H. rewrite H. reflexivity.
      Qed.

      Lemma tid_red i : tid_of R i = tid_of E i.
      Proof.
        unfold tid_of, R, redirect. simpl.
        destruct (Nat.eqb_spec i r) as [->|H]; reflexivity.
      Qed.

      Lemma ws_red_r : ex_ws R r = Some x.
      Proof. unfold R, redirect. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

      Lemma ws_red_ne i : i <> r -> ex_ws R i = ex_ws E i.
      Proof.
        intros H. unfold R, redirect. simpl. apply Nat.eqb_neq in H. rewrite H. reflexivity.
      Qed.

      Lemma x_ne_r : x <> r.
      Proof. intros ->. lia. Qed.

      Lemma lt_ne i : T i < T r -> i <> r.
      Proof. intros H ->. lia. Qed.

      Lemma sub_red : sub R E.
      Proof.
        constructor.
        - reflexivity.
        - intros i Di. apply D_red in Di. apply Di.
        - intros i Di. apply tid_red.
        - intros i Di. destruct (Nat.eq_dec i r) as [->|H].
          + right. exists l, v0, vx. split; [exact Ar|apply act_red_r].
          + left. apply act_red_ne. exact H.
        - intros i j Dj Di Hij Ht. apply D_red in Dj as [Dj Hj]. apply D_red.
          split; auto. left. assert (T i < T j) by (apply Tpo; repeat split; auto).
          destruct Hj as [Hj| ->]; lia.
        - intros i j Dj Di Hij Si Sj. apply D_red in Dj as [Dj Hj]. apply D_red.
          split; auto. left. assert (T i < T j) by (apply Tso; repeat split; auto).
          destruct Hj as [Hj| ->]; lia.
        - intros r' l' v' Dr' Ar'. destruct (Nat.eq_dec r' r) as [->|H].
          + rewrite act_red_r in Ar'. discriminate.
          + apply ws_red_ne. exact H.
      Qed.

      Lemma wf_red : wf R.
      Proof.
        apply (wf_sub _ _ sub_red Hwf).
        - intros r' l' v' Dr' Hread. destruct (Nat.eq_dec r' r) as [->|Hne].
          + rewrite act_red_r in Hread. simpl in Hread. injection Hread as <- <-.
            rewrite ws_red_r. split.
            * apply D_red. split; auto.
            * rewrite (act_red_ne x x_ne_r), Ax. reflexivity.
          + rewrite (act_red_ne r' Hne) in Hread. rewrite (ws_red_ne r' Hne).
            apply D_red in Dr' as [Dr' Hr']. destruct Hr' as [Hr'|]; [|contradiction].
            pose proof (wf_ws _ _ _ _ Hwf r' l' v' Dr' Hread) as H.
            destruct (ex_ws E r') as [w|] eqn:Hw; [|exact H].
            destruct H as [Dw Ww]. pose proof (rf_T r' w Dr' Hw).
            split.
            * apply D_red. split; auto. left. lia.
            * rewrite act_red_ne; [exact Ww|]. apply lt_ne. lia.
        - intros i Di Hread. destruct (Nat.eq_dec i r) as [->|Hne].
          + rewrite act_red_r in Hread. discriminate.
          + rewrite (act_red_ne i Hne) in Hread. rewrite (ws_red_ne i Hne).
            apply (wf_ws_none _ _ _ _ Hwf i); auto. apply D_red in Di. apply Di.
      Qed.

      Lemma thread_ids_red_r :
        thread_ids R (tid_of E r) = thread_ids (cut r) (tid_of E r) ++ [r].
      Proof.
        unfold thread_ids. simpl. apply filter_seq_snoc.
        - apply (wf_bound _ _ _ _ Hwf). exact Dr.
        - intros i Hi. apply andb_true_iff in Hi as [Hi Ht].
          apply andb_true_iff in Hi as [Di Hi]. apply Nat.ltb_lt in Hi.
          apply Nat.eqb_eq in Ht. unfold tid_of in Ht. simpl in Ht. fold (tid_of E i) in Ht.
          destruct (lt_eq_lt_dec i r) as [[H|H]|H]; [exact H|subst; lia|].
          assert (T r < T i) by (apply Tpo; repeat split; auto). lia.
        - intros i. rewrite tid_red.
          destruct (Nat.eqb_spec i r) as [->|H].
          + unfold D in Dr. unfold tid_of, cut. simpl. rewrite Dr.
            rewrite ?Nat.eqb_refl, ?orb_true_r. reflexivity.
          + unfold tid_of. simpl.
            destruct (ex_dom E i), (Nat.ltb (T i) (T r)), (Nat.eqb (ev_tid (ex_lab E i)) _);
              reflexivity.
      Qed.

      Lemma exec_red : exec_of P R.
      Proof.
        intros t (j & Dj & Hj).
        assert (Dj0 : D E j) by (apply D_red in Dj; apply Dj).
        rewrite tid_red in Hj.
        destruct (Hex t (ex_intro _ j (conj Dj0 Hj))) as (s0 & s & Hinit & Hrun).
        exists s0.
        assert (Hinit' : thread_init P R t s0).
        { apply (thread_init_sub _ _ sub_red); auto. exists j. rewrite tid_red. auto. }
        destruct (thread_ids_sub _ _ sub_red t) as [suf Hsuf].
        destruct (Nat.eq_dec t (tid_of E r)) as [->|Hne].
        - rewrite thread_ids_red_r, <- app_assoc in Hsuf. simpl in Hsuf.
          unfold proj in Hrun. rewrite Hsuf, map_app in Hrun. simpl in Hrun.
          rewrite Ar in Hrun.
          replace (map (act E) (thread_ids (cut r) (tid_of E r)) ++ ARead l v0 :: map (act E) suf)
            with ((map (act E) (thread_ids (cut r) (tid_of E r)) ++ [ARead l v0]) ++ map (act E) suf)
            in Hrun by (rewrite <- app_assoc; reflexivity).
          apply trun_app_inv in Hrun as (s1 & Hrun & _).
          destruct (trun_snoc_read _ Hrec _ _ _ _ _ Hrun vx) as [s2 Hrun2].
          exists s2. split; [exact Hinit'|].
          unfold proj. rewrite thread_ids_red_r, map_app. simpl. rewrite act_red_r.
          replace (map (act R) (thread_ids (cut r) (tid_of E r)))
            with (map (act E) (thread_ids (cut r) (tid_of E r))); [exact Hrun2|].
          apply map_ext_in. intros i Hi.
          unfold thread_ids in Hi. apply filter_In in Hi as [_ Hi].
          apply andb_true_iff in Hi as [Hi _]. apply (D_cut r i) in Hi.
          symmetry. apply act_red_ne. apply lt_ne. apply Hi.
        - unfold proj in Hrun. rewrite Hsuf, map_app in Hrun.
          apply trun_app_inv in Hrun as (s1 & Hrun & _).
          exists s1. split; [exact Hinit'|].
          unfold proj.
          replace (map (act R) (thread_ids R t)) with (map (act E) (thread_ids R t)); [exact Hrun|].
          apply map_ext_in. intros i Hi.
          unfold thread_ids in Hi. apply filter_In in Hi as [_ Hi].
          apply andb_true_iff in Hi as [_ Hi]. apply Nat.eqb_eq in Hi.
          rewrite tid_red in Hi.
          symmetry. apply act_red_ne. intros ->. apply Hne. symmetry. exact Hi.
      Qed.

      Lemma sc_red : sc_order R T.
      Proof.
        constructor.
        - intros i j Di Dj. apply D_red in Di, Dj. apply T_inj_D; tauto.
        - intros i j H. apply Tpo, (sub_po _ _ sub_red), H.
        - intros i j H. apply Tso, (sub_so _ _ sub_red), H.
        - intros i Di. destruct (Nat.eq_dec i r) as [->|Hne].
          + intros l' v' Hread. rewrite act_red_r in Hread. simpl in Hread.
            injection Hread as <- <-. rewrite ws_red_r.
            repeat split; auto.
            * apply D_red. split; auto.
            * rewrite (act_red_ne x x_ne_r), Ax. reflexivity.
            * intros w' Dw' Hw' Hlt.
              assert (Hw'r : w' <> r) by (intros ->; rewrite act_red_r in Hw'; discriminate).
              rewrite (act_red_ne w' Hw'r) in Hw'.
              apply Xmax; auto. apply D_red in Dw'. apply Dw'.
          + pose proof Di as Di'. apply D_red in Di' as [Di0 [Hi| ->]]; [|contradiction].
            apply (sees_last_sub _ _ sub_red); auto.
            * apply act_red_ne. exact Hne.
            * apply ws_red_ne. exact Hne.
            * intros w Dw Hw. split.
              -- apply D_red. split; auto. left. lia.
              -- apply act_red_ne. apply lt_ne. lia.
      Qed.

      (** In the redirected execution, x and r would race unless x
          happens-before r. *)
      Lemma redirect_ordered : ~ ~ hb E x r.
      Proof.
        intros Hn.
        assert (Hrf : race_free R).
        { apply Hcs; [apply wf_red|apply exec_red|]. exists T. apply sc_red. }
        apply (Hrf x r). repeat split.
        - apply D_red. auto.
        - apply D_red. auto.
        - apply x_ne_r.
        - exists l. rewrite (act_red_ne x x_ne_r), Ax, act_red_r. auto.
        - left. rewrite (act_red_ne x x_ne_r), Ax. reflexivity.
        - intros H. apply Hn. apply (sub_hb _ _ sub_red). exact H.
        - intros H. apply (sub_hb _ _ sub_red), T_hb in H. lia.
      Qed.
    End Redirect.

    (** In the cut execution, two writes to the same plain variable
        before r are hb-ordered. *)
    Lemma cut_ordered r w x l vw vx :
      (forall i, D E i -> T i < T r -> sees_last E T i) ->
      D E w -> D E x -> T w < T r -> T x < T r -> T w < T x ->
      act E w = AWrite l vw -> act E x = AWrite l vx ->
      ~ ~ hb E w x.
    Proof.
      intros IH Dw Dx Hw Hx Hwx Aw Ax Hn.
      apply (race_free_cut r IH w x). repeat split.
      - apply D_cut. auto.
      - apply D_cut. auto.
      - intros ->. lia.
      - exists l. unfold act, cut. simpl. fold (act E w) (act E x). rewrite Aw, Ax. auto.
      - left. unfold act, cut. simpl. fold (act E w). rewrite Aw. reflexivity.
      - intros H. apply Hn. apply (sub_hb _ _ (sub_cut r)). exact H.
      - intros H. apply (sub_hb _ _ (sub_cut r)), T_hb in H. lia.
    Qed.

    (** ** Every read sees the T-latest write *)

    Lemma good_step r : D E r -> (forall i, D E i -> T i < T r -> sees_last E T i) ->
      sees_last E T r.
    Proof.
      intros Dr IH l v Hread.
      pose proof (wf_ws _ _ _ _ Hwf r l v Dr Hread) as Hws.
      pose proof (Hhb r l v Dr Hread) as Hc.
      destruct (read_of_cases _ _ _ Hread) as [Ar|Ar].
      - (* plain read *)
        assert (Hvol : vol l = false).
        { pose proof (wf_vol _ _ _ _ Hwf r Dr) as H. rewrite Ar in H. exact H. }
        pose proof (latest_in_spec l (T r) (seq 0 (ex_n E))) as Hx.
        destruct (latest_in l (T r) (seq 0 (ex_n E))) as [x|] eqn:Hxe.
        + destruct Hx as (_ & Dx & Wx & Txr & Xmax).
          destruct (plain_write _ _ _ _ Hwf x l Dx Wx Hvol) as [vx Ax].
          assert (Hmax : forall w', D E w' -> write_loc (act E w') = Some l -> T w' < T r ->
                    T w' <= T x).
          { intros w' Dw' Hw' Hlt. apply Xmax; auto. apply in_events; auto. }
          pose proof (redirect_ordered r l v vx x Dr Ar Dx Txr Ax Hmax IH) as Hxr.
          destruct (ex_ws E r) as [w|] eqn:Hw.
          * destruct Hws as [Dw Ww].
            destruct (Nat.eq_dec w x) as [->|Hwx].
            -- repeat split; auto.
            -- exfalso.
               assert (Twr : T w < T r) by (apply (rf_T r w); auto).
               assert (Wl : write_loc (act E w) = Some l) by (eapply write_of_loc; eauto).
               destruct (plain_write _ _ _ _ Hwf w l Dw Wl Hvol) as [vw Aw].
               assert (Twx : T w < T x).
               { pose proof (Hmax w Dw Wl Twr).
                 assert (T w <> T x) by (intros Heq; apply Hwx, T_inj_D; auto). lia. }
               apply (not_not_and (hb E w x) (hb E x r)); auto.
               ++ apply (cut_ordered r w x l vw vx); auto.
               ++ apply (proj2 Hc). exact Wx.
          * exfalso. apply Hxr. apply Hc. exact Wx.
        + destruct (ex_ws E r) as [w|] eqn:Hw.
          * exfalso. destruct Hws as [Dw Ww]. apply (Hx w); auto.
            -- apply in_events; auto.
            -- eapply write_of_loc; eauto.
            -- apply (rf_T r w); auto.
          * split; [exact Hws|]. intros w' Dw' Hw'. apply Hx; auto. apply in_events; auto.
      - (* volatile read: synchronization-order consistency *)
        assert (Hvol : vol l = true).
        { pose proof (wf_vol _ _ _ _ Hwf r Dr) as H. rewrite Ar in H. exact H. }
        assert (Sr : sync E r) by (unfold sync; rewrite Ar; reflexivity).
        pose proof (wf_so_vol _ _ _ _ Hwf r l v Dr Ar) as Hso.
        (* any write to l that is after r in the numbering is after r in T *)
        assert (Hafter : forall w', D E w' -> write_loc (act E w') = Some l -> r < w' -> T r < T w').
        { intros w' Dw' Hw' Hlt.
          destruct (volatile_write _ _ _ _ Hwf w' l Dw' Hw' Hvol) as [vw' Aw'].
          apply Tso. repeat split; auto. unfold sync. rewrite Aw'. reflexivity. }
        assert (Hne : forall w', write_loc (act E w') = Some l -> w' <> r).
        { intros w' Hw' ->. rewrite Ar in Hw'. discriminate. }
        destruct (ex_ws E r) as [w|] eqn:Hw.
        + destruct Hws as [Dw Ww]. destruct Hso as [Hlt Hnb].
          assert (Wl : write_loc (act E w) = Some l) by (eapply write_of_loc; eauto).
          destruct (volatile_write _ _ _ _ Hwf w l Dw Wl Hvol) as [vw Aw].
          assert (Twr : T w < T r).
          { apply Tso. repeat split; auto. unfold sync. rewrite Aw. reflexivity. }
          repeat split; auto.
          intros w' Dw' Hw' Hw'r.
          destruct (volatile_write _ _ _ _ Hwf w' l Dw' Hw' Hvol) as [vw' Aw'].
          destruct (lt_eq_lt_dec w' w) as [[H|H]|H].
          * assert (T w' < T w); [|lia].
            apply Tso. repeat split; auto; unfold sync; [rewrite Aw'|rewrite Aw]; reflexivity.
          * subst. lia.
          * exfalso. destruct (lt_dec w' r) as [H'|H'].
            -- apply (Hnb w' Dw' Hw'). auto.
            -- assert (r < w') by (pose proof (Hne w' Hw'); lia).
               pose proof (Hafter w' Dw' Hw' H0). lia.
        + split; [exact Hws|]. intros w' Dw' Hw' Hw'r.
          destruct (lt_dec w' r) as [H'|H'].
          * exact (Hso w' Dw' Hw' H').
          * assert (r < w') by (pose proof (Hne w' Hw'); lia).
            pose proof (Hafter w' Dw' Hw' H). lia.
    Qed.

    Lemma good_all : forall r, D E r -> sees_last E T r.
    Proof.
      assert (H : forall k r, D E r -> T r < k -> sees_last E T r).
      { induction k as [|k IHk]; intros r Dr Hk; [lia|].
        destruct (lt_dec (T r) k) as [Hlt|Hge]; [apply IHk; auto|].
        apply good_step; auto. intros i Di Hi. apply IHk; auto. lia. }
      intros r Dr. apply (H (S (T r))); auto.
    Qed.

    Lemma drf_sc_given_order : sc_order E T /\ race_free E.
    Proof.
      assert (Hsc : sc_order E T).
      { constructor; auto using T_inj_D, good_all. }
      split; [exact Hsc|]. apply Hcs; auto. exists T. exact Hsc.
    Qed.
  End B.

  (** Theorem (b): DRF-SC for hb-consistency + acyclic(po U so U rf).
      If the program is correctly synchronized, every well-formed,
      hb-consistent execution of it in which po U so U rf is acyclic is
      sequentially consistent and race-free.  Receptiveness: the
      thread-local semantics accepts any value for a plain read. *)
  Theorem drf_sc_no_thin_air
    (L_eq_dec : forall l l' : L, {l = l'} + {l <> l'})
    (P : program L V M C X) (E : execution) :
    receptive (p_lts P) ->
    correctly_synchronized vol init M_eq_dec P ->
    wf E -> exec_of P E -> hb_consistent E ->
    acyclic (fun i j => po E i j \/ so E i j \/ rf E i j) ->
    sequentially_consistent E /\ race_free E.
  Proof.
    intros Hrec Hcs Hwf Hex Hhb Hac.
    destruct (toposort (ex_n E) (fun i j => po E i j \/ so E i j \/ rf E i j))
      as (T & Tinj & Tresp).
    - intros i j. apply or_dec; [apply po_dec|apply or_dec; [apply so_dec|apply rf_dec]].
    - intros i j [H|[H|H]].
      + destruct H as (Di & Dj & _). split; apply (wf_bound _ _ _ _ Hwf); auto.
      + destruct H as (Di & Dj & _). split; apply (wf_bound _ _ _ _ Hwf); auto.
      + destruct H as [Dj Hw]. split; [|apply (wf_bound _ _ _ _ Hwf); auto].
        destruct (read_of (act E j)) as [[l v]|] eqn:Hread.
        * pose proof (wf_ws _ _ _ _ Hwf j l v Dj Hread) as H. rewrite Hw in H.
          apply (wf_bound _ _ _ _ Hwf). apply H.
        * rewrite (wf_ws_none _ _ _ _ Hwf j Dj Hread) in Hw. discriminate.
    - exact Hac.
    - destruct (drf_sc_given_order L_eq_dec P Hrec Hcs E Hwf Hex Hhb T Tinj)
        as [Hsc Hrf]; auto.
      split; [exists T|]; auto.
  Qed.

End DRF.

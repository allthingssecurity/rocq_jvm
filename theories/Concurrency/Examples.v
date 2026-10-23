(* ===================================================================== *)
(*  JVM.Concurrency.Examples                                             *)
(*                                                                       *)
(*  The out-of-thin-air example of JLS SE 21 section 17.4.8:            *)
(*                                                                       *)
(*      x = y = 0 (defaults)                                             *)
(*      Thread 1                     Thread 2                            *)
(*      r1 = x;                      r2 = y;                             *)
(*      if (r1 != 0) y = 1;          if (r2 != 0) x = 1;                 *)
(*                                                                       *)
(*  started by a main thread that spawns both.  We prove:                *)
(*   - [prog_correctly_synchronized]: no SC execution writes anything,   *)
(*     so every SC execution is race-free;                               *)
(*   - [oota_wf], [oota_exec], [oota_hb_consistent]: the execution with  *)
(*     r1 = r2 = 1 (each read sees the other thread's write) is a        *)
(*     well-formed, hb-consistent execution of the program;              *)
(*   - [oota_not_sc]: it is not sequentially consistent;                 *)
(*   - [hb_model_not_drf_sc]: hence the hb model alone does not satisfy  *)
(*     DRF-SC;                                                           *)
(*   - [oota_cyclic]: the execution has a cycle in po U so U rf, so it   *)
(*     is excluded by the hypothesis of theorem (b);                     *)
(*   - [oota_racy]: by theorem (a), it has a data race.                  *)
(* ===================================================================== *)

From Stdlib Require Import List Arith Bool Lia Relations.
From JVM.Concurrency Require Import Events Order Executions DRF.
Import ListNotations.

(** Locations: 0 is x, 1 is y.  Values: nat.  Monitors: unit.
    Spawn payload: the thread's code (1 or 2).  No external actions. *)
Definition Act := action nat nat unit nat unit.

Definition vol0 (l : nat) : bool := false.
Definition init0 (l : nat) : nat := 0.
Definition unit_eq_dec (a b : unit) : {a = b} + {a <> b}.
Proof. destruct a, b. left. reflexivity. Defined.

(** * The program *)

Inductive st : Type :=
| Main (pc : nat)
| Th (k : nat) (pc : nat) (reg : nat).

Definition src (k : nat) : nat := if Nat.eqb k 1 then 0 else 1.
Definition dst (k : nat) : nat := if Nat.eqb k 1 then 1 else 0.

Inductive step : st -> option Act -> st -> Prop :=
| s_main0 : step (Main 0) (Some AStart) (Main 1)
| s_main1 : step (Main 1) (Some (ASpawn 1 1)) (Main 2)
| s_main2 : step (Main 2) (Some (ASpawn 2 2)) (Main 3)
| s_main3 : step (Main 3) (Some AFinish) (Main 4)
| s_start k r : step (Th k 0 r) (Some AStart) (Th k 1 0)
| s_read k r v : step (Th k 1 r) (Some (ARead (src k) v)) (Th k 2 v)
| s_write k v : v <> 0 -> step (Th k 2 v) (Some (AWrite (dst k) 1)) (Th k 3 v)
| s_skip k : step (Th k 2 0) None (Th k 3 0)
| s_fin k v : step (Th k 3 v) (Some AFinish) (Th k 4 v).

Definition Sys : lts nat nat unit nat unit :=
  mkLTS st step (fun c s0 => s0 = Th c 0 0).

Definition prog : program nat nat unit nat unit := mkProg Sys 0 (Main 0).

Lemma prog_receptive : receptive (p_lts prog).
Proof.
  intros s l v s' H v'. simpl in *. inversion H; subst. eexists. apply s_read.
Qed.

(** * No SC execution of the program writes *)

Definition armed (s : st) : Prop := exists k v, v <> 0 /\ s = Th k 2 v.

(* Every write in a run is preceded by a read of a non-zero value,
   unless the run starts in an armed state. *)
Lemma run_write_after_read s as_ s' :
  trun Sys s as_ s' ->
  forall as1 l v as2, as_ = as1 ++ AWrite l v :: as2 ->
  (exists l' v', v' <> 0 /\ In (ARead l' v') as1) \/ armed s.
Proof.
  induction 1 as [s|s s1 as_ s'' Hst Hrun IH|s a s1 as_ s'' Hst Hrun IH];
    intros as1 l v as2 Heq.
  - destruct as1; discriminate.
  - destruct (IH as1 l v as2 Heq) as [H|(k & v' & Hv & ->)]; [left; exact H|].
    simpl in Hst. inversion Hst.
  - destruct as1 as [|a' as1].
    + simpl in Heq. injection Heq as -> _. simpl in Hst. inversion Hst; subst.
      right. exists k, v0. auto.
    + simpl in Heq. injection Heq as -> Heq.
      destruct (IH as1 l v as2 Heq) as [(l' & v' & Hv & Hin)|(k & v' & Hv & ->)].
      * left. exists l', v'. split; [exact Hv| right; exact Hin].
      * simpl in Hst. inversion Hst; subst. left. exists (src k), v'.
        split; [exact Hv| left; reflexivity].
Qed.

Lemma init_not_armed E t s0 : thread_init prog E t s0 -> ~ armed s0.
Proof.
  intros [[_ ->]|(_ & i & c & _ & _ & Hinit)] (k & v & _ & Heq).
  - discriminate.
  - simpl in Hinit. subst. discriminate.
Qed.

Section NoWrites.
  Variable E : execution nat nat unit nat unit.
  Hypothesis Hwf : wf vol0 init0 unit_eq_dec E.
  Hypothesis Hex : exec_of prog E.
  Variable ord : nat -> nat.
  Hypothesis Hsc : sc_order init0 E ord.

  Lemma no_writes_below k : forall i l, D E i -> ord i < k -> write_loc (act E i) <> Some l.
  Proof.
    induction k as [|k IH]; intros i l Di Hk Hw; [lia|].
    destruct (plain_write _ _ _ _ Hwf i l Di Hw eq_refl) as [v Ai].
    set (t := tid_of E i).
    destruct (Hex t (ex_intro _ i (conj Di eq_refl))) as (s0 & s & Hinit & Hrun).
    assert (Hin : In i (thread_ids E t)).
    { unfold thread_ids. apply filter_In. split.
      - apply in_seq. pose proof (wf_bound _ _ _ _ Hwf i Di). lia.
      - unfold D in Di. rewrite Di. simpl. apply Nat.eqb_refl. }
    destruct (in_split _ _ Hin) as (pre & post & Hsplit).
    unfold proj in Hrun. rewrite Hsplit, map_app in Hrun. simpl in Hrun. rewrite Ai in Hrun.
    destruct (run_write_after_read _ _ _ Hrun _ l v _ eq_refl)
      as [(l' & v' & Hv & Hrd)|Harm]; [|exact (init_not_armed _ _ _ Hinit Harm)].
    apply in_map_iff in Hrd as (j & Aj & Hj).
    assert (Hji : j < i) by (unfold thread_ids in Hsplit; eapply filter_seq_sorted; eauto).
    assert (Hjin : In j (thread_ids E t)) by (rewrite Hsplit; apply in_or_app; left; exact Hj).
    unfold thread_ids in Hjin. apply filter_In in Hjin as [_ Hjin].
    apply andb_true_iff in Hjin as [Dj Htj]. apply Nat.eqb_eq in Htj.
    assert (Hord : ord j < ord i) by (apply (sc_po _ _ _ Hsc); repeat split; auto).
    pose proof (sc_reads _ _ _ Hsc j Dj l' v') as Hsl. rewrite Aj in Hsl.
    specialize (Hsl eq_refl).
    destruct (ex_ws E j) as [w|].
    - destruct Hsl as (Dw & Ww & Hwj & _).
      apply (IH w l' Dw ltac:(lia)). eapply write_of_loc. exact Ww.
    - destruct Hsl as [Hv0 _]. apply Hv. exact Hv0.
  Qed.

  Lemma sc_race_free : race_free E.
  Proof.
    intros i j (Di & Dj & _ & (l & Hi & Hj) & Hw & _).
    destruct Hw as [Hw|Hw].
    - destruct (act E i) eqn:Ai; try discriminate. simpl in Hi. injection Hi as ->.
      apply (no_writes_below (S (ord i)) i l Di ltac:(lia)). rewrite Ai. reflexivity.
    - destruct (act E j) eqn:Aj; try discriminate. simpl in Hj. injection Hj as ->.
      apply (no_writes_below (S (ord j)) j l Dj ltac:(lia)). rewrite Aj. reflexivity.
  Qed.
End NoWrites.

Theorem prog_correctly_synchronized : correctly_synchronized vol0 init0 unit_eq_dec prog.
Proof.
  intros E Hwf Hex [ord Hsc]. eapply sc_race_free; eauto.
Qed.

(** * The out-of-thin-air execution r1 = r2 = 1 *)

Definition d0 : event nat nat unit nat unit := mkEv 0 AStart.

Definition evs : list (event nat nat unit nat unit) :=
  [ mkEv 0 AStart; mkEv 0 (ASpawn 1 1); mkEv 0 (ASpawn 2 2); mkEv 0 AFinish;  (* 0-3  *)
    mkEv 1 AStart; mkEv 1 (ARead 0 1); mkEv 1 (AWrite 1 1); mkEv 1 AFinish;    (* 4-7  *)
    mkEv 2 AStart; mkEv 2 (ARead 1 1); mkEv 2 (AWrite 0 1); mkEv 2 AFinish ].  (* 8-11 *)

Definition oota : execution nat nat unit nat unit :=
  mkExec 12 (fun i => Nat.ltb i 12) (fun i => nth i evs d0)
    (fun i => match i with 5 => Some 10 | 9 => Some 6 | _ => None end).

Ltac enum i Di :=
  let Hin := fresh "Hin" in
  assert (Hin : In i (seq 0 12))
    by (apply in_seq; unfold D in Di; simpl in Di; apply Nat.ltb_lt in Di; lia);
  simpl in Hin; repeat (destruct Hin as [<-|Hin]); try contradiction.

Lemma oota_wf : wf vol0 init0 unit_eq_dec oota.
Proof.
  constructor.
  - intros i Di. unfold D in Di. simpl in Di. apply Nat.ltb_lt. exact Di.
  - intros r l v Dr H. enum r Dr; simpl in H; try discriminate;
      injection H as <- <-; simpl; split; reflexivity.
  - intros i Di H. enum i Di; simpl in H; try discriminate; reflexivity.
  - intros i Di. enum i Di; simpl; auto.
  - intros r l v Dr H. enum r Dr; simpl in H; discriminate.
  - intros i m t Di H. enum i Di; simpl in H; discriminate.
  - intros i m Di H. enum i Di; simpl in H; discriminate.
  - intros i Di H. enum i Di; try reflexivity; exfalso;
      first [ apply (H 0); solve [reflexivity | lia]
            | apply (H 4); solve [reflexivity | lia]
            | apply (H 8); solve [reflexivity | lia] ].
  - intros i j Di Dj Aj Ht. enum j Dj; simpl in Aj; try discriminate;
      enum i Di; simpl in Ht; try discriminate; lia.
  - intros i j Di Dj Ai Ht. enum i Di; simpl in Ai; try discriminate;
      enum j Dj; simpl in Ht; try discriminate; lia.
  - intros i j t c Di Dj Ai Ht. enum i Di; simpl in Ai; try discriminate;
      injection Ai as <- <-; enum j Dj; simpl in Ht; try discriminate; lia.
  - intros j t Dj Aj. enum j Dj; simpl in Aj; discriminate.
Qed.

(** No happens-before edge leaves thread 1 (or thread 2). *)
Lemma oota_hb_stays i j k : hb oota i j -> tid_of oota i = k -> k <> 0 -> tid_of oota j = k.
Proof.
  intros H. revert k. induction H as [i j [Hpo|Hsw]|i m j _ IH1 _ IH2]; intros k Ht Hk.
  - destruct Hpo as (_ & _ & _ & H). congruence.
  - destruct Hsw as (Di & Dj & H).
    enum i Di; simpl in Ht; try (subst k; contradiction); simpl in H; try contradiction;
      enum j Dj; simpl in H; contradiction.
  - apply IH2; auto.
Qed.

Lemma oota_hb_consistent : hb_consistent oota.
Proof.
  intros r l v Dr H.
  pose proof (hb_lt _ _ _ _ oota_wf) as Hlt.
  enum r Dr; simpl in H; try discriminate; injection H as <- <-; simpl.
  - split.
    + intros Hb. apply (oota_hb_stays 5 10 1) in Hb; [discriminate|reflexivity|lia].
    + intros w' Hw' [H1 H2]. apply Hlt in H1, H2. lia.
  - split.
    + intros Hb. apply Hlt in Hb. lia.
    + intros w' Hw' [H1 H2]. destruct (hb_dom _ _ _ H1) as [_ Dw].
      apply Hlt in H1, H2. enum w' Dw; simpl in Hw'; try discriminate; lia.
Qed.

Lemma oota_threads t : (exists i, D oota i /\ tid_of oota i = t) -> t = 0 \/ t = 1 \/ t = 2.
Proof.
  intros (i & Di & <-). enum i Di; simpl; auto.
Qed.

Lemma oota_exec : exec_of prog oota.
Proof.
  intros t Ht. destruct (oota_threads t Ht) as [-> | [-> | ->]].
  - exists (Main 0), (Main 4). split.
    + left. split; reflexivity.
    + change (proj oota 0) with [@AStart nat nat unit nat unit; ASpawn 1 1; ASpawn 2 2; AFinish].
      eapply trun_act; [apply s_main0|].
      eapply trun_act; [apply s_main1|].
      eapply trun_act; [apply s_main2|].
      eapply trun_act; [apply s_main3|].
      apply trun_nil.
  - exists (Th 1 0 0), (Th 1 4 1). split.
    + right. split; [discriminate|]. exists 1, 1. repeat split.
    + change (proj oota 1) with [@AStart nat nat unit nat unit; ARead 0 1; AWrite 1 1; AFinish].
      eapply trun_act; [apply (s_start 1 0)|].
      eapply trun_act; [apply (s_read 1 0 1)|].
      eapply trun_act; [apply (s_write 1 1); discriminate|].
      eapply trun_act; [apply s_fin|].
      apply trun_nil.
  - exists (Th 2 0 0), (Th 2 4 1). split.
    + right. split; [discriminate|]. exists 2, 2. repeat split.
    + change (proj oota 2) with [@AStart nat nat unit nat unit; ARead 1 1; AWrite 0 1; AFinish].
      eapply trun_act; [apply (s_start 2 0)|].
      eapply trun_act; [apply (s_read 2 0 1)|].
      eapply trun_act; [apply (s_write 2 1); discriminate|].
      eapply trun_act; [apply s_fin|].
      apply trun_nil.
Qed.

Lemma oota_not_sc : ~ sequentially_consistent init0 oota.
Proof.
  intros [ord Hsc].
  assert (H56 : ord 5 < ord 6) by (apply (sc_po _ _ _ Hsc); repeat split; lia).
  assert (H910 : ord 9 < ord 10) by (apply (sc_po _ _ _ Hsc); repeat split; lia).
  assert (H105 : ord 10 < ord 5).
  { pose proof (sc_reads _ _ _ Hsc 5 eq_refl 0 1 eq_refl) as H. simpl in H. apply H. }
  assert (H69 : ord 6 < ord 9).
  { pose proof (sc_reads _ _ _ Hsc 9 eq_refl 1 1 eq_refl) as H. simpl in H. apply H. }
  lia.
Qed.

(** The hb model (well-formedness + hb-consistency) does not guarantee
    DRF-SC: a correctly synchronized program has a well-formed,
    hb-consistent execution that is not sequentially consistent. *)
Theorem hb_model_not_drf_sc :
  exists (P : program nat nat unit nat unit) (E : execution nat nat unit nat unit),
    receptive (p_lts P) /\ correctly_synchronized vol0 init0 unit_eq_dec P /\
    wf vol0 init0 unit_eq_dec E /\ exec_of P E /\ hb_consistent E /\
    ~ sequentially_consistent init0 E.
Proof.
  exists prog, oota.
  exact (conj prog_receptive (conj prog_correctly_synchronized
          (conj oota_wf (conj oota_exec (conj oota_hb_consistent oota_not_sc))))).
Qed.

(** The execution has the cycle 5 -po-> 6 -rf-> 9 -po-> 10 -rf-> 5, so it
    is excluded by acyclic(po U so U rf), the extra hypothesis of
    theorem (b). *)
Theorem oota_cyclic : ~ acyclic (fun i j => po oota i j \/ so oota i j \/ rf oota i j).
Proof.
  intros Hac. apply (Hac 5).
  apply t_trans with 6; [apply t_step; left; repeat split; lia|].
  apply t_trans with 9; [apply t_step; right; right; split; reflexivity|].
  apply t_trans with 10; [apply t_step; left; repeat split; lia|].
  apply t_step. right. right. split; reflexivity.
Qed.

(** Consistently with theorem (b): every well-formed, hb-consistent
    execution of the program without such a cycle is SC. *)
Corollary prog_drf_sc (E : execution nat nat unit nat unit) :
  wf vol0 init0 unit_eq_dec E -> exec_of prog E -> hb_consistent E ->
  acyclic (fun i j => po E i j \/ so E i j \/ rf E i j) ->
  sequentially_consistent init0 E.
Proof.
  intros. apply (drf_sc_no_thin_air vol0 init0 unit_eq_dec Nat.eq_dec prog E); auto.
  - apply prog_receptive.
  - apply prog_correctly_synchronized.
Qed.

(** By theorem (a), the thin-air execution must have a data race (the
    read of x in thread 1 and the write of x in thread 2 are not
    ordered by hb). *)
Corollary oota_racy : ~ race_free oota.
Proof.
  intros Hrf. apply oota_not_sc.
  apply (drf_execution_sc vol0 init0 unit_eq_dec); auto using oota_wf, oota_hb_consistent.
Qed.

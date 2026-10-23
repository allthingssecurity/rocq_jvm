(** * Calibration: camel-wal [TransactionLog.canUpdate(IIII)Z], CAMEL-26088.

    Both methods are taken from the real class files (see the headers of
    [JVM.Classes.WalMain_TransactionLog] and [JVM.Classes.WalFix_TransactionLog]
    for commit, javac version and SHA-256):
    - main: apache/camel 36bebb520a632d0d02a90680bba60e2a1e3941f9
    - fix:  branch camel-wal-update-after-roll-over, e72996b974ad97f55b3ba3f73497adbf27a6609d

    Results (all for the bytecode obtained by [load_method] = Rocq parser +
    decoder applied to the file's bytes, run by [invoke_static]):
    - [main_behaviour], [fix_behaviour]: exact input/output function of each
      method for all int arguments (fix: for a current layer >= 0).
    - [fix_correct]: the fix satisfies [canUpdate_contract] (WalSpec.v) for
      every reachable ring-buffer state and every added entry.
    - [main_refuted]: main does NOT satisfy the contract; two counterexamples
      (one live entry rejected: the off-by-one; one overwritten entry accepted:
      the stale-layer bug), the same inputs JBMC reported in r79.
    Every [invoke_static] statement uses 100 steps of fuel; [invoke_static_mono]
    extends each to any larger fuel. *)

From Stdlib Require Import ZArith Lia Bool String List.
From JVM.Core Require Import Int Instr Desc Semantics Tactics.
From JVM.Loader Require Import ClassFile.
From JVM.Camel Require Import WalSpec.
From JVM.Classes Require WalMain_TransactionLog WalFix_TransactionLog.
Import ListNotations.
Open Scope Z_scope.

Definition canUpdate_main : option method :=
  load_method WalMain_TransactionLog.bytes "canUpdate" "(IIII)Z".
Definition canUpdate_fix : option method :=
  load_method WalFix_TransactionLog.bytes "canUpdate" "(IIII)Z".

(** Run a loaded method on four ints and read back a boolean result. *)
Definition call4 (m : option method) (a b c d : Z) : result :=
  match m with
  | Some m => invoke_static 100 m [VInt a; VInt b; VInt c; VInt d]
  | None => RStuck "method not found"
  end.

Definition ret_bool (b : bool) : result := RValue (Some (VInt (if b then 1 else 0))).

(** The decoded code, computed (not written by hand) from the bytes. *)
Lemma canUpdate_main_eq :
  canUpdate_main = ltac:(let x := eval vm_compute in canUpdate_main in exact x).
Proof. vm_compute. reflexivity. Qed.
Lemma canUpdate_fix_eq :
  canUpdate_fix = ltac:(let x := eval vm_compute in canUpdate_fix in exact x).
Proof. vm_compute. reflexivity. Qed.

Lemma in_int_rangeb : forall z, in_int z -> in_rangeb 32 z = true.
Proof. intros. apply in_rangeb_spec. exact H. Qed.

(** ** What main's bytecode computes *)
Theorem main_behaviour : forall a b c d,
  in_int a -> in_int b -> in_int c -> in_int d ->
  call4 canUpdate_main a b c d = ret_bool ((a =? c) && (d <=? b) || (c <? a) && (b <? d)).
Proof.
  intros a b c d Ha Hb Hc Hd.
  unfold call4. rewrite canUpdate_main_eq. unfold invoke_static.
  cbn -[in_rangeb wrap].
  rewrite !in_int_rangeb by assumption. unfold ret_bool.
  unfold ret_bool; symex; finish_branch.
Qed.

(** ** What the fix's bytecode computes (current layer [a] >= 0, which every
    reachable state satisfies; it rules out the [entryInfoLayer + 1] overflow
    mattering). *)
Theorem fix_behaviour : forall a b c d,
  in_int a -> in_int b -> in_int c -> in_int d -> 0 <= a ->
  call4 canUpdate_fix a b c d = ret_bool ((a =? c) && (d <=? b) || (a =? c + 1) && (b <=? d)).
Proof.
  intros a b c d Ha Hb Hc Hd Ha0.
  unfold call4. rewrite canUpdate_fix_eq. unfold invoke_static.
  cbn -[in_rangeb wrap].
  rewrite !in_int_rangeb by assumption. unfold ret_bool.
  assert (Hw : (c < INT_MAX /\ wrap 32 (c + 1) = c + 1) \/ (c = INT_MAX /\ wrap 32 (c + 1) = INT_MIN)).
  { destruct (Z.eq_dec c INT_MAX) as [E|E].
    - right. split; [exact E|]. subst c. reflexivity.
    - left. split; [unfold in_int, in_range, INT_MAX in *; simpl in *; lia|].
      apply wrap32_id. unfold in_int, in_range, INT_MAX in *; simpl in *; lia. }
  destruct Hw as [[Hlt Hw]|[Heq Hw]];
  symex; try rewrite Hw in *; finish_branch.
Qed.

(** ** The fix meets the contract *)
(** For every reachable ring-buffer state and every added entry, the fix's
    bytecode returns exactly [live] (as the JVM int 1/0 of a boolean). *)
Theorem fix_correct_exact : forall cap n k, reachable cap n k ->
  call4 canUpdate_fix (cur_layer cap n) (cur_index cap n) (ent_layer cap k) (ent_index cap k)
  = ret_bool (live cap n k).
Proof.
  intros cap n k Hr.
  destruct (live_linear cap n k Hr) as (Hlive & HeL & HeI & HcI & Hsame & HcL).
  set (cL := cur_layer cap n) in *. set (cI := cur_index cap n) in *.
  set (eL := ent_layer cap k) in *. set (eI := ent_index cap k) in *.
  assert (Hint : forall z, -2147483648 <= z <= 2147483647 -> in_int z)
    by (intros; unfold in_int, in_range; simpl; lia).
  destruct Hr as (Hcap & Hk & Hl). unfold INT_MAX in *.
  rewrite fix_behaviour by (try apply Hint; simpl in *; lia).
  case_eq (live cap n k); intro L.
  - apply Hlive in L. unfold ret_bool.
    destruct L as [E|[E1 E2]].
    + replace ((cL =? eL) && (eI <=? cI)) with true by
        (symmetry; apply andb_true_iff; split; [apply Z.eqb_eq | apply Z.leb_le]; specialize (Hsame E); lia).
      reflexivity.
    + replace ((cL =? eL + 1) && (cI <=? eI)) with true by
        (symmetry; apply andb_true_iff; split; [apply Z.eqb_eq | apply Z.leb_le]; lia).
      rewrite orb_true_r. reflexivity.
  - assert (NL : ~ (eL = cL \/ (eL + 1 = cL /\ cI <= eI))) by (rewrite <- Hlive; congruence).
    unfold ret_bool.
    replace ((cL =? eL) && (eI <=? cI) || (cL =? eL + 1) && (cI <=? eI)) with false.
    + reflexivity.
    + symmetry. apply orb_false_iff; split; apply andb_false_iff;
      destruct (Z.eq_dec cL eL); destruct (Z.eq_dec cL (eL + 1));
      try (left; apply Z.eqb_neq; lia); right; apply Z.leb_gt; lia.
Qed.

Theorem fix_correct :
  canUpdate_contract (fun a b c d =>
    match call4 canUpdate_fix a b c d with
    | RValue (Some (VInt 1)) => true
    | _ => false
    end).
Proof.
  intros cap n k Hr. rewrite fix_correct_exact by exact Hr. destruct (live cap n k); reflexivity.
Qed.

(** The same for any amount of fuel >= 100 (the method needs at most 8 steps). *)
Corollary fix_correct_any_fuel : forall cap n k fuel, reachable cap n k -> (100 <= fuel)%nat ->
  exists m, canUpdate_fix = Some m /\
    invoke_static fuel m [VInt (cur_layer cap n); VInt (cur_index cap n);
                          VInt (ent_layer cap k); VInt (ent_index cap k)] = ret_bool (live cap n k).
Proof.
  intros cap n k fuel Hr Hf.
  pose proof (fix_correct_exact cap n k Hr) as H. unfold call4 in H.
  destruct canUpdate_fix as [m|] eqn:E; [|discriminate].
  exists m. split; [reflexivity|].
  eapply invoke_static_mono; [exact H| |exact Hf].
  unfold ret_bool; destruct (live cap n k); discriminate.
Qed.

(** ** Main violates the contract *)
Theorem main_refuted :
  ~ canUpdate_contract (fun a b c d =>
      match call4 canUpdate_main a b c d with
      | RValue (Some (VInt 1)) => true
      | _ => false
      end).
Proof.
  intros H.
  (* capacity 377, 10345 adds, entry 9968: live (one layer behind, same
     index as the next write), but main's bytecode returns false. *)
  specialize (H 377 10345 9968).
  assert (R : reachable 377 10345 9968)
    by (unfold reachable, INT_MAX; repeat split; compute; try (intro; discriminate); reflexivity).
  specialize (H R). vm_compute in H. discriminate H.
Qed.

(** The two counterexamples spelled out with their concrete call arguments. *)
Example main_rejects_live_entry :
  live 377 10345 9968 = true /\
  (cur_layer 377 10345, cur_index 377 10345, ent_layer 377 9968, ent_index 377 9968) = (27, 166, 26, 166) /\
  call4 canUpdate_main 27 166 26 166 = ret_bool false.
Proof. vm_compute. auto. Qed.

Example main_accepts_overwritten_entry :
  reachable 575 81556 28088 /\ live 575 81556 28088 = false /\
  (cur_layer 575 81556, cur_index 575 81556, ent_layer 575 28088, ent_index 575 28088) = (141, 481, 48, 488) /\
  call4 canUpdate_main 141 481 48 488 = ret_bool true.
Proof.
  repeat split; unfold reachable, INT_MAX; repeat split; compute; try (intro; discriminate); reflexivity.
Qed.

Example fix_on_the_same_inputs :
  call4 canUpdate_fix 27 166 26 166 = ret_bool true /\
  call4 canUpdate_fix 141 481 48 488 = ret_bool false.
Proof. vm_compute. auto. Qed.

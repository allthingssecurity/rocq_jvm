(** * Reasoning about machine runs: run segments, fuel composition, symbolic execution.

    [leads p mdl s s'] says: running from [s] reaches [s'] after some number
    [k] of steps, so any run from [s'] with [n] fuel is a run from [s] with
    [k + n] fuel.  Proofs about methods with loops chain such segments: one
    segment per loop iteration (proved by symbolic execution, [sym_step]) and
    induction over the iterations. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
Import ListNotations.
Open Scope string_scope.

Section Runs.
  Variable p : program.
  Variable mdl : model.

  Definition leads (s s' : mstate) : Prop :=
    exists k, forall n, mrun p mdl (k + n) s = mrun p mdl n s'.

  Lemma leads_refl : forall s, leads s s.
  Proof. intros s. exists 0%nat. reflexivity. Qed.

  Lemma leads_trans : forall s1 s2 s3, leads s1 s2 -> leads s2 s3 -> leads s1 s3.
  Proof.
    intros s1 s2 s3 [k1 H1] [k2 H2]. exists (k1 + k2)%nat. intros n.
    rewrite <- Nat.add_assoc, H1, H2. reflexivity.
  Qed.

  Lemma leads_step : forall s s1 s', mstep_of p mdl s = MNext s1 -> leads s1 s' -> leads s s'.
  Proof.
    intros s s1 s' Hs [k Hk]. exists (S k). intros n. simpl. rewrite Hs. apply Hk.
  Qed.

  (** A run that reaches a return of the bottom frame. *)
  Definition returns (s : mstate) (v : option value) (P : mstate -> Prop) : Prop :=
    exists k s', mrun p mdl k s = MRValue v s' /\ P s'.

  Lemma returns_step : forall s s1 v P, mstep_of p mdl s = MNext s1 -> returns s1 v P -> returns s v P.
  Proof.
    intros s s1 v P Hs (k & s' & Hk & HP). exists (S k), s'. simpl. rewrite Hs. auto.
  Qed.

  Lemma returns_leads : forall s s1 v P, leads s s1 -> returns s1 v P -> returns s v P.
  Proof.
    intros s s1 v P [k Hk] (k' & s' & H & HP). exists (k + k')%nat, s'. rewrite Hk. auto.
  Qed.

  Lemma returns_now : forall s v s' (P : mstate -> Prop),
    mstep_of p mdl s = MReturn v s' -> P s' -> returns s v P.
  Proof. intros s v s' P Hs HP. exists 1%nat, s'. simpl. rewrite Hs. auto. Qed.

  (** Fuel: a run that returns keeps returning the same with more fuel. *)
  Lemma returns_fuel : forall s v P, returns s v P ->
    exists k, forall n, (k <= n)%nat -> exists s', mrun p mdl n s = MRValue v s' /\ P s'.
  Proof.
    intros s v P (k & s' & H & HP). exists k. intros n Hn. exists s'. split; auto.
    eapply mrun_mono; eauto. discriminate.
  Qed.
End Runs.

(** ** Heap update lemmas used by symbolic execution *)
Lemma upd_same : forall {A} (h : Z -> option A) l o, upd h l o l = Some o.
Proof. intros. unfold upd. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma upd_other : forall {A} (h : Z -> option A) l l' o, l' <> l -> upd h l o l' = h l'.
Proof. intros. unfold upd. destruct (Z.eqb_spec l' l); congruence. Qed.

(** One symbolic step: compute [mstep_of] with [cbn], keeping the integer
    helpers folded, rewrite heap lookups with the hypotheses, and close the
    step with the reflexive instance of [MNext ?s]. *)

Ltac sym_rewrite :=
  repeat match goal with
  | H : ?h ?l = Some _ |- context [?h ?l] => rewrite H
  | |- context [upd ?h ?l ?o ?l] => rewrite upd_same
  end.

(** ** Controlled symbolic execution: step lemmas for [mstep_of].
    Instead of letting [cbn] unfold the whole machine step (which explodes on
    symbolic states), a proof applies one of these lemmas per instruction:
    frame-local instructions reduce to [Semantics.step] (small, cbn-friendly);
    calls into models reduce to the model's result. *)



Lemma mstep_local : forall p mdl s top rest i nx f',
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (i, nx) ->
  is_local_instr i = true ->
  step (cf_code top) (cf_rt top) (cf_frame top) = Normal f' ->
  (stack_slots (f_stack f') <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s = MNext (with_frames s (set_frame top f' :: rest)).
Proof.
  intros p mdl s top rest i nx f' Hfr Hf Hl Hs Hb.
  unfold mstep_of. rewrite Hfr, Hf, Hl, Hs, Hb. reflexivity.
Qed.

Lemma mstep_local_return : forall p mdl s top i nx v,
  ms_frames s = [top] ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (i, nx) ->
  is_local_instr i = true ->
  cf_clinit top = false ->
  step (cf_code top) (cf_rt top) (cf_frame top) = Done v ->
  mstep_of p mdl s = MReturn v (with_frames s nil).
Proof.
  intros p mdl s top i nx v Hfr Hf Hl Hc Hs.
  unfold mstep_of. rewrite Hfr, Hf, Hl, Hs, Hc. reflexivity.
Qed.


(** Every invoke instruction is handled by [do_invoke]. *)
Lemma mstep_invoke : forall p mdl s top rest k mr nx ps rt args r,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke k mr, nx) ->
  parse_mdesc (mr_desc mr) = Some (ps, rt) ->
  pop_n (length ps + match k with InvStatic => 0 | _ => 1 end)%nat (f_stack (cf_frame top)) = Some (args, r) ->
  mstep_of p mdl s = do_invoke 8 p mdl s top rest k mr args r nx.
Proof.
  intros p mdl s top rest k mr nx ps rt args r Hfr Hf Hd Hp.
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite Hd, Hp. reflexivity.
Qed.

Lemma do_invoke_static_model : forall p mdl s top rest mr args r nx v s',
  erroneous p 64 (ms_statics s) (mr_class mr) = false ->
  init_needed p 64 (ms_inited s) (mr_class mr) = None ->
  resolve_full p (mr_class mr) (mr_name mr) (mr_desc mr) = None ->
  mdl (mr_class mr) (mr_name mr) (mr_desc mr) args s = MOk v s' ->
  let st' := match v with Some w => w :: r | None => r end in
  (stack_slots st' <=? c_max_stack (cf_code top))%Z = true ->
  do_invoke 8 p mdl s top rest InvStatic mr args r nx =
    MNext (with_frames (with_frames s' (ms_frames s))
             (set_frame top (mkframe nx st' (f_locals (cf_frame top))) :: rest)).
Proof.
  intros p mdl s top rest mr args r nx v s' He Hi Hr Hm st' Hb.
  unfold do_invoke. rewrite He, Hi, Hr. unfold invoke_run_model. rewrite Hm.
  unfold invoke_frame_go. subst st'. rewrite Hb. reflexivity.
Qed.

(** A virtual/interface call on a String receiver answered by the String model. *)
Lemma do_invoke_string_model : forall p mdl s top rest k mr l u more r nx v s',
  (k = InvVirtual \/ k = InvInterface) ->
  ms_heap s l = Some (OStr u) ->
  resolve_full p "java/lang/String" (mr_name mr) (mr_desc mr) = None ->
  first_unloaded p 64 "java/lang/String" = "java/lang/String" ->
  mdl "java/lang/String" (mr_name mr) (mr_desc mr) (VRef l :: more) s = MOk v s' ->
  let st' := match v with Some w => w :: r | None => r end in
  (stack_slots st' <=? c_max_stack (cf_code top))%Z = true ->
  do_invoke 8 p mdl s top rest k mr (VRef l :: more) r nx =
    MNext (with_frames (with_frames s' (ms_frames s))
             (set_frame top (mkframe nx st' (f_locals (cf_frame top))) :: rest)).
Proof.
  intros p mdl s top rest k mr l u more r nx v s' Hk Hh Hr Hu Hm st' Hb.
  assert (E : do_invoke 8 p mdl s top rest k mr (VRef l :: more) r nx =
              invoke_obj (fun k' impl args' => do_invoke 7 p mdl s top rest k' impl args' r nx)
                         p mdl s top rest k mr l more (ms_heap s l) r nx)
    by (destruct Hk as [-> | ->]; reflexivity).
  rewrite E, Hh. unfold invoke_obj.
  destruct Hk as [-> | ->]; rewrite Hr, Hu, Hm; unfold invoke_run_model; rewrite Hm;
  unfold invoke_frame_go; subst st'; rewrite Hb; reflexivity.
Qed.

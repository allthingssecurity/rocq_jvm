(** * Reasoning about machine runs: run segments, fuel composition, symbolic execution.

    [leads p mdl s s'] says: running from [s] reaches [s'] after some number
    [k] of steps, so any run from [s'] with [n] fuel is a run from [s] with
    [k + n] fuel.  Proofs about methods with loops chain such segments: one
    segment per loop iteration (proved by symbolic execution, [sym_step]) and
    induction over the iterations. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
From JVM.Loader Require Import ClassFile.
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

(** ** Step lemmas for heap instructions and calls into bytecode *)
Section HeapSteps.
Variable p : program.
Variable mdl : model.

Lemma mstep_getfield : forall s top rest fr nx l r c fs v,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Getfield fr, nx) ->
  f_stack (cf_frame top) = VRef l :: r ->
  ms_heap s l = Some (OObj c fs) ->
  obj_get p fr fs = Some v ->
  (stack_slots (v :: r) <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s = MNext (with_frames s (set_frame top (mkframe nx (v :: r) (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest fr nx l r c fs v Hfr Hf Hst Hh Ha Hb.
  unfold obj_get in Ha. destruct (field_slot p fr fs) as [key| |] eqn:Hk; try discriminate Ha.
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite Hst, Hh, Hk, Ha. cbv beta iota zeta; cbn [f_stack f_pc f_locals]. rewrite Hb. reflexivity.
Qed.

Lemma mstep_putfield : forall s top rest fr nx v l r c fs t fs',
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Putfield fr, nx) ->
  f_stack (cf_frame top) = v :: VRef l :: r ->
  field_type (fr_desc fr) = Some t ->
  value_fits t v = true ->
  ms_heap s l = Some (OObj c fs) ->
  obj_set p fr (narrow_store t v) fs = Some fs' ->
  (stack_slots r <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s =
    MNext (with_frames {| ms_heap := upd (ms_heap s) l (OObj c fs'); ms_next := ms_next s;
                          ms_statics := ms_statics s; ms_inited := ms_inited s; ms_locks := ms_locks s;
                          ms_frames := ms_frames s |}
             (set_frame top (mkframe nx r (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest fr nx v l r c fs t fs' Hfr Hf Hst Ht Hv Hh Ha Hb.
  unfold obj_set in Ha. destruct (field_slot p fr fs) as [key| |] eqn:Hk; try discriminate Ha.
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite Hst, Ht.
  destruct v; cbn [value_fits] in Hv; try discriminate Hv; cbn [negb];
  rewrite ?Hv; cbn [negb]; rewrite Hh, Hk, Ha; cbv beta iota zeta; cbn [f_stack f_pc f_locals]; rewrite Hb; reflexivity.
Qed.

Lemma mstep_getstatic : forall s top rest fr nx v,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Getstatic fr, nx) ->
  erroneous p 64 (ms_statics s) (fr_class fr) = false ->
  init_needed p 64 (ms_inited s) (fr_class fr) = None ->
  assoc (static_key (fr_class fr) (fr_name fr)) (ms_statics s) = Some v ->
  (stack_slots (v :: f_stack (cf_frame top)) <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s = MNext (with_frames s (set_frame top
                         (mkframe nx (v :: f_stack (cf_frame top)) (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest fr nx v Hfr Hf He Hi Ha Hb.
  assert (Ht : static_target p s fr = STKey (static_key (fr_class fr) (fr_name fr)))
    by (unfold static_target; rewrite He, Hi, Ha; reflexivity).
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite Ht, Ha. cbv beta iota zeta; cbn [f_stack f_pc f_locals]. rewrite Hb. reflexivity.
Qed.

Lemma mstep_aaload : forall s top rest nx i l r e es v,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (ALoadArr AA, nx) ->
  f_stack (cf_frame top) = VInt i :: VRef l :: r ->
  ms_heap s l = Some (OArr e es) ->
  akind_load_ok AA e = true ->
  ((i <? 0) || (Z.of_nat (length es) <=? i))%Z = false ->
  nth_z es i = Some v ->
  (stack_slots (v :: r) <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s = MNext (with_frames s (set_frame top (mkframe nx (v :: r) (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest nx i l r e es v Hfr Hf Hst Hh Hk Hr Hn Hb.
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite Hst, Hh, Hk. cbn [negb]. rewrite Hr, Hn. cbv beta iota zeta; cbn [f_stack f_pc f_locals]. rewrite Hb.
  reflexivity.
Qed.

Lemma mstep_aastore_ref : forall s top rest nx vl i l r e es o cname,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (AStoreArr AA, nx) ->
  f_stack (cf_frame top) = VRef vl :: VInt i :: VRef l :: r ->
  ms_heap s l = Some (OArr e es) ->
  akind_ok AA e (VRef vl) = true ->
  ((i <? 0) || (Z.of_nat (length es) <=? i))%Z = false ->
  ms_heap s vl = Some o ->
  (match e with TArr _ => type_desc e | TRef c => c | _ => "" end) = cname ->
  assignable p 64 (runtime_type o) cname = Some true ->
  (stack_slots r <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s =
    MNext (with_frames {| ms_heap := upd (ms_heap s) l (OArr e (set_nth_z es i (narrow_store e (VRef vl))));
                          ms_next := ms_next s; ms_statics := ms_statics s; ms_inited := ms_inited s;
                          ms_locks := ms_locks s; ms_frames := ms_frames s |}
             (set_frame top (mkframe nx r (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest nx vl i l r e es o cname Hfr Hf Hst Hh Hk Hr Ho Hc Ha Hb.
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite Hst, Hh, Hk. cbn [negb]. rewrite Hr, Ho.
  rewrite Hc, Ha. cbv beta iota zeta; cbn [f_stack f_pc f_locals]. rewrite Hb. reflexivity.
Qed.

Lemma mstep_new : forall s top rest cn nx fs,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (New cn, nx) ->
  erroneous p 64 (ms_statics s) cn = false ->
  init_needed p 64 (ms_inited s) cn = None ->
  instance_fields p 64 cn = Some fs ->
  (stack_slots (VRef (ms_next s) :: f_stack (cf_frame top)) <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s =
    MNext (with_frames (snd (alloc s (OObj cn fs)))
             (set_frame top (mkframe nx (VRef (ms_next s) :: f_stack (cf_frame top)) (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest cn nx fs Hfr Hf He Hi Hfs Hb.
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite He, Hi, Hfs. cbn [alloc fst snd].
  cbv beta iota zeta; cbn [f_stack f_pc f_locals]. rewrite Hb. reflexivity.
Qed.

(** Calls into loaded bytecode: [enter] pushes the callee frame. *)
Lemma do_invoke_static_enter : forall s top rest mr args r nx cn m,
  erroneous p 64 (ms_statics s) (mr_class mr) = false ->
  init_needed p 64 (ms_inited s) (mr_class mr) = None ->
  resolve_full p (mr_class mr) (mr_name mr) (mr_desc mr) = Some (cn, m) ->
  Z.testbit (m_access m) 8 = false ->
  do_invoke 8 p mdl s top rest InvStatic mr args r nx =
    enter s (set_frame top (mkframe (f_pc (cf_frame top)) r (f_locals (cf_frame top)))) rest cn m args nx.
Proof.
  intros s top rest mr args r nx cn m He Hi Hr Hn. unfold do_invoke. rewrite He, Hi, Hr, Hn. reflexivity.
Qed.

Lemma do_invoke_obj_enter : forall s top rest k mr l more r nx cls fs cn m,
  (k = InvVirtual \/ k = InvInterface) ->
  ms_heap s l = Some (OObj cls fs) ->
  resolve_full p cls (mr_name mr) (mr_desc mr) = Some (cn, m) ->
  Z.testbit (m_access m) 8 = false ->
  do_invoke 8 p mdl s top rest k mr (VRef l :: more) r nx =
    enter s (set_frame top (mkframe (f_pc (cf_frame top)) r (f_locals (cf_frame top)))) rest cn m (VRef l :: more) nx.
Proof.
  intros s top rest k mr l more r nx cls fs cn m Hk Hh Hr Hn.
  assert (E : do_invoke 8 p mdl s top rest k mr (VRef l :: more) r nx =
              invoke_obj (fun k' impl args' => do_invoke 7 p mdl s top rest k' impl args' r nx)
                         p mdl s top rest k mr l more (ms_heap s l) r nx)
    by (destruct Hk as [-> | ->]; reflexivity).
  rewrite E, Hh. unfold invoke_obj. destruct Hk as [-> | ->]; rewrite Hr, Hn; reflexivity.
Qed.

Lemma do_invoke_special_enter : forall s top rest mr l more r nx o cn m,
  ms_heap s l = Some o ->
  (match o with OLam _ _ _ _ _ => false | _ => true end) = true ->
  resolve_full p (mr_class mr) (mr_name mr) (mr_desc mr) = Some (cn, m) ->
  Z.testbit (m_access m) 8 = false ->
  do_invoke 8 p mdl s top rest InvSpecial mr (VRef l :: more) r nx =
    enter s (set_frame top (mkframe (f_pc (cf_frame top)) r (f_locals (cf_frame top)))) rest cn m (VRef l :: more) nx.
Proof.
  intros s top rest mr l more r nx o cn m Hh Ho Hr Hn.
  assert (E : do_invoke 8 p mdl s top rest InvSpecial mr (VRef l :: more) r nx =
              invoke_obj (fun k' impl args' => do_invoke 7 p mdl s top rest k' impl args' r nx)
                         p mdl s top rest InvSpecial mr l more (ms_heap s l) r nx) by reflexivity.
  rewrite E, Hh. unfold invoke_obj. destruct o; try discriminate Ho; rewrite Hr, Hn; reflexivity.
Qed.

(** Return from a callee to its caller. *)
Lemma mstep_return_to : forall s top caller rest i nx v nx',
  ms_frames s = top :: caller :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (i, nx) ->
  is_local_instr i = true ->
  cf_clinit top = false ->
  step (cf_code top) (cf_rt top) (cf_frame top) = Done v ->
  cf_resume caller = Some nx' ->
  mstep_of p mdl s =
    MNext (with_frames s (set_resume (set_frame caller
             (mkframe nx' (match v with Some w => w :: f_stack (cf_frame caller) | None => f_stack (cf_frame caller) end)
                      (f_locals (cf_frame caller)))) None :: rest)).
Proof.
  intros s top caller rest i nx v nx' Hfr Hf Hl Hc Hs Hr.
  unfold mstep_of. rewrite Hfr, Hf, Hl, Hs, Hc. unfold return_to. rewrite Hr. reflexivity.
Qed.
End HeapSteps.

Section MoreSteps.
Variable p : program.
Variable mdl : model.

Lemma init_needed_done : forall k inited c cf,
  find_class p c = Some cf -> existsb (String.eqb c) inited = true -> init_needed p (S k) inited c = None.
Proof. intros k inited c cf Hf He. simpl. rewrite Hf, He. reflexivity. Qed.

Lemma mstep_ldc_string : forall s top rest raw nx u,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Ldc (LdcString raw), nx) ->
  utf8_units raw = Some u ->
  (stack_slots (VRef (fst (intern s (OStr u))) :: f_stack (cf_frame top)) <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s =
    MNext (with_frames (snd (intern s (OStr u)))
             (set_frame top (mkframe nx (VRef (fst (intern s (OStr u))) :: f_stack (cf_frame top))
                                     (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest raw nx u Hfr Hf Hu Hb.
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite Hu.
  destruct (intern s (OStr u)) as [l s'] eqn:Ei. cbn [fst snd] in *.
  cbv beta iota zeta; cbn [f_stack f_pc f_locals]. rewrite Hb. reflexivity.
Qed.

(** Interning only allocates a fresh object: old objects, frames and initialisation state are unchanged. *)
Lemma intern_old : forall s o x, x < ms_next s -> ms_heap (snd (intern s o)) x = ms_heap s x.
Proof.
  intros s o x Hx. unfold intern. destruct (assoc (intern_key o) (ms_statics s)) as [[]|]; simpl; try reflexivity.
  all: unfold upd; destruct (Z.eqb_spec x (ms_next s)); [lia | reflexivity].
Qed.

Lemma intern_next : forall s o, ms_next s <= ms_next (snd (intern s o)).
Proof.
  intros s o. unfold intern. destruct (assoc (intern_key o) (ms_statics s)) as [[]|]; simpl; lia.
Qed.

Lemma intern_frames : forall s o, ms_frames (snd (intern s o)) = ms_frames s.
Proof. intros. unfold intern. destruct (assoc (intern_key o) (ms_statics s)) as [[]|]; reflexivity. Qed.

Lemma intern_inited : forall s o, ms_inited (snd (intern s o)) = ms_inited s.
Proof. intros. unfold intern. destruct (assoc (intern_key o) (ms_statics s)) as [[]|]; reflexivity. Qed.

Lemma intern_statics : forall s o k, k <> intern_key o ->
  assoc k (ms_statics (snd (intern s o))) = assoc k (ms_statics s).
Proof.
  intros s o k Hk. unfold intern. destruct (assoc (intern_key o) (ms_statics s)) as [[]|]; simpl; try reflexivity.
  all: destruct (String.eqb_spec k (intern_key o)); [contradiction | reflexivity].
Qed.

(** A virtual/interface call on an object of a class that is not loaded, answered by a model. *)
Lemma do_invoke_unloaded_model : forall s top rest k mr l more r nx cls fs v s',
  (k = InvVirtual \/ k = InvInterface) ->
  ms_heap s l = Some (OObj cls fs) ->
  resolve_full p cls (mr_name mr) (mr_desc mr) = None ->
  first_unloaded p 64 cls = cls ->
  mdl cls (mr_name mr) (mr_desc mr) (VRef l :: more) s = MOk v s' ->
  let st' := match v with Some w => w :: r | None => r end in
  (stack_slots st' <=? c_max_stack (cf_code top))%Z = true ->
  do_invoke 8 p mdl s top rest k mr (VRef l :: more) r nx =
    MNext (with_frames (with_frames s' (ms_frames s))
             (set_frame top (mkframe nx st' (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest k mr l more r nx cls fs v s' Hk Hh Hr Hu Hm st' Hb.
  assert (E : do_invoke 8 p mdl s top rest k mr (VRef l :: more) r nx =
              invoke_obj (fun k' impl args' => do_invoke 7 p mdl s top rest k' impl args' r nx)
                         p mdl s top rest k mr l more (ms_heap s l) r nx)
    by (destruct Hk as [-> | ->]; reflexivity).
  rewrite E, Hh. unfold invoke_obj.
  destruct Hk as [-> | ->]; rewrite Hr, Hu, Hm; unfold invoke_run_model; rewrite Hm;
  unfold invoke_frame_go; subst st'; rewrite Hb; reflexivity.
Qed.
End MoreSteps.

Section InternFacts.
Variable p : program.

Lemma err_key_ne : forall c u, ("#err:" ++ c)%string <> intern_key (OStr u).
Proof. intros c u H. cbn in H. discriminate H. Qed.

Lemma erroneous_intern : forall k s u c,
  erroneous p k (ms_statics (snd (intern s (OStr u)))) c = erroneous p k (ms_statics s) c.
Proof.
  induction k as [|k IH]; intros s u c; [reflexivity|]. cbn [erroneous].
  destruct (find_class p c) as [cf|]; [|reflexivity].
  rewrite intern_statics by apply err_key_ne.
  destruct (assoc ("#err:" ++ c) (ms_statics s)); [reflexivity|].
  destruct (cf_super cf); [apply IH | reflexivity].
Qed.
End InternFacts.

Section SpecialModel.
Variable p : program.
Variable mdl : model.

(** invokespecial of a JDK constructor (e.g. Object.<init>) answered by a model. *)
Lemma do_invoke_special_model : forall s top rest mr l more r nx o v s',
  ms_heap s l = Some o ->
  (match o with OLam _ _ _ _ _ => false | _ => true end) = true ->
  resolve_full p (mr_class mr) (mr_name mr) (mr_desc mr) = None ->
  first_unloaded p 64 (mr_class mr) = mr_class mr ->
  mdl (mr_class mr) (mr_name mr) (mr_desc mr) (VRef l :: more) s = MOk v s' ->
  let st' := match v with Some w => w :: r | None => r end in
  (stack_slots st' <=? c_max_stack (cf_code top))%Z = true ->
  do_invoke 8 p mdl s top rest InvSpecial mr (VRef l :: more) r nx =
    MNext (with_frames (with_frames s' (ms_frames s))
             (set_frame top (mkframe nx st' (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest mr l more r nx o v s' Hh Ho Hr Hu Hm st' Hb.
  assert (E : do_invoke 8 p mdl s top rest InvSpecial mr (VRef l :: more) r nx =
              invoke_obj (fun k' impl args' => do_invoke 7 p mdl s top rest k' impl args' r nx)
                         p mdl s top rest InvSpecial mr l more (ms_heap s l) r nx) by reflexivity.
  rewrite E, Hh. unfold invoke_obj. destruct o; try discriminate Ho;
  rewrite Hr, Hu, Hm; unfold invoke_run_model; rewrite Hm; unfold invoke_frame_go; subst st'; rewrite Hb; reflexivity.
Qed.
End SpecialModel.

Lemma returns_weaken : forall p mdl s v (P Q : mstate -> Prop),
  returns p mdl s v P -> (forall s', P s' -> Q s') -> returns p mdl s v Q.
Proof. intros p mdl s v P Q (k & s' & H1 & H2) HPQ. exists k, s'. auto. Qed.

Section ArraySteps.
Variable p : program.
Variable mdl : model.

Lemma mstep_anewarray : forall s top rest cn nx n r,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Anewarray cn, nx) ->
  f_stack (cf_frame top) = VInt n :: r ->
  (n <? 0)%Z = false -> (MAX_ARRAY <? n)%Z = false ->
  (stack_slots (VRef (ms_next s) :: r) <=? c_max_stack (cf_code top))%Z = true ->
  mstep_of p mdl s =
    MNext (with_frames (snd (alloc s (OArr (class_type cn) (repeat VNull (Z.to_nat n)))))
             (set_frame top (mkframe nx (VRef (ms_next s) :: r) (f_locals (cf_frame top))) :: rest)).
Proof.
  intros s top rest cn nx n r Hfr Hf Hst H1 H2 Hb.
  unfold mstep_of. rewrite Hfr, Hf. cbn [is_local_instr]. rewrite Hst, H1, H2. cbn [alloc fst snd].
  cbv beta iota zeta; cbn [f_stack f_pc f_locals]. rewrite Hb. reflexivity.
Qed.
End ArraySteps.

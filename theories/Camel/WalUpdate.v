(** * camel-wal TransactionLog.update, whole class, unbounded (fix e72996b974ad).

    The program is the real class files of the fix branch (TransactionLog,
    LayerInfo, EntryContainer, LogEntry, EntryState).  We prove a contract for
    [update(LayerInfo, EntryState)] over every heap that holds a log with any
    capacity and any number of adds (see [wal_inv]): for the LayerInfo that
    [add] returned for entry k, [update] sets the state of entry k and returns
    its container exactly when entry k is still in the ring buffer, and
    otherwise returns null and changes no object of the log. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic Tactics.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import WalSpec.
From JVM.Classes Require WalFixP.
Import ListNotations.
Open Scope Z_scope.

Definition wp : program :=
  ltac:(let x := eval vm_compute in (match load_program WalFixP.files with Some p => p | None => nil end) in exact x).

Definition TL := "org/apache/camel/component/wal/TransactionLog"%string.
Definition LI := "org/apache/camel/component/wal/TransactionLog$LayerInfo"%string.
Definition EC := "org/apache/camel/component/wal/TransactionLog$EntryContainer"%string.
Definition LE := "org/apache/camel/component/wal/LogEntry"%string.
Definition ES := "org/apache/camel/component/wal/LogEntry$EntryState"%string.

Definition no_code : code := {| c_max_stack := 0; c_max_locals := 0; c_length := 0; c_instrs := nil; c_handlers := nil |}.
Definition code_of (cls name desc : string) : code :=
  match resolve_full wp cls name desc with
  | Some (_, m) => match m_code m with Some c => c | None => no_code end
  | None => no_code
  end.

Definition gi_code := ltac:(let x := eval vm_compute in (code_of LI "getIndex" "()I") in exact x).
Definition gl_code := ltac:(let x := eval vm_compute in (code_of LI "getLayer" "()I") in exact x).
Definition ses_code := ltac:(let x := eval vm_compute in (code_of LE "setEntryState" "(Lorg/apache/camel/component/wal/LogEntry$EntryState;)V") in exact x).
Definition cu4_code := ltac:(let x := eval vm_compute in (code_of TL "canUpdate" "(IIII)Z") in exact x).
Definition cu_code := ltac:(let x := eval vm_compute in (code_of TL "canUpdate" "(Lorg/apache/camel/component/wal/TransactionLog$LayerInfo;)Z") in exact x).
Definition upd_code := ltac:(let x := eval vm_compute in (code_of TL "update" "(Lorg/apache/camel/component/wal/TransactionLog$LayerInfo;Lorg/apache/camel/component/wal/LogEntry$EntryState;)Lorg/apache/camel/component/wal/TransactionLog$EntryContainer;") in exact x).

Definition mk_m (name desc : string) (acc : Z) (c : code) : method :=
  {| m_name := name; m_desc := desc; m_access := acc; m_code := Some c |}.

Definition gi_m := mk_m "getIndex" "()I" 1 gi_code.
Definition gl_m := mk_m "getLayer" "()I" 1 gl_code.
Definition ses_m := mk_m "setEntryState" "(Lorg/apache/camel/component/wal/LogEntry$EntryState;)V" 1 ses_code.
Definition cu4_m := mk_m "canUpdate" "(IIII)Z" 8 cu4_code.
Definition upd_m := mk_m "update" "(Lorg/apache/camel/component/wal/TransactionLog$LayerInfo;Lorg/apache/camel/component/wal/LogEntry$EntryState;)Lorg/apache/camel/component/wal/TransactionLog$EntryContainer;" 1 upd_code.
Definition cu_m := mk_m "canUpdate" "(Lorg/apache/camel/component/wal/TransactionLog$LayerInfo;)Z" 2 cu_code.

Lemma rf_gi : resolve_full wp LI "getIndex" "()I" = Some (LI, gi_m). Proof. vm_compute. reflexivity. Qed.
Lemma rf_gl : resolve_full wp LI "getLayer" "()I" = Some (LI, gl_m). Proof. vm_compute. reflexivity. Qed.
Lemma rf_ses : resolve_full wp LE "setEntryState" "(Lorg/apache/camel/component/wal/LogEntry$EntryState;)V" = Some (LE, ses_m).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_cu4 : resolve_full wp TL "canUpdate" "(IIII)Z" = Some (TL, cu4_m). Proof. vm_compute. reflexivity. Qed.
Lemma rf_cu : resolve_full wp TL "canUpdate" "(Lorg/apache/camel/component/wal/TransactionLog$LayerInfo;)Z" = Some (TL, cu_m).
Proof. vm_compute. reflexivity. Qed.


Section Proofs.
Variable e : jenv.
Definition mdl := jdk_model wp e.

Ltac use_hyps :=
  repeat match goal with
  | H : ?a = ?b |- context [?a] => progress rewrite H
  end.

(** Normalise the machine state in the goal (keeps proof terms small). *)
Ltac nz := match goal with |- returns ?p ?m ?S ?v ?P =>
  let S1 := eval unfold with_frames, set_frame, set_resume in S in
  let S2 := eval cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames cf_class cf_method cf_code
                      cf_rt cf_frame cf_resume cf_clinit f_pc f_stack f_locals] in S1 in
  change (returns p m S2 v P) end.

Ltac lstep := eapply returns_step;
  [ eapply mstep_local; [ reflexivity | reflexivity | reflexivity
                        | cbn -[wrap i2c Z.mul iinc cat2]; use_hyps; cbn -[wrap i2c Z.mul iinc]; reflexivity
                        | cbn -[cat2]; use_hyps; reflexivity ]
  | try nz ].

Definition gi_mr : methodref := {| mr_class := LI; mr_name := "getIndex"; mr_desc := "()I"; mr_interface := false |}.

(** Calling LayerInfo.getIndex() on a LayerInfo object pushes its index. *)
Lemma call_getIndex : forall s top rest nx l r idx ly b v P,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvVirtual gi_mr, nx) ->
  f_stack (cf_frame top) = VRef l :: r ->
  ms_heap s l = Some (OObj LI [("index", VInt idx); ("layer", VInt ly); ("isRollingOver", b)]) ->
  (stack_slots (VInt idx :: r) <=? c_max_stack (cf_code top)) = true ->
  returns wp mdl (with_frames s (set_resume (set_frame top (mkframe nx (VInt idx :: r) (f_locals (cf_frame top)))) None :: rest)) v P ->
  returns wp mdl s v P.
Proof.
  intros s top rest nx l r idx ly b v P Hfr Hf Hst Hh Hb HR.
  eapply returns_step.
  { erewrite mstep_invoke; [ | exact Hfr | exact Hf | reflexivity | rewrite Hst; reflexivity ].
    cbn [app]. erewrite do_invoke_obj_enter; [ | left; reflexivity | exact Hh | exact rf_gi | reflexivity ].
    unfold enter. cbn. reflexivity. }
  lstep.
  eapply returns_step.
  { eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | cbn; exact Hh | reflexivity | reflexivity ]. }
  eapply returns_step.
  { eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ]. }
  exact HR.
Qed.

Definition gl_mr : methodref := {| mr_class := LI; mr_name := "getLayer"; mr_desc := "()I"; mr_interface := false |}.

Lemma call_getLayer : forall s top rest nx l r idx ly b v P,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvVirtual gl_mr, nx) ->
  f_stack (cf_frame top) = VRef l :: r ->
  ms_heap s l = Some (OObj LI [("index", VInt idx); ("layer", VInt ly); ("isRollingOver", b)]) ->
  (stack_slots (VInt ly :: r) <=? c_max_stack (cf_code top)) = true ->
  returns wp mdl (with_frames s (set_resume (set_frame top (mkframe nx (VInt ly :: r) (f_locals (cf_frame top)))) None :: rest)) v P ->
  returns wp mdl s v P.
Proof.
  intros s top rest nx l r idx ly b v P Hfr Hf Hst Hh Hb HR.
  eapply returns_step.
  { erewrite mstep_invoke; [ | exact Hfr | exact Hf | reflexivity | rewrite Hst; reflexivity ].
    cbn [app]. erewrite do_invoke_obj_enter; [ | left; reflexivity | exact Hh | exact rf_gl | reflexivity ].
    unfold enter. cbn. reflexivity. }
  lstep.
  eapply returns_step.
  { eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | cbn; exact Hh | reflexivity | reflexivity ]. }
  eapply returns_step.
  { eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ]. }
  exact HR.
Qed.

Definition ses_mr : methodref :=
  {| mr_class := LE; mr_name := "setEntryState"; mr_desc := "(Lorg/apache/camel/component/wal/LogEntry$EntryState;)V";
     mr_interface := false |}.

Definition le_fields (st km k vm vv : value) : list (string * value) :=
  [("entryState", st); ("keyMetadata", km); ("key", k); ("valueMetadata", vm); ("value", vv)].

Lemma call_setEntryState : forall s top rest nx le stv r st0 km k vm vv v P,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvVirtual ses_mr, nx) ->
  f_stack (cf_frame top) = stv :: VRef le :: r ->
  (match stv with VNull | VRef _ => true | _ => false end) = true ->
  ms_heap s le = Some (OObj LE (le_fields st0 km k vm vv)) ->
  returns wp mdl
    (with_frames {| ms_heap := upd (ms_heap s) le (OObj LE (le_fields stv km k vm vv)); ms_next := ms_next s;
                    ms_statics := ms_statics s; ms_inited := ms_inited s; ms_locks := ms_locks s;
                    ms_frames := ms_frames s |}
       (set_resume (set_frame top (mkframe nx r (f_locals (cf_frame top)))) None :: rest)) v P ->
  returns wp mdl s v P.
Proof.
  intros s top rest nx le stv r st0 km k vm vv v P Hfr Hf Hst Hv Hh HR.
  destruct stv; try discriminate Hv.
  all: eapply returns_step;
    [ erewrite mstep_invoke; [ | exact Hfr | exact Hf | reflexivity | rewrite Hst; reflexivity ];
      cbn [app]; erewrite do_invoke_obj_enter; [ | left; reflexivity | exact Hh | exact rf_ses | reflexivity ];
      unfold enter; cbn; reflexivity | ].
  all: lstep; lstep.
  all: eapply returns_step;
    [ eapply mstep_putfield; [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
                             | cbn; exact Hh | reflexivity | reflexivity ] | ].
  all: eapply returns_step;
    [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ] | ].
  all: exact HR.
Qed.

Definition cu4_mr : methodref := {| mr_class := TL; mr_name := "canUpdate"; mr_desc := "(IIII)Z"; mr_interface := false |}.

(** The value the fix's canUpdate(IIII)Z returns. *)
Definition cu4_val (a b c d : Z) : Z :=
  if (a =? c) && (d <=? b) then 1 else if (a =? wrap 32 (c + 1)) && (b <=? d) then 1 else 0.

Lemma call_cu4 : forall s top rest nx a b c d r v P,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvStatic cu4_mr, nx) ->
  f_stack (cf_frame top) = VInt d :: VInt c :: VInt b :: VInt a :: r ->
  erroneous wp 64 (ms_statics s) TL = false ->
  init_needed wp 64 (ms_inited s) TL = None ->
  (stack_slots (VInt (cu4_val a b c d) :: r) <=? c_max_stack (cf_code top)) = true ->
  returns wp mdl (with_frames s (set_resume (set_frame top (mkframe nx (VInt (cu4_val a b c d) :: r) (f_locals (cf_frame top)))) None :: rest)) v P ->
  returns wp mdl s v P.
Proof.
  intros s top rest nx a b c d r v P Hfr Hf Hst He Hi Hb HR.
  eapply returns_step.
  { erewrite mstep_invoke; [ | exact Hfr | exact Hf | reflexivity | rewrite Hst; reflexivity ].
    cbn [app]. erewrite do_invoke_static_enter; [ | exact He | exact Hi | exact rf_cu4 | reflexivity ].
    unfold enter. cbn. reflexivity. }
  lstep. lstep.
  destruct (a =? c) eqn:E1.
  - lstep. lstep. lstep.
    destruct (b <? d) eqn:E2.
    + lstep. lstep. lstep. lstep. lstep.
      destruct (a =? wrap 32 (c + 1)) eqn:E3.
      * lstep. lstep. lstep.
        destruct (d <? b) eqn:E4.
        -- exfalso. apply Z.ltb_lt in E2; apply Z.ltb_lt in E4; lia.
        -- lstep. lstep. eapply returns_step; [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ] | ].
           unfold cu4_val in HR. rewrite E1, E3 in HR.
           replace (d <=? b) with false in HR by (symmetry; apply Z.leb_gt; apply Z.ltb_lt in E2; lia).
           replace (b <=? d) with true in HR by (symmetry; apply Z.leb_le; apply Z.ltb_lt in E2; lia).
           exact HR.
      * lstep. lstep. eapply returns_step; [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ] | ].
        unfold cu4_val in HR. rewrite E1, E3 in HR.
        replace (d <=? b) with false in HR by (symmetry; apply Z.leb_gt; apply Z.ltb_lt in E2; lia).
        exact HR.
    + lstep. lstep. eapply returns_step; [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ] | ].
      unfold cu4_val in HR. rewrite E1 in HR.
      replace (d <=? b) with true in HR by (symmetry; apply Z.leb_le; apply Z.ltb_ge in E2; lia).
      exact HR.
  - lstep. lstep. lstep. lstep. lstep.
    destruct (a =? wrap 32 (c + 1)) eqn:E3.
    + lstep. lstep. lstep.
      destruct (d <? b) eqn:E4.
      * lstep. lstep. eapply returns_step; [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ] | ].
        unfold cu4_val in HR. rewrite E1, E3 in HR.
        replace (b <=? d) with false in HR by (symmetry; apply Z.leb_gt; apply Z.ltb_lt in E4; lia).
        exact HR.
      * lstep. lstep. eapply returns_step; [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ] | ].
        unfold cu4_val in HR. rewrite E1, E3 in HR.
        replace (b <=? d) with true in HR by (symmetry; apply Z.leb_le; apply Z.ltb_ge in E4; lia).
        exact HR.
    + lstep. lstep. eapply returns_step; [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ] | ].
      unfold cu4_val in HR. rewrite E1, E3 in HR. exact HR.
Qed.

Definition cu_mr : methodref :=
  {| mr_class := TL; mr_name := "canUpdate"; mr_desc := "(Lorg/apache/camel/component/wal/TransactionLog$LayerInfo;)Z";
     mr_interface := false |}.

Definition tl_fields (cap arr cI cL : Z) : list (string * value) :=
  [("maxCapacity", VInt cap); ("logEntries", VRef arr); ("currentIndex", VInt cI); ("currentLayer", VInt cL)].
Definition li_fields (idx ly : Z) (b : value) : list (string * value) :=
  [("index", VInt idx); ("layer", VInt ly); ("isRollingOver", b)].

Lemma cu4_val_bool : forall a b c d, Z.land (cu4_val a b c d) 1 = cu4_val a b c d.
Proof. intros. unfold cu4_val. destruct ((a =? c) && (d <=? b)); [reflexivity|]. destruct (_ && _); reflexivity. Qed.

Ltac RET := eapply returns_step;
  [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ] | ].

Lemma call_cuLI : forall s top rest nx t li r cap arr cI cL eI eL b v P,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvVirtual cu_mr, nx) ->
  f_stack (cf_frame top) = VRef li :: VRef t :: r ->
  ms_heap s t = Some (OObj TL (tl_fields cap arr cI cL)) ->
  ms_heap s li = Some (OObj LI (li_fields eI eL b)) ->
  erroneous wp 64 (ms_statics s) TL = false ->
  init_needed wp 64 (ms_inited s) TL = None ->
  (stack_slots (VInt (cu4_val cL cI eL eI) :: r) <=? c_max_stack (cf_code top)) = true ->
  returns wp mdl (with_frames s (set_resume (set_frame top
      (mkframe nx (VInt (cu4_val cL cI eL eI) :: r) (f_locals (cf_frame top)))) None :: rest)) v P ->
  returns wp mdl s v P.
Proof.
  intros s top rest nx t li r cap arr cI cL eI eL b v P Hfr Hf Hst Ht Hli He Hi Hb HR.
  eapply returns_step.
  { erewrite mstep_invoke; [ | exact Hfr | exact Hf | reflexivity | rewrite Hst; reflexivity ].
    cbn [app]. erewrite do_invoke_obj_enter; [ | left; reflexivity | exact Ht | exact rf_cu | reflexivity ].
    unfold enter. cbn. reflexivity. }
  lstep.
  eapply returns_step.
  { eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | cbn; exact Ht | reflexivity | reflexivity ]. }
  lstep.
  eapply returns_step.
  { eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | cbn; exact Ht | reflexivity | reflexivity ]. }
  lstep.
  eapply call_getLayer; [ reflexivity | reflexivity | reflexivity | cbn; exact Hli | reflexivity | ].
  lstep.
  eapply call_getIndex; [ reflexivity | reflexivity | reflexivity | cbn; exact Hli | reflexivity | ].
  eapply call_cu4; [ reflexivity | reflexivity | reflexivity | cbn; exact He | cbn; exact Hi | reflexivity | ].
  RET.
  cbn [narrow_ret]. rewrite cu4_val_bool. exact HR.
Qed.

Definition LOGK := "org/apache/camel/component/wal/TransactionLog.LOG"%string.
Definition LOGC := "org/slf4j/Logger"%string.

Definition FAILEDK := "org/apache/camel/component/wal/LogEntry$EntryState.FAILED"%string.

Lemma failed_ne : forall u, FAILEDK <> intern_key (OStr u).
Proof. intros u E. unfold FAILEDK, intern_key in E. discriminate E. Qed.
Lemma log_ne : forall u, LOGK <> intern_key (OStr u).
Proof. intros u E. unfold LOGK, intern_key in E. discriminate E. Qed.

(** What a call leaves unchanged besides the heap: no address is reused, no class is
    (de)initialised, the logger and FAILED constants stay. *)
Definition env_same (s0 s' : mstate) : Prop :=
  ms_next s0 <= ms_next s' /\ ms_inited s' = ms_inited s0 /\
  (forall c, erroneous wp 64 (ms_statics s') c = erroneous wp 64 (ms_statics s0) c) /\
  assoc LOGK (ms_statics s') = assoc LOGK (ms_statics s0) /\
  assoc FAILEDK (ms_statics s') = assoc FAILEDK (ms_statics s0).

Lemma env_same_proj : forall s s', ms_next s <= ms_next s' -> ms_inited s' = ms_inited s ->
  ms_statics s' = ms_statics s -> env_same s s'.
Proof.
  intros s s' H1 H2 H3. unfold env_same. rewrite H2, H3.
  refine (conj H1 (conj eq_refl (conj (fun c => eq_refl) (conj eq_refl eq_refl)))).
Qed.

Lemma env_same_intern : forall s s' u, ms_next s' = ms_next (snd (intern s (OStr u))) ->
  ms_inited s' = ms_inited (snd (intern s (OStr u))) -> ms_statics s' = ms_statics (snd (intern s (OStr u))) ->
  env_same s s'.
Proof.
  intros s s' u H1 H2 H3. unfold env_same. rewrite H1, H2, H3.
  refine (conj (intern_next s _) (conj (intern_inited s _) (conj (fun c => erroneous_intern wp 64 s u c)
    (conj (intern_statics s _ _ (log_ne u)) (intern_statics s _ _ (failed_ne u)))))).
Qed.

Lemma env_same_intern' : forall s0 s s' u,
  ms_next s = ms_next s0 -> ms_inited s = ms_inited s0 -> ms_statics s = ms_statics s0 ->
  ms_next s' = ms_next (snd (intern s (OStr u))) ->
  ms_inited s' = ms_inited (snd (intern s (OStr u))) -> ms_statics s' = ms_statics (snd (intern s (OStr u))) ->
  env_same s0 s'.
Proof.
  intros s0 s s' u A1 A2 A3 H1 H2 H3. pose proof (env_same_intern s s' u H1 H2 H3) as (B1 & B2 & B3 & B4 & B5).
  unfold env_same. rewrite <- A1, <- A2, <- A3. exact (conj B1 (conj B2 (conj B3 (conj B4 B5)))).
Qed.

Ltac env_intern := match goal with |- env_same ?s0 ?s' =>
  match s' with context [intern ?X (OStr ?u)] =>
    apply (env_same_intern' s0 X s' u); reflexivity end end.

Lemma env_same_trans : forall a b c, env_same a b -> env_same b c -> env_same a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5) (B1 & B2 & B3 & B4 & B5). unfold env_same.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - lia.
  - rewrite B2. exact A2.
  - intros x. rewrite B3. apply A3.
  - rewrite B4. exact A4.
  - rewrite B5. exact A5.
Qed.

Lemma rf_debug : resolve_full wp LOGC "debug" "(Ljava/lang/String;Ljava/lang/Object;)V" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_warn : resolve_full wp LOGC "warn" "(Ljava/lang/String;)V" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_isdebug : resolve_full wp LOGC "isDebugEnabled" "()Z" = None. Proof. vm_compute. reflexivity. Qed.
Lemma fu_log : first_unloaded wp 64 LOGC = LOGC. Proof. vm_compute. reflexivity. Qed.

Lemma m_debug : forall args s, jdk_model wp e LOGC "debug" "(Ljava/lang/String;Ljava/lang/Object;)V" args s = MOk None s.
Proof. intros. unfold jdk_model. cbv -[j_log_enabled]. reflexivity. Qed.
Lemma m_warn : forall args s, jdk_model wp e LOGC "warn" "(Ljava/lang/String;)V" args s = MOk None s.
Proof. intros. unfold jdk_model. cbv -[j_log_enabled]. reflexivity. Qed.
Lemma m_isdebug : forall args s, jdk_model wp e LOGC "isDebugEnabled" "()Z" args s =
  MOk (Some (VInt (if j_log_enabled e "isDebugEnabled" then 1 else 0))) s.
Proof. intros. unfold jdk_model. cbv -[j_log_enabled]. reflexivity. Qed.

Definition upd_frame (t li : Z) (stv : value) : cframe :=
  {| cf_class := TL; cf_method := upd_m; cf_code := upd_code; cf_rt := Some (TRef EC);
     cf_frame := mkframe 0 nil [VRef t; VRef li; stv; VTop]; cf_resume := None; cf_clinit := false |}.

Definition ec_fields (li le : value) (pos : value) : list (string * value) :=
  [("layerInfo", li); ("logEntry", le); ("position", pos)].

(** A model call on the logger (no effect, nothing pushed). *)
Ltac log_call ml rf :=
  eapply returns_step;
  [ erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ];
    cbn [app];
    erewrite do_invoke_unloaded_model;
    [ | right; reflexivity | cbn; rewrite ?intern_old by lia; eassumption | exact rf | exact fu_log
      | unfold mdl; apply ml | reflexivity ]; reflexivity
  | ].

Theorem update_live : forall s0 t li stv cap arr cI cL eI eL b lg es c x pos le st0 km k vm vv,
  ms_frames s0 = [upd_frame t li stv] ->
  ms_heap s0 t = Some (OObj TL (tl_fields cap arr cI cL)) ->
  ms_heap s0 li = Some (OObj LI (li_fields eI eL b)) ->
  (match stv with VNull | VRef _ => true | _ => false end) = true ->
  erroneous wp 64 (ms_statics s0) TL = false ->
  init_needed wp 64 (ms_inited s0) TL = None ->
  assoc LOGK (ms_statics s0) = Some (VRef lg) ->
  ms_heap s0 lg = Some (OObj LOGC nil) ->
  cu4_val cL cI eL eI = 1 ->
  ms_heap s0 arr = Some (OArr (TRef EC) es) ->
  0 <= eI < Z.of_nat (length es) ->
  nth_z es eI = Some (VRef c) ->
  ms_heap s0 c = Some (OObj EC (ec_fields x (VRef le) pos)) ->
  ms_heap s0 le = Some (OObj LE (le_fields st0 km k vm vv)) ->
  t < ms_next s0 -> li < ms_next s0 -> lg < ms_next s0 -> arr < ms_next s0 -> c < ms_next s0 -> le < ms_next s0 ->
  returns wp mdl s0 (Some (VRef c))
    (fun s' => ms_heap s' le = Some (OObj LE (le_fields stv km k vm vv)) /\
               (forall y, y < ms_next s0 -> y <> le -> ms_heap s' y = ms_heap s0 y) /\ env_same s0 s').
Proof.
  intros s0 t li stv cap arr cI cL eI eL b lg es c x pos le st0 km k vm vv
         Hfr Ht Hli Hstv He Hi HLOG Hlg Hcu Harr HeI Hes Hc Hle Ht' Hli' Hlg' Harr' Hc' Hle'.
  destruct s0 as [h0 n0 sts0 ini0 lk0 fs0];
  cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames] in *.
  subst fs0.
  assert (Hc2 : cat2 stv = false) by (destruct stv; try discriminate Hstv; reflexivity).
  assert (Hs2 : slots stv = 1) by (destruct stv; try discriminate Hstv; reflexivity).
  lstep.
  lstep.
  lstep. lstep.
  eapply call_cuLI; [ reflexivity | reflexivity | reflexivity | cbn; exact Ht | cbn; exact Hli
                    | cbn; exact He | cbn; exact Hi | reflexivity | ].
  rewrite Hcu.
  lstep.
  (* 31: getstatic LOG *)
  eapply returns_step.
  { eapply mstep_getstatic; [ reflexivity | reflexivity | cbn; exact He | cbn; exact Hi | cbn; exact HLOG | reflexivity ]. }
  (* 34: ldc "Updating record with layer: {}" -- interned, maybe allocated *)
  eapply returns_step.
  { eapply mstep_ldc_string; [ reflexivity | reflexivity | reflexivity | ].
    destruct (intern _ _); reflexivity. }
  match goal with |- context [intern ?X ?o] => remember (intern X o) as I eqn:HI end.
  assert (Hold : forall y, y < n0 -> ms_heap (snd I) y = h0 y).
  { intros y Hy. subst I. rewrite intern_old; cbn; [reflexivity | lia]. }
  lstep.
  (* 37: LOG.debug(String, Object) *)
  eapply returns_step.
  { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
    erewrite do_invoke_unloaded_model;
      [ reflexivity | right; reflexivity | cbn; rewrite Hold by lia; exact Hlg | exact rf_debug | exact fu_log
      | unfold mdl; apply m_debug | reflexivity ]. }
  (* 42: aload_0; getfield logEntries *)
  lstep.
  eapply returns_step.
  { eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | cbn; rewrite Hold by lia; exact Ht
                           | reflexivity | reflexivity ]. }
  (* 46: aload_1; invokevirtual getIndex *)
  lstep.
  eapply call_getIndex; [ reflexivity | reflexivity | reflexivity | cbn; rewrite Hold by lia; exact Hli | reflexivity | ].
  (* 50: aaload *)
  eapply returns_step.
  { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | cbn; rewrite Hold by lia; exact Harr
                         | reflexivity | | exact Hes | reflexivity ].
    apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia. }
  (* 51: astore_3; aload_3; getfield logEntry *)
  lstep. lstep.
  eapply returns_step.
  { eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | cbn; rewrite Hold by lia; exact Hc
                           | reflexivity | reflexivity ]. }
  (* 56: aload_2; invokevirtual setEntryState *)
  lstep.
  eapply call_setEntryState; [ reflexivity | reflexivity | reflexivity | exact Hstv | cbn; rewrite Hold by lia; exact Hle | ].
  (* 60: aload_3; areturn *)
  lstep.
  eapply returns_now.
  { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
  cbn [with_frames ms_heap ms_next]. split; [|split].
  - apply upd_same.
  - intros y Hy Hne. rewrite upd_other by exact Hne. apply Hold. exact Hy.
  - subst I. env_intern.
Qed.



(** The tail of [update] from pc 84 (after the record was found rolled over):
    compare the state with FAILED, maybe log a warning, return null. *)
Lemma from84 : forall S t li stv h0 n0 lg vf,
  ms_frames S = [set_frame (upd_frame t li stv) (mkframe 84 nil [VRef t; VRef li; stv; VTop])] ->
  (match stv with VNull | VRef _ => true | _ => false end) = true ->
  (match vf with VNull | VRef _ => true | _ => false end) = true ->
  (forall y, y < n0 -> ms_heap S y = h0 y) ->
  n0 <= ms_next S ->
  erroneous wp 64 (ms_statics S) ES = false ->
  init_needed wp 64 (ms_inited S) ES = None ->
  assoc FAILEDK (ms_statics S) = Some vf ->
  assoc LOGK (ms_statics S) = Some (VRef lg) ->
  erroneous wp 64 (ms_statics S) TL = false ->
  init_needed wp 64 (ms_inited S) TL = None ->
  h0 lg = Some (OObj LOGC nil) -> lg < n0 ->
  returns wp mdl S (Some VNull) (fun s' => (forall y, y < n0 -> ms_heap s' y = h0 y) /\ env_same S s').
Proof.
  intros S t li stv h0 n0 lg vf Hfr Hstv Hvf Hold Hn He Hi HF HLOG He' Hi' Hlg Hlg'.
  assert (Hc2 : cat2 stv = false) by (destruct stv; try discriminate Hstv; reflexivity).
  assert (Hs2 : slots stv = 1) by (destruct stv; try discriminate Hstv; reflexivity).
  assert (Hs3 : slots vf = 1) by (destruct vf; try discriminate Hvf; reflexivity).
  assert (Hr1 : is_ref stv = true) by (destruct stv; try discriminate Hstv; reflexivity).
  assert (Hr2 : is_ref vf = true) by (destruct vf; try discriminate Hvf; reflexivity).
  destruct S as [h n sts ini lk fs]; cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames] in *. subst fs.
  lstep.
  eapply returns_step.
  { eapply mstep_getstatic; [ reflexivity | reflexivity | exact He | exact Hi | exact HF | cbn -[cat2 slots]; use_hyps; reflexivity ]. }
  destruct (ref_eq stv vf) eqn:Eq.
  - (* the state is FAILED: warn *)
    lstep.
    eapply returns_step.
    { eapply mstep_getstatic; [ reflexivity | reflexivity | exact He' | exact Hi' | exact HLOG | reflexivity ]. }
    eapply returns_step.
    { eapply mstep_ldc_string; [ reflexivity | reflexivity | reflexivity | ].
      destruct (intern _ _); reflexivity. }
    match goal with |- context [intern ?X ?o] => remember (intern X o) as I eqn:HI end.
    assert (Hold' : forall y, y < n0 -> ms_heap (snd I) y = h0 y).
    { intros y Hy. subst I. rewrite intern_old; cbn; [apply Hold; exact Hy | lia]. }
    eapply returns_step.
    { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
      erewrite do_invoke_unloaded_model;
        [ reflexivity | right; reflexivity | cbn; rewrite Hold' by lia; exact Hlg | exact rf_warn | exact fu_log
        | unfold mdl; apply m_warn | reflexivity ]. }
    lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
    cbn [with_frames ms_heap]. split; [exact Hold' | subst I; env_intern].
  - lstep.
    lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
    cbn [with_frames ms_heap]. split; [exact Hold | apply env_same_proj; cbn; [lia | reflexivity | reflexivity]].
Qed.

Theorem update_dead : forall s0 t li stv cap arr cI cL eI eL b lg vf,
  ms_frames s0 = [upd_frame t li stv] ->
  ms_heap s0 t = Some (OObj TL (tl_fields cap arr cI cL)) ->
  ms_heap s0 li = Some (OObj LI (li_fields eI eL b)) ->
  (match stv with VNull | VRef _ => true | _ => false end) = true ->
  (match vf with VNull | VRef _ => true | _ => false end) = true ->
  erroneous wp 64 (ms_statics s0) TL = false ->
  init_needed wp 64 (ms_inited s0) TL = None ->
  erroneous wp 64 (ms_statics s0) ES = false ->
  init_needed wp 64 (ms_inited s0) ES = None ->
  assoc LOGK (ms_statics s0) = Some (VRef lg) ->
  assoc FAILEDK (ms_statics s0) = Some vf ->
  ms_heap s0 lg = Some (OObj LOGC nil) ->
  cu4_val cL cI eL eI = 0 ->
  t < ms_next s0 -> li < ms_next s0 -> lg < ms_next s0 ->
  returns wp mdl s0 (Some VNull)
    (fun s' => (forall y, y < ms_next s0 -> ms_heap s' y = ms_heap s0 y) /\ env_same s0 s').
Proof.
  intros s0 t li stv cap arr cI cL eI eL b lg vf Hfr Ht Hli Hstv Hvf He Hi He2 Hi2 HLOG HF Hlg Hcu Ht' Hli' Hlg'.
  destruct s0 as [h0 n0 sts0 ini0 lk0 fs0];
  cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames] in *.
  subst fs0.
  assert (Hc2 : cat2 stv = false) by (destruct stv; try discriminate Hstv; reflexivity).
  assert (Hs2 : slots stv = 1) by (destruct stv; try discriminate Hstv; reflexivity).
  lstep. lstep. lstep. lstep.
  eapply call_cuLI; [ reflexivity | reflexivity | reflexivity | cbn; exact Ht | cbn; exact Hli
                    | cbn; exact He | cbn; exact Hi | reflexivity | ].
  rewrite Hcu.
  lstep.
  eapply returns_step.
  { eapply mstep_getstatic; [ reflexivity | reflexivity | cbn; exact He | cbn; exact Hi | cbn; exact HLOG | reflexivity ]. }
  eapply returns_step.
  { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
    erewrite do_invoke_unloaded_model;
      [ reflexivity | right; reflexivity | cbn; exact Hlg | exact rf_isdebug | exact fu_log
      | unfold mdl; apply m_isdebug | reflexivity ]. }
  destruct (j_log_enabled e "isDebugEnabled") eqn:Ed.
  - (* debug enabled: log the discarded record *)
    lstep.
    eapply returns_step.
    { eapply mstep_getstatic; [ reflexivity | reflexivity | cbn; exact He | cbn; exact Hi | cbn; exact HLOG | reflexivity ]. }
    eapply returns_step.
    { eapply mstep_ldc_string; [ reflexivity | reflexivity | reflexivity | ].
      destruct (intern _ _); reflexivity. }
    match goal with |- context [intern ?X ?o] => remember (intern X o) as I eqn:HI end.
    lstep.
    eapply returns_step.
    { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
      erewrite do_invoke_unloaded_model;
        [ reflexivity | right; reflexivity | cbn; subst I; rewrite intern_old by (cbn; lia); exact Hlg
        | exact rf_debug | exact fu_log | unfold mdl; apply m_debug | reflexivity ]. }
    eapply returns_weaken.
    { eapply (from84 _ t li stv h0 n0 lg vf); [ reflexivity | exact Hstv | exact Hvf | | | | | | | | | exact Hlg | exact Hlg' ];
        cbn [with_frames ms_heap ms_next ms_statics ms_inited]; subst I.
      + intros y Hy. rewrite intern_old by (cbn; lia). reflexivity.
      + eapply Z.le_trans; [ | apply intern_next ]. cbn. lia.
      + rewrite erroneous_intern. exact He2.
      + rewrite intern_inited. exact Hi2.
      + rewrite intern_statics by apply failed_ne. exact HF.
      + rewrite intern_statics by apply log_ne. exact HLOG.
      + rewrite erroneous_intern. exact He.
      + rewrite intern_inited. exact Hi. }
    intros s' [H1 H2]. split; [exact H1|]. eapply env_same_trans; [ | exact H2 ].
    subst I. env_intern.
  - (* debug disabled *)
    lstep.
    eapply returns_weaken.
    { eapply (from84 _ t li stv h0 n0 lg vf); [ reflexivity | exact Hstv | exact Hvf | intros y Hy; reflexivity
      | cbn; lia | exact He2 | exact Hi2 | exact HF | exact HLOG | exact He | exact Hi | exact Hlg | exact Hlg' ]. }
    intros s' [H1 H2]. split; [exact H1|]. eapply env_same_trans; [ | exact H2 ].
    apply env_same_proj; [apply Z.le_refl | reflexivity | reflexivity].
Qed.

End Proofs.

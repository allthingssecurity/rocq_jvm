(** * camel-wal TransactionLog.add (fix e72996b974ad), whole bytecode, unbounded.

    For any heap holding a TransactionLog [t] of capacity [cap] whose array
    [arr] has [cap] slots, [add(le)] allocates a LayerInfo and an
    EntryContainer, stores the container in slot [cI'] and returns it, where
    (cI', cL') = (0, cL + 1) if the current index reached the capacity (a
    roll-over) and (cI, cL) otherwise; afterwards currentIndex = cI' + 1 and
    currentLayer = cL'.  Together with [WalUpdateSpec.update_contract] this
    gives the whole-class behaviour for every sequence of operations
    (see [WalRing.v]). *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic Tactics.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import WalSpec WalUpdate.
Import ListNotations.
Open Scope Z_scope.

Definition add_desc := "(Lorg/apache/camel/component/wal/LogEntry;)Lorg/apache/camel/component/wal/TransactionLog$EntryContainer;"%string.
Definition li_init_desc := "(IIZ)V"%string.
Definition ec_init_desc := "(Lorg/apache/camel/component/wal/TransactionLog$LayerInfo;Lorg/apache/camel/component/wal/LogEntry;)V"%string.

Definition add_code := ltac:(let x := eval vm_compute in (code_of TL "add" add_desc) in exact x).
Definition li_init_code := ltac:(let x := eval vm_compute in (code_of LI "<init>" li_init_desc) in exact x).
Definition ec_init_code := ltac:(let x := eval vm_compute in (code_of EC "<init>" ec_init_desc) in exact x).
Definition add_m := mk_m "add" add_desc 1 add_code.
Definition li_init_m := mk_m "<init>" li_init_desc 1 li_init_code.
Definition ec_init_m := mk_m "<init>" ec_init_desc 1 ec_init_code.

Lemma rf_li_init : resolve_full wp LI "<init>" li_init_desc = Some (LI, li_init_m). Proof. vm_compute. reflexivity. Qed.
Lemma rf_ec_init : resolve_full wp EC "<init>" ec_init_desc = Some (EC, ec_init_m). Proof. vm_compute. reflexivity. Qed.
Lemma rf_obj_init : resolve_full wp "java/lang/Object" "<init>" "()V" = None. Proof. vm_compute. reflexivity. Qed.
Lemma fu_obj : first_unloaded wp 64 "java/lang/Object" = "java/lang/Object". Proof. vm_compute. reflexivity. Qed.
Lemma if_li : instance_fields wp 64 LI = Some (li_fields 0 0 (VInt 0)). Proof. vm_compute. reflexivity. Qed.
Lemma if_ec : instance_fields wp 64 EC = Some (ec_fields VNull VNull (VLong 0)). Proof. vm_compute. reflexivity. Qed.
Definition tl_init_desc := "(I)V"%string.
Definition tl_init_code := ltac:(let x := eval vm_compute in (code_of TL "<init>" tl_init_desc) in exact x).
Definition tl_init_m := mk_m "<init>" tl_init_desc 1 tl_init_code.
Definition tl_default : list (string * value) :=
  ltac:(let x := eval vm_compute in (match instance_fields wp 64 TL with Some f => f | None => nil end) in exact x).
Lemma if_tl : instance_fields wp 64 TL = Some tl_default. Proof. vm_compute. reflexivity. Qed.
Lemma ct_ec : class_type EC = TRef EC. Proof. reflexivity. Qed.

Lemma asg_ec : assignable wp 64 (TRef EC) EC = Some true. Proof. vm_compute. reflexivity. Qed.

Definition add_frame (t le : Z) : cframe :=
  {| cf_class := TL; cf_method := add_m; cf_code := add_code; cf_rt := Some (TRef EC);
     cf_frame := mkframe 0 nil [VRef t; VRef le; VTop; VTop]; cf_resume := None; cf_clinit := false |}.

Section Add.
Variable e : jenv.

Lemma m_obj_init : forall args s, jdk_model wp e "java/lang/Object" "<init>" "()V" args s = MOk None s.
Proof. intros. unfold jdk_model. cbv -[j_log_enabled]. reflexivity. Qed.

Ltac use_hyps :=
  repeat match goal with
  | H : ?a = ?b |- context [?a] => progress rewrite H
  end.

Ltac nz := match goal with |- returns ?p ?m ?S ?v ?P =>
  let S1 := eval unfold with_frames, set_frame, set_resume, alloc in S in
  let S2 := eval cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames cf_class cf_method cf_code
                      cf_rt cf_frame cf_resume cf_clinit f_pc f_stack f_locals fst snd narrow_store] in S1 in
  change (returns p m S2 v P) end.

Ltac lstep := eapply returns_step;
  [ eapply mstep_local; [ reflexivity | reflexivity | reflexivity
                        | cbn -[wrap i2c Z.mul iinc cat2 upd]; use_hyps; cbn -[wrap i2c Z.mul iinc upd]; reflexivity
                        | cbn -[cat2 upd]; use_hyps; reflexivity ]
  | try nz ].

(** heap lookups through a chain of updates *)
Ltac hp := cbn [ms_heap ms_statics ms_inited];
  repeat first [ rewrite upd_same | rewrite upd_other by lia ];
  first [ eassumption | reflexivity ].

Ltac GET := eapply returns_step;
  [ eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | reflexivity ] | try nz ].
Ltac PUT := eapply returns_step;
  [ eapply mstep_putfield; [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | hp
                           | reflexivity | reflexivity ] | try nz ].
Ltac NEW F := eapply returns_step;
  [ eapply mstep_new; [ reflexivity | reflexivity | cbn [ms_statics]; eassumption | cbn [ms_inited]; eassumption
                      | exact F | reflexivity ] | try nz ].
Ltac RET := eapply returns_step;
  [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ]
  | try nz ].
Ltac SPECIAL RF := eapply returns_step;
  [ erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]; cbn [app];
    erewrite do_invoke_special_enter; [ | hp | reflexivity | exact RF | reflexivity ];
    unfold enter; cbn -[upd]; reflexivity
  | try nz ].
(** Object.<init> through invokespecial: answered by the model, no effect. *)
Ltac OBJINIT := eapply returns_step;
  [ erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]; cbn [app];
    erewrite do_invoke_special_model;
    [ reflexivity | hp | reflexivity | exact rf_obj_init | exact fu_obj
    | unfold mdl; apply m_obj_init | reflexivity ]
  | try nz ].

Definition add_post (S : mstate) (t le cap arr cI cL rb : Z) (es : list value) (s' : mstate) : Prop :=
  let n := ms_next S in
  ms_heap s' t = Some (OObj TL (tl_fields cap arr (cI + 1) cL)) /\
  ms_heap s' arr = Some (OArr (TRef EC) (set_nth_z es cI (VRef n))) /\
  ms_heap s' n = Some (OObj EC (ec_fields (VRef (n + 1)) (VRef le) (VLong (-1)))) /\
  ms_heap s' (n + 1) = Some (OObj LI (li_fields cI cL (VInt rb))) /\
  ms_next s' = n + 2 /\ ms_statics s' = ms_statics S /\ ms_inited s' = ms_inited S /\
  (forall y, y < n -> y <> t -> y <> arr -> ms_heap s' y = ms_heap S y).

(** The common tail of [add] from pc 30 (after the roll-over check). *)
Lemma add_from30 : forall S t le cap arr cI cL rb es,
  ms_frames S = [set_frame (add_frame t le) (mkframe 30 nil [VRef t; VRef le; VInt rb; VTop])] ->
  ms_heap S t = Some (OObj TL (tl_fields cap arr cI cL)) ->
  ms_heap S arr = Some (OArr (TRef EC) es) ->
  0 <= cI < Z.of_nat (length es) -> cI + 1 <= INT_MAX -> Z.land rb 1 = rb ->
  t < ms_next S -> arr < ms_next S -> t <> arr ->
  erroneous wp 64 (ms_statics S) EC = false -> init_needed wp 64 (ms_inited S) EC = None ->
  erroneous wp 64 (ms_statics S) LI = false -> init_needed wp 64 (ms_inited S) LI = None ->
  returns wp (mdl e) S (Some (VRef (ms_next S))) (add_post S t le cap arr cI cL rb es).
Proof.
  intros S t le cap arr cI cL rb es Hfr Ht Ha HcI Hmax Hrb Ht' Ha' Hta He1 Hi1 He2 Hi2.
  destruct S as [h n sts ini lk fs]; cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames] in *. subst fs.
  unfold add_post; cbn [ms_heap ms_next ms_statics ms_inited].
  (* 30: new EC; dup; new LI; dup *)
  NEW if_ec. lstep. NEW if_li. lstep.
  (* aload_0 getfield currentIndex aload_0 getfield currentLayer iload_2 *)
  lstep. GET. lstep. GET. lstep.
  (* 47: invokespecial LayerInfo.<init>(IIZ) *)
  SPECIAL rf_li_init.
  lstep. OBJINIT.
  lstep. lstep. PUT. lstep. lstep. PUT. lstep. lstep. PUT.
  RET.
  (* 50: aload_1; invokespecial EntryContainer.<init>(LayerInfo, LogEntry) *)
  lstep. SPECIAL rf_ec_init.
  lstep. OBJINIT.
  lstep. lstep. PUT. lstep. lstep. PUT. lstep. lstep. PUT.
  RET.
  (* 54: astore_3; aload_0 getfield logEntries; aload_0 getfield currentIndex; aload_3; aastore *)
  lstep. lstep. GET. lstep. GET. lstep.
  eapply returns_step.
  { eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | | hp
                              | reflexivity | exact asg_ec | reflexivity ].
    apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia. }
  nz.
  (* 65: currentIndex++ *)
  lstep. lstep. GET. lstep. lstep. PUT.
  (* 75: aload_3; areturn *)
  lstep.
  eapply returns_now.
  { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
  assert (Hw : wrap 32 (cI + 1) = cI + 1) by (apply wrap_id; [lia | unfold in_range, INT_MAX in *; cbn; lia]).
  cbn [with_frames ms_heap ms_next ms_statics ms_inited]. rewrite Hw, Hrb.
  assert (n <> n + 1) by lia.
  repeat split; try lia.
  all: try (repeat first [ rewrite upd_same | rewrite upd_other by lia ]; reflexivity).
  intros y Hy H1 H2. repeat rewrite upd_other by lia. reflexivity.
Qed.

(** [add(le)] on any log object: the roll-over decision, the new LayerInfo
    and EntryContainer, the array store and the index increment. *)
Theorem add_step : forall s0 t le cap arr cI cL es,
  ms_frames s0 = [add_frame t le] ->
  ms_heap s0 t = Some (OObj TL (tl_fields cap arr cI cL)) ->
  ms_heap s0 arr = Some (OArr (TRef EC) es) ->
  Z.of_nat (length es) = cap -> 0 < cap <= INT_MAX -> 0 <= cI <= cap ->
  t < ms_next s0 -> arr < ms_next s0 ->
  erroneous wp 64 (ms_statics s0) EC = false -> init_needed wp 64 (ms_inited s0) EC = None ->
  erroneous wp 64 (ms_statics s0) LI = false -> init_needed wp 64 (ms_inited s0) LI = None ->
  let roll := cap <=? cI in
  returns wp (mdl e) s0 (Some (VRef (ms_next s0)))
    (add_post s0 t le cap arr (if roll then 0 else cI) (if roll then wrap 32 (cL + 1) else cL)
              (if roll then 1 else 0) es).
Proof.
  intros s0 t le cap arr cI cL es Hfr Ht Ha Hlen Hcap HcI Ht' Ha' He1 Hi1 He2 Hi2 roll.
  assert (Hta : t <> arr) by (intro E; subst arr; rewrite Ht in Ha; discriminate).
  destruct s0 as [h n sts ini lk fs]; cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames] in *. subst fs.
  unfold roll; clear roll.
  lstep. lstep. lstep. GET. lstep. GET.
  destruct (cI <? cap) eqn:E.
  - (* no roll-over: jump to 30 *)
    replace (cap <=? cI) with false by (symmetry; apply Z.leb_gt; apply Z.ltb_lt in E; lia).
    lstep.
    eapply returns_weaken.
    + match goal with |- returns _ _ ?S _ _ => apply (add_from30 S t le cap arr cI cL 0 es) end;
        cbn [ms_frames ms_heap ms_next ms_statics ms_inited]; try eassumption; try reflexivity; try (apply Z.ltb_lt in E; lia).
    + unfold add_post. cbn [ms_heap ms_next ms_statics ms_inited]. tauto.
  - (* roll-over: currentLayer++, currentIndex = 0, flag = true *)
    replace (cap <=? cI) with true by (symmetry; apply Z.leb_le; apply Z.ltb_ge in E; lia).
    lstep. lstep. lstep. GET. lstep. lstep. PUT. lstep. lstep. PUT. lstep. lstep.
    eapply returns_weaken.
    + match goal with |- returns _ _ ?S _ _ => apply (add_from30 S t le cap arr 0 (wrap 32 (cL + 1)) 1 es) end;
        cbn [ms_frames ms_heap ms_next ms_statics ms_inited]; try eassumption; try reflexivity;
        try (rewrite upd_same; reflexivity); try (rewrite !upd_other by lia; eassumption); try lia.
    + unfold add_post. cbn [ms_heap ms_next ms_statics ms_inited].
      intros s' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
      repeat split; try assumption.
      intros y Hy Hyt Hya. rewrite H8 by assumption. rewrite !upd_other by assumption. reflexivity.
Qed.

(** The constructor [TransactionLog(int capacity)], called on a fresh object
    (fields at their defaults, as after [new]). *)
Definition tl_init_frame (t cap : Z) : cframe :=
  {| cf_class := TL; cf_method := tl_init_m; cf_code := tl_init_code; cf_rt := None;
     cf_frame := mkframe 0 nil ([VRef t; VInt cap] ++ repeat VTop (Z.to_nat (c_max_locals tl_init_code - 2)));
     cf_resume := None; cf_clinit := false |}.

Theorem tl_init : forall s t cap,
  ms_frames s = [tl_init_frame t cap] ->
  ms_heap s t = Some (OObj TL tl_default) -> t < ms_next s ->
  0 <= cap <= MAX_ARRAY ->
  returns wp (mdl e) s None
    (fun s' => ms_heap s' t = Some (OObj TL (tl_fields cap (ms_next s) 0 0)) /\
               ms_heap s' (ms_next s) = Some (OArr (TRef EC) (repeat VNull (Z.to_nat cap))) /\
               ms_next s' = ms_next s + 1 /\ ms_statics s' = ms_statics s /\ ms_inited s' = ms_inited s /\
               (forall y, y < ms_next s -> y <> t -> ms_heap s' y = ms_heap s y)).
Proof.
  intros s t cap Hfr Ht Ht' Hcap.
  destruct s as [h n sts ini lk fs]; cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames] in *. subst fs.
  lstep. OBJINIT.
  lstep. lstep. PUT.
  lstep. lstep.
  eapply returns_step.
  { eapply mstep_anewarray; [ reflexivity | reflexivity | reflexivity | apply Z.ltb_ge; lia | apply Z.ltb_ge; lia
                            | reflexivity ]. }
  nz.
  PUT.
  eapply returns_now.
  { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
  cbn [with_frames ms_heap ms_next ms_statics ms_inited].
  assert (t <> n) by lia.
  repeat split.
  - repeat first [ rewrite upd_same | rewrite upd_other by lia ]. reflexivity.
  - repeat first [ rewrite upd_same | rewrite upd_other by lia ]. reflexivity.
  - intros y Hy Hyt. repeat rewrite upd_other by lia. reflexivity.
Qed.

End Add.

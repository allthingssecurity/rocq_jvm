From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic Tactics.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Classes Require CimFix.
Import ListNotations.
Open Scope Z_scope.

Definition cim_p : program :=
  ltac:(let x := eval vm_compute in (match load_program CimFix.files with Some p => p | None => nil end) in exact x).

Definition cih_m : method :=
  ltac:(let x := eval vm_compute in (match resolve_full cim_p "org/apache/camel/util/CaseInsensitiveMap" "caseInsensitiveHash" "(Ljava/lang/String;)I" with Some (_, m) => m | None => {| m_name := ""; m_desc := ""; m_access := 0; m_code := None |} end) in exact x).

Definition cih_code : code :=
  ltac:(let x := eval vm_compute in (match m_code cih_m with Some c => c | None => {| c_max_stack := 0; c_max_locals := 0; c_length := 0; c_instrs := nil; c_handlers := nil |} end) in exact x).


Section CIH.
Variable e : jenv.
Definition mdl := jdk_model cim_p e.

Definition cih_frame (pc_ : Z) (stk lv : list value) : cframe :=
  {| cf_class := "org/apache/camel/util/CaseInsensitiveMap"; cf_method := cih_m; cf_code := cih_code;
     cf_rt := Some TInt; cf_frame := mkframe pc_ stk lv; cf_resume := None; cf_clinit := false |}.

Definition st_at (s0 : mstate) (pc_ : Z) (stk lv : list value) : mstate :=
  with_frames s0 [cih_frame pc_ stk lv].

(** The per-character fold of the source, exactly as the bytecode computes it. *)
Definition fold_char (c : Z) : Z :=
  if negb (c <? 65) && negb (90 <? c) then i2c (wrap 32 (c + 32))
  else if c <? 128 then c
  else i2c (u_lower (j_u e) (i2c (u_upper (j_u e) c))).

Definition hstep (h c : Z) : Z := wrap 32 (wrap 32 (31 * h) + fold_char c).

Definition cih_spec (u : list Z) : Z :=
  let h := fold_left hstep u 0 in
  wrap 32 (Z.lxor h (wrap 32 (Z.shiftr (h mod 2 ^ 32) (Z.land 16 (32 - 1))))).

Ltac norm := unfold with_frames, set_frame, set_resume, cih_frame, st_at;
  cbn [ms_heap ms_next ms_statics ms_inited ms_locks ms_frames cf_frame f_pc f_stack f_locals
       cf_class cf_method cf_code cf_rt cf_resume cf_clinit].

Ltac sym := cbn -[wrap i2c nth_unit hstep fold_char].

Ltac rw := repeat (progress sym_rewrite; sym).
Ltac run1 := eapply returns_step; [ sym; rw; reflexivity | norm ].

Lemma nth_unit_firstn : forall u i, 0 <= i < Z.of_nat (length u) ->
  nth_unit u i = Some (nth (Z.to_nat i) u 0).
Proof.
  induction u as [|c u IH]; intros i Hi; simpl in *; [lia|].
  destruct (Z.eqb_spec i 0) as [->|Hne]; [reflexivity|].
  rewrite IH by lia. replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia. reflexivity.
Qed.

Lemma firstn_S_snoc : forall (u : list Z) (i : nat), (i < length u)%nat ->
  firstn (S i) u = app (firstn i u) [nth i u 0].
Proof.
  induction u as [|c u IH]; intros i Hi; simpl in *; [lia|].
  destruct i as [|i]; [reflexivity|]. simpl. f_equal. apply IH. lia.
Qed.

Lemma fold_firstn_S : forall u (i : nat), (i < length u)%nat ->
  fold_left hstep (firstn (S i) u) 0 = hstep (fold_left hstep (firstn i u) 0) (nth i u 0).
Proof.
  intros u i Hi. rewrite firstn_S_snoc by auto. rewrite fold_left_app. reflexivity.
Qed.

Lemma fc_string : find_class cim_p "java/lang/String" = None. Proof. vm_compute. reflexivity. Qed.
Lemma fc_char : find_class cim_p "java/lang/Character" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_charAt : resolve_full cim_p "java/lang/String" "charAt" "(I)C" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_length : resolve_full cim_p "java/lang/String" "length" "()I" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_up : resolve_full cim_p "java/lang/Character" "toUpperCase" "(C)C" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_low : resolve_full cim_p "java/lang/Character" "toLowerCase" "(C)C" = None. Proof. vm_compute. reflexivity. Qed.
Lemma fu_string : first_unloaded cim_p 64 "java/lang/String" = "java/lang/String". Proof. vm_compute. reflexivity. Qed.
Lemma err_char : forall st, erroneous cim_p 64 st "java/lang/Character" = false. Proof. intros. vm_compute. reflexivity. Qed.
Lemma in_char : forall st, init_needed cim_p 64 st "java/lang/Character" = None. Proof. intros. vm_compute. reflexivity. Qed.



Definition st (h : heap) (n : Z) (sts : list (string * value)) (ini : list string) (lk : list (Z * Z))
  (pc_ : Z) (stk lv : list value) : mstate :=
  {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
     ms_frames := [cih_frame pc_ stk lv] |}.

Lemma st_local : forall h n a b c pc stk lv pc' stk' lv',
  with_frames (st h n a b c pc stk lv) (set_frame (cih_frame pc stk lv) (mkframe pc' stk' lv') :: nil)
  = st h n a b c pc' stk' lv'.
Proof. reflexivity. Qed.

Lemma st_model : forall h n a b c pc stk lv pc' stk' lv',
  with_frames (with_frames (st h n a b c pc stk lv) (ms_frames (st h n a b c pc stk lv)))
    (set_frame (cih_frame pc stk lv) (mkframe pc' stk' lv') :: nil)
  = st h n a b c pc' stk' lv'.
Proof. reflexivity. Qed.

Ltac nrm := rewrite ?st_local, ?st_model.

(** Branch tests and lookups are discharged with the hypotheses in context. *)
Ltac use_hyps :=
  repeat match goal with
  | H : ?a = ?b |- context [?a] => progress rewrite H
  end.

Ltac lstep := eapply returns_step;
  [ eapply mstep_local; [ reflexivity | reflexivity | reflexivity
                        | cbn -[wrap i2c nth_unit Z.mul iinc]; use_hyps; cbn -[wrap i2c nth_unit Z.mul iinc]; reflexivity
                        | reflexivity ]
  | nrm ].

(** The JDK model calls of this method. *)
Lemma m_length : forall h n a b c pc stk lv l u,
  h l = Some (OStr u) ->
  jdk_model cim_p e "java/lang/String" "length" "()I" [VRef l] (st h n a b c pc stk lv)
  = MOk (Some (VInt (slen u))) (st h n a b c pc stk lv).
Proof. intros. unfold jdk_model. cbv -[slen st]. cbn [ms_heap st]. rewrite H. reflexivity. Qed.

Lemma m_charAt : forall h n a b c pc stk lv l u i ch,
  h l = Some (OStr u) -> nth_unit u i = Some ch ->
  jdk_model cim_p e "java/lang/String" "charAt" "(I)C" [VRef l; VInt i] (st h n a b c pc stk lv)
  = MOk (Some (VInt ch)) (st h n a b c pc stk lv).
Proof.
  intros.
  (* the String model alone (its charAt case), then the dispatch of jdk_model to it *)
  assert (Hs : string_model e "charAt" "(I)C" [VRef l; VInt i] (st h n a b c pc stk lv)
               = MOk (Some (VInt ch)) (st h n a b c pc stk lv)).
  { unfold string_model. cbv -[nth_unit st char_at sioobe_index]. cbn [ms_heap st]. rewrite H.
    cbv -[nth_unit st sioobe_index]. rewrite H0. reflexivity. }
  unfold jdk_model. cbv -[string_model string_static object_model st]. rewrite Hs. reflexivity.
Qed.

Lemma m_upper : forall s ch,
  jdk_model cim_p e "java/lang/Character" "toUpperCase" "(C)C" [VInt ch] s = MOk (Some (VInt (i2c (u_upper (j_u e) ch)))) s.
Proof. intros. unfold jdk_model. cbv -[i2c u_upper j_u]. reflexivity. Qed.

Lemma m_lower : forall s ch,
  jdk_model cim_p e "java/lang/Character" "toLowerCase" "(C)C" [VInt ch] s = MOk (Some (VInt (i2c (u_lower (j_u e) ch)))) s.
Proof. intros. unfold jdk_model. cbv -[i2c u_lower j_u]. reflexivity. Qed.


(** A call on a String receiver answered by the model (lemma [ml]). *)
Ltac vstep ml :=
  eapply returns_step;
  [ erewrite mstep_invoke by reflexivity;
    eapply do_invoke_string_model;
    [ auto | cbn [ms_heap st]; eassumption | first [exact rf_charAt | exact rf_length] | exact fu_string
    | unfold mdl; erewrite ml; [reflexivity | eassumption ..] | reflexivity ]
  | nrm ].

Ltac sstep ml :=
  eapply returns_step;
  [ erewrite mstep_invoke by reflexivity;
    eapply do_invoke_static_model;
    [ apply err_char | apply in_char | first [exact rf_up | exact rf_low] | unfold mdl; apply ml | reflexivity ]
  | nrm ].

Lemma iteration : forall h n sts ini lk l u hacc i x v P,
  h l = Some (OStr u) -> 0 <= i < slen u ->
  returns cim_p mdl (st h n sts ini lk 9 [] [VRef l; VInt (hstep hacc (nth (Z.to_nat i) u 0)); VInt (iinc i 1);
                                           VInt (slen u); VInt (fold_char (nth (Z.to_nat i) u 0))]) v P ->
  returns cim_p mdl (st h n sts ini lk 9 [] [VRef l; VInt hacc; VInt i; VInt (slen u); x]) v P.
Proof.
  intros h n sts ini lk l u hacc i x v P H Hi HR.
  assert (Hc : nth_unit u i = Some (nth (Z.to_nat i) u 0)) by (apply nth_unit_firstn; unfold slen in Hi; lia).
  set (c := nth (Z.to_nat i) u 0) in *.
  assert (Hlt : (slen u <=? i) = false) by (apply Z.leb_gt; lia).
  lstep. lstep. lstep. lstep. lstep.
  vstep m_charAt.
  lstep. lstep. lstep.
  destruct (c <? 65) eqn:E1.
  - (* c < 65: no ASCII upper case; c < 128 *)
    lstep. lstep. lstep.
    assert (E3 : (c <? 128) = true) by (apply Z.ltb_lt; apply Z.ltb_lt in E1; lia).
    lstep.
    do 8 lstep.
    assert (Hf : fold_char c = c) by (unfold fold_char; rewrite E1, E3; reflexivity).
    unfold hstep in HR. rewrite Hf in HR. exact HR.
  - lstep. lstep. lstep.
    destruct (90 <? c) eqn:E2.
    + (* above 'Z' *)
      lstep. lstep. lstep.
      destruct (c <? 128) eqn:E3.
      * lstep. do 8 lstep.
        assert (Hf : fold_char c = c) by (unfold fold_char; rewrite E1, E2, E3; reflexivity).
        unfold hstep in HR. rewrite Hf in HR. exact HR.
      * lstep. lstep.
        sstep m_upper. sstep m_lower.
        do 9 lstep.
        assert (Hf : fold_char c = i2c (u_lower (j_u e) (i2c (u_upper (j_u e) c))))
          by (unfold fold_char; rewrite E1, E2, E3; reflexivity).
        unfold hstep in HR. rewrite Hf in HR. exact HR.
    + (* 'A'..'Z' *)
      do 6 lstep. do 9 lstep.
      assert (Hf : fold_char c = i2c (wrap 32 (c + 32))) by (unfold fold_char; rewrite E1, E2; reflexivity).
      unfold hstep in HR. rewrite Hf in HR. exact HR.
Qed.

Lemma exit_loop : forall h n sts ini lk l u hacc x,
  returns cim_p mdl (st h n sts ini lk 9 [] [VRef l; VInt hacc; VInt (slen u); VInt (slen u); x])
    (Some (VInt (wrap 32 (Z.lxor hacc (wrap 32 (Z.shiftr (hacc mod 2 ^ 32) (Z.land 16 (32 - 1))))))))
    (fun _ => True).
Proof.
  intros. assert (Hge : (slen u <=? slen u) = true) by (apply Z.leb_le; lia).
  lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
  eapply returns_now; [ | exact I ].
  eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | ].
  cbn -[wrap i2c nth_unit Z.mul iinc Z.lxor Z.shiftr Z.modulo Z.land Z.pow]. reflexivity.
Qed.

Lemma loop : forall h n sts ini lk l u, h l = Some (OStr u) -> slen u <= INT_MAX ->
  forall k i x, Z.to_nat (slen u - i) = k -> 0 <= i <= slen u ->
  returns cim_p mdl
    (st h n sts ini lk 9 [] [VRef l; VInt (fold_left hstep (firstn (Z.to_nat i) u) 0); VInt i; VInt (slen u); x])
    (Some (VInt (cih_spec u))) (fun _ => True).
Proof.
  intros h n sts ini lk l u H Hmax k. induction k as [|k IH]; intros i x Hk Hi.
  - assert (i = slen u) by lia. subst i.
    replace (firstn (Z.to_nat (slen u)) u) with u by (unfold slen; rewrite Nat2Z.id, firstn_all; reflexivity).
    apply exit_loop.
  - apply iteration; [assumption | lia | ].
    assert (Hinc : iinc i 1 = i + 1) by (unfold iinc; apply wrap32_id; unfold in_int, in_range, INT_MAX in *; simpl in *; lia).
    rewrite Hinc.
    replace (hstep (fold_left hstep (firstn (Z.to_nat i) u) 0) (nth (Z.to_nat i) u 0))
      with (fold_left hstep (firstn (Z.to_nat (i + 1)) u) 0).
    + apply IH; lia.
    + replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      apply fold_firstn_S. unfold slen in *. lia.
Qed.

(** [caseInsensitiveHash] of the real class, for every String argument and any
    Unicode tables [e]: it returns [cih_spec u] where [u] are the string's
    UTF-16 units, from any state (heap, statics, ...) whose top frame starts
    the method on that string. *)
Theorem caseInsensitiveHash_correct : forall h n sts ini lk l u,
  h l = Some (OStr u) -> slen u <= INT_MAX ->
  returns cim_p mdl (st h n sts ini lk 0 [] [VRef l; VTop; VTop; VTop; VTop])
    (Some (VInt (cih_spec u))) (fun _ => True).
Proof.
  intros h n sts ini lk l u H Hmax.
  lstep. lstep. lstep. lstep. lstep.
  vstep m_length.
  lstep.
  apply (loop h n sts ini lk l u H Hmax (Z.to_nat (slen u - 0)) 0); [lia | unfold slen; lia].
Qed.
End CIH.

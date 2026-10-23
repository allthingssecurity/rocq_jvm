(** * CaseInsensitiveMap (fix 27aeb4f860d9): calls of [caseInsensitiveHash] and
    [findIndex(String, int)] from any caller, on any heap.

    Building blocks for the unbounded put/remove/get proofs ([CimMap.v]).  The
    program is [CimProg.fix_prog] (the real class + AbstractMap/Map model classes);
    the Unicode tables [e] are arbitrary. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg.
From JVM.Camel Require CimHash.
Import ListNotations.
Open Scope Z_scope.

Definition cp := fix_prog.

Definition no_code : code := {| c_max_stack := 0; c_max_locals := 0; c_length := 0; c_instrs := nil; c_handlers := nil |}.
Definition code_of (cls name desc : string) : code :=
  match resolve_full cp cls name desc with
  | Some (_, m) => match m_code m with Some c => c | None => no_code end
  | None => no_code
  end.
Definition mk_m (name desc : string) (acc : Z) (c : code) : method :=
  {| m_name := name; m_desc := desc; m_access := acc; m_code := Some c |}.

Definition cih_desc := "(Ljava/lang/String;)I"%string.
Definition fi_desc := "(Ljava/lang/String;I)I"%string.
Definition cih_code := ltac:(let x := eval vm_compute in (code_of CIM "caseInsensitiveHash" cih_desc) in exact x).
Definition fi_code := ltac:(let x := eval vm_compute in (code_of CIM "findIndex" fi_desc) in exact x).
Definition cih_acc := ltac:(let x := eval vm_compute in (match resolve_full cp CIM "caseInsensitiveHash" cih_desc with Some (_, m) => m_access m | None => 0 end) in exact x).
Definition fi_acc := ltac:(let x := eval vm_compute in (match resolve_full cp CIM "findIndex" fi_desc with Some (_, m) => m_access m | None => 0 end) in exact x).
Definition cih_m := mk_m "caseInsensitiveHash" cih_desc cih_acc cih_code.
Definition fi_m := mk_m "findIndex" fi_desc fi_acc fi_code.

Lemma rf_cih : resolve_full cp CIM "caseInsensitiveHash" cih_desc = Some (CIM, cih_m). Proof. vm_compute. reflexivity. Qed.
Lemma rf_fi : resolve_full cp CIM "findIndex" fi_desc = Some (CIM, fi_m). Proof. vm_compute. reflexivity. Qed.
Lemma rf_charAt : resolve_full cp "java/lang/String" "charAt" "(I)C" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_length : resolve_full cp "java/lang/String" "length" "()I" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_eic : resolve_full cp "java/lang/String" "equalsIgnoreCase" "(Ljava/lang/String;)Z" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_up : resolve_full cp "java/lang/Character" "toUpperCase" "(C)C" = None. Proof. vm_compute. reflexivity. Qed.
Lemma rf_low : resolve_full cp "java/lang/Character" "toLowerCase" "(C)C" = None. Proof. vm_compute. reflexivity. Qed.
Lemma fu_string : first_unloaded cp 64 "java/lang/String" = "java/lang/String". Proof. vm_compute. reflexivity. Qed.
Lemma err_char : forall st, erroneous cp 64 st "java/lang/Character" = false. Proof. intros. vm_compute. reflexivity. Qed.
Lemma in_char : forall st, init_needed cp 64 st "java/lang/Character" = None. Proof. intros. vm_compute. reflexivity. Qed.

Section Calls.
Variable e : jenv.
Definition mdl := jdk_model cp e.

Definition fold_char := CimHash.fold_char e.
Definition hstep := CimHash.hstep e.
Definition cih_spec := CimHash.cih_spec e.

(** The JDK model calls. *)
Lemma m_length : forall s l u, ms_heap s l = Some (OStr u) ->
  jdk_model cp e "java/lang/String" "length" "()I" [VRef l] s = MOk (Some (VInt (slen u))) s.
Proof. intros s l u H. unfold jdk_model. cbv -[slen ms_heap]. rewrite H. reflexivity. Qed.

Lemma m_charAt : forall s l u i ch, ms_heap s l = Some (OStr u) -> nth_unit u i = Some ch ->
  jdk_model cp e "java/lang/String" "charAt" "(I)C" [VRef l; VInt i] s = MOk (Some (VInt ch)) s.
Proof. intros s l u i ch H H0. unfold jdk_model. cbv -[nth_unit ms_heap]. rewrite H. cbv -[nth_unit]. rewrite H0. reflexivity. Qed.

Lemma m_upper : forall s ch,
  jdk_model cp e "java/lang/Character" "toUpperCase" "(C)C" [VInt ch] s = MOk (Some (VInt (i2c (u_upper (j_u e) ch)))) s.
Proof. intros. unfold jdk_model. cbv -[i2c u_upper j_u]. reflexivity. Qed.

Lemma m_lower : forall s ch,
  jdk_model cp e "java/lang/Character" "toLowerCase" "(C)C" [VInt ch] s = MOk (Some (VInt (i2c (u_lower (j_u e) ch)))) s.
Proof. intros. unfold jdk_model. cbv -[i2c u_lower j_u]. reflexivity. Qed.

(** ** caseInsensitiveHash as a callee: the state below the hash frame is fixed *)
Definition hframe (pc : Z) (stk lv : list value) : cframe :=
  {| cf_class := CIM; cf_method := cih_m; cf_code := cih_code; cf_rt := Some TInt;
     cf_frame := mkframe pc stk lv; cf_resume := None; cf_clinit := false |}.
Definition hs (s : mstate) (rest : list cframe) (pc : Z) (stk lv : list value) : mstate :=
  with_frames s (hframe pc stk lv :: rest).

Lemma hs_local : forall s rest pc stk lv pc' stk' lv',
  with_frames (hs s rest pc stk lv) (set_frame (hframe pc stk lv) (mkframe pc' stk' lv') :: rest) = hs s rest pc' stk' lv'.
Proof. reflexivity. Qed.
Lemma hs_model : forall s rest pc stk lv pc' stk' lv',
  with_frames (with_frames (hs s rest pc stk lv) (ms_frames (hs s rest pc stk lv)))
    (set_frame (hframe pc stk lv) (mkframe pc' stk' lv') :: rest) = hs s rest pc' stk' lv'.
Proof. reflexivity. Qed.
Ltac nrm := rewrite ?hs_local, ?hs_model.

Ltac use_hyps :=
  repeat match goal with
  | H : ?a = ?b |- context [?a] => progress rewrite H
  end.

Ltac lstep := eapply returns_step;
  [ eapply mstep_local; [ reflexivity | reflexivity | reflexivity
                        | cbn -[wrap i2c nth_unit Z.mul iinc]; use_hyps; cbn -[wrap i2c nth_unit Z.mul iinc]; reflexivity
                        | reflexivity ]
  | nrm ].

Ltac vstep ml :=
  eapply returns_step;
  [ erewrite mstep_invoke by reflexivity;
    eapply do_invoke_string_model;
    [ auto | cbn [ms_heap hs with_frames]; eassumption | first [exact rf_charAt | exact rf_length] | exact fu_string
    | unfold mdl; erewrite ml; [reflexivity | cbn [ms_heap hs with_frames]; eassumption ..] | reflexivity ]
  | nrm ].

Ltac sstep ml :=
  eapply returns_step;
  [ erewrite mstep_invoke by reflexivity;
    eapply do_invoke_static_model;
    [ apply err_char | apply in_char | first [exact rf_up | exact rf_low] | unfold mdl; apply ml | reflexivity ]
  | nrm ].

(** The continuation after the hash returns to caller [c]. *)
Definition hret (s : mstate) (c : cframe) (rs : list cframe) (v : Z) : mstate :=
  with_frames s (set_resume (set_frame c (mkframe (match cf_resume c with Some x => x | None => 0 end)
                                               (VInt v :: f_stack (cf_frame c)) (f_locals (cf_frame c)))) None :: rs).

Lemma iteration : forall s c rs l u hacc i x v P,
  ms_heap s l = Some (OStr u) -> 0 <= i < slen u ->
  returns cp mdl (hs s (c :: rs) 9 [] [VRef l; VInt (hstep hacc (nth (Z.to_nat i) u 0)); VInt (iinc i 1);
                                     VInt (slen u); VInt (fold_char (nth (Z.to_nat i) u 0))]) v P ->
  returns cp mdl (hs s (c :: rs) 9 [] [VRef l; VInt hacc; VInt i; VInt (slen u); x]) v P.
Proof.
  intros s c rs l u hacc i x v P H Hi HR.
  assert (Hc : nth_unit u i = Some (nth (Z.to_nat i) u 0)) by (apply CimHash.nth_unit_firstn; unfold slen in Hi; lia).
  set (ch := nth (Z.to_nat i) u 0) in *.
  assert (Hlt : (slen u <=? i) = false) by (apply Z.leb_gt; lia).
  lstep. lstep. lstep. lstep. lstep.
  vstep m_charAt.
  lstep. lstep. lstep.
  unfold hstep, fold_char, CimHash.hstep in HR.
  destruct (ch <? 65) eqn:E1.
  - lstep. lstep. lstep.
    assert (E3 : (ch <? 128) = true) by (apply Z.ltb_lt; apply Z.ltb_lt in E1; lia).
    lstep.
    do 8 lstep.
    assert (Hf : CimHash.fold_char e ch = ch) by (unfold CimHash.fold_char; rewrite E1, E3; reflexivity).
    rewrite Hf in HR. exact HR.
  - lstep. lstep. lstep.
    destruct (90 <? ch) eqn:E2.
    + lstep. lstep. lstep.
      destruct (ch <? 128) eqn:E3.
      * lstep. do 8 lstep.
        assert (Hf : CimHash.fold_char e ch = ch) by (unfold CimHash.fold_char; rewrite E1, E2, E3; reflexivity).
        rewrite Hf in HR. exact HR.
      * lstep. lstep.
        sstep m_upper. sstep m_lower.
        do 9 lstep.
        assert (Hf : CimHash.fold_char e ch = i2c (u_lower (j_u e) (i2c (u_upper (j_u e) ch))))
          by (unfold CimHash.fold_char; rewrite E1, E2, E3; reflexivity).
        rewrite Hf in HR. exact HR.
    + do 6 lstep. do 9 lstep.
      assert (Hf : CimHash.fold_char e ch = i2c (wrap 32 (ch + 32))) by (unfold CimHash.fold_char; rewrite E1, E2; reflexivity).
      rewrite Hf in HR. exact HR.
Qed.

Lemma exit_loop : forall s c rs l u hacc x v P nx,
  cf_resume c = Some nx ->
  returns cp mdl (hret s c rs (wrap 32 (Z.lxor hacc (wrap 32 (Z.shiftr (hacc mod 2 ^ 32) (Z.land 16 (32 - 1))))))) v P ->
  returns cp mdl (hs s (c :: rs) 9 [] [VRef l; VInt hacc; VInt (slen u); VInt (slen u); x]) v P.
Proof.
  intros s c rs l u hacc x v P nx Hr HR. assert (Hge : (slen u <=? slen u) = true) by (apply Z.leb_le; lia).
  lstep. lstep. lstep. lstep. lstep. lstep. lstep. lstep.
  eapply returns_step.
  { eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity
                            | cbn -[wrap i2c nth_unit Z.mul iinc Z.lxor Z.shiftr Z.modulo Z.land Z.pow]; reflexivity
                            | exact Hr ]. }
  unfold hret in HR. rewrite Hr in HR. exact HR.
Qed.

Lemma loop : forall s c rs l u nx v P, ms_heap s l = Some (OStr u) -> slen u <= INT_MAX -> cf_resume c = Some nx ->
  returns cp mdl (hret s c rs (cih_spec u)) v P ->
  forall k i x, Z.to_nat (slen u - i) = k -> 0 <= i <= slen u ->
  returns cp mdl (hs s (c :: rs) 9 [] [VRef l; VInt (fold_left hstep (firstn (Z.to_nat i) u) 0); VInt i; VInt (slen u); x]) v P.
Proof.
  intros s c rs l u nx v P H Hmax Hr HR k. induction k as [|k IH]; intros i x Hk Hi.
  - assert (i = slen u) by lia. subst i.
    replace (firstn (Z.to_nat (slen u)) u) with u by (unfold slen; rewrite Nat2Z.id, firstn_all; reflexivity).
    eapply exit_loop; [exact Hr | exact HR].
  - apply iteration; [assumption | lia | ].
    assert (Hinc : iinc i 1 = i + 1) by (unfold iinc; apply wrap32_id; unfold in_int, in_range, INT_MAX in *; simpl in *; lia).
    rewrite Hinc.
    replace (hstep (fold_left hstep (firstn (Z.to_nat i) u) 0) (nth (Z.to_nat i) u 0))
      with (fold_left hstep (firstn (Z.to_nat (i + 1)) u) 0).
    + apply IH; lia.
    + replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      apply CimHash.fold_firstn_S. unfold slen in *. lia.
Qed.

Definition cih_mr : methodref := {| mr_class := CIM; mr_name := "caseInsensitiveHash"; mr_desc := cih_desc; mr_interface := false |}.

(** Calling caseInsensitiveHash(String) from any frame, on any state where the class is
    initialised: the hash [cih_spec u] of the string's units is pushed; nothing else changes. *)
Lemma call_cih : forall s top rest nx l r u v P,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvStatic cih_mr, nx) ->
  f_stack (cf_frame top) = VRef l :: r ->
  ms_heap s l = Some (OStr u) -> slen u <= INT_MAX ->
  erroneous cp 64 (ms_statics s) CIM = false -> init_needed cp 64 (ms_inited s) CIM = None ->
  returns cp mdl (with_frames s (set_resume (set_frame top (mkframe nx (VInt (cih_spec u) :: r) (f_locals (cf_frame top)))) None :: rest)) v P ->
  returns cp mdl s v P.
Proof.
  intros s top rest nx l r u v P Hfr Hf Hst Hh Hmax He Hi HR.
  set (c := set_resume (set_frame top (mkframe (f_pc (cf_frame top)) r (f_locals (cf_frame top)))) (Some nx)).
  eapply returns_step.
  { erewrite mstep_invoke; [ | exact Hfr | exact Hf | reflexivity | rewrite Hst; reflexivity ].
    cbn [app]. erewrite do_invoke_static_enter; [ | exact He | exact Hi | exact rf_cih | reflexivity ].
    unfold enter. cbn -[set_resume set_frame]. reflexivity. }
  change (returns cp mdl (hs s (c :: rest) 0 [] [VRef l; VTop; VTop; VTop; VTop]) v P).
  lstep. lstep. lstep. lstep. lstep.
  vstep m_length.
  lstep.
  apply (loop s c rest l u nx v P Hh Hmax eq_refl HR (Z.to_nat (slen u - 0)) 0 VTop); [lia | unfold slen; lia].
Qed.

(** ** findIndex(String key, int hash) *)

Lemma m_eic : forall s a b ua ub, ms_heap s a = Some (OStr ua) -> ms_heap s b = Some (OStr ub) ->
  jdk_model cp e "java/lang/String" "equalsIgnoreCase" "(Ljava/lang/String;)Z" [VRef a; VRef b] s
  = MOk (Some (VInt (if equals_ignore_case (j_u e) ua ub then 1 else 0))) s.
Proof. intros s a b ua ub Ha Hb. unfold jdk_model. cbv -[equals_ignore_case ms_heap j_u]. rewrite Ha, Hb. reflexivity. Qed.

Lemma nth_z_bounds : forall {A} (l : list A) i x, nth_z l i = Some x -> 0 <= i < Z.of_nat (length l).
Proof.
  induction l as [|y r IH]; intros i x H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec i 0); [subst; cbn; lia|]. apply IH in H. cbn [length]. lia.
Qed.

Lemma bounds_false : forall {A} (l : list A) i x, nth_z l i = Some x -> ((i <? 0) || (Z.of_nat (length l) <=? i)) = false.
Proof. intros A l i x H. apply nth_z_bounds in H. apply orb_false_iff. split; [apply Z.ltb_ge | apply Z.leb_gt]; lia. Qed.

Definition STR := "java/lang/String"%string.

(** What findIndex computes: walk the chain from [i], return the first slot whose key
    equalsIgnoreCase [q], or -1. [None] if the walk is longer than the fuel or meets a
    malformed slot (then the lemma below says nothing). *)
Fixpoint fi_walk (h : heap) (ks cn : list value) (q : list Z) (i : Z) (f : nat) : option Z :=
  match f with
  | O => None
  | S f => if i =? -1 then Some (-1) else
      match nth_z ks i with
      | Some (VRef kl) =>
          match h kl with
          | Some (OStr ku) =>
              if equals_ignore_case (j_u e) ku q then Some i
              else match nth_z cn i with Some (VInt j) => fi_walk h ks cn q j f | _ => None end
          | _ => None
          end
      | _ => None
      end
  end.

Definition fframe (pc : Z) (stk lv : list value) : cframe :=
  {| cf_class := CIM; cf_method := fi_m; cf_code := fi_code; cf_rt := Some TInt;
     cf_frame := mkframe pc stk lv; cf_resume := None; cf_clinit := false |}.
Definition fs (s : mstate) (rest : list cframe) (pc : Z) (stk lv : list value) : mstate :=
  with_frames s (fframe pc stk lv :: rest).
Lemma fs_local : forall s rest pc stk lv pc' stk' lv',
  with_frames (fs s rest pc stk lv) (set_frame (fframe pc stk lv) (mkframe pc' stk' lv') :: rest) = fs s rest pc' stk' lv'.
Proof. reflexivity. Qed.
Lemma fs_model : forall s rest pc stk lv pc' stk' lv',
  with_frames (with_frames (fs s rest pc stk lv) (ms_frames (fs s rest pc stk lv)))
    (set_frame (fframe pc stk lv) (mkframe pc' stk' lv') :: rest) = fs s rest pc' stk' lv'.
Proof. reflexivity. Qed.
Ltac nrm ::= rewrite ?hs_local, ?hs_model, ?fs_local, ?fs_model.

Ltac hp := cbn [ms_heap fs hs with_frames]; eassumption.
Ltac GET := eapply returns_step;
  [ eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | hp | eassumption | reflexivity ] | nrm ].

(** The continuation after a callee returns int [v] to caller [c]. *)
Definition iret (s : mstate) (c : cframe) (rs : list cframe) (v : Z) : mstate :=
  with_frames s (set_resume (set_frame c (mkframe (match cf_resume c with Some x => x | None => 0 end)
                                               (VInt v :: f_stack (cf_frame c)) (f_locals (cf_frame c)))) None :: rs).

Lemma fi_loop : forall f s c rs nx m q qu hsh fs_ kA ks cA cn r v P,
  ms_heap s m = Some (OObj CIM fs_) ->
  assoc "keys" fs_ = Some (VRef kA) -> assoc "chainNext" fs_ = Some (VRef cA) ->
  ms_heap s kA = Some (OArr (TRef STR) ks) -> ms_heap s cA = Some (OArr TInt cn) ->
  ms_heap s q = Some (OStr qu) -> cf_resume c = Some nx ->
  forall idx, fi_walk (ms_heap s) ks cn qu idx f = Some r ->
  returns cp mdl (iret s c rs r) v P ->
  returns cp mdl (fs s (c :: rs) 15 [] [VRef m; VRef q; VInt hsh; VInt idx]) v P.
Proof.
  induction f as [|f IH]; intros s c rs nx m q qu hsh fs_ kA ks cA cn r v P Hm Hk Hc HkA HcA Hq Hr idx Hw HR;
    [discriminate|].
  cbn [fi_walk] in Hw.
  destruct (Z.eqb_spec idx (-1)) as [E|E].
  - (* end of chain: return -1 *)
    injection Hw as <-. subst idx.
    assert (E1 : (-1 =? -1) = true) by reflexivity.
    lstep. lstep. lstep. lstep.
    eapply returns_step.
    { eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | exact Hr ]. }
    unfold iret in HR. rewrite Hr in HR. exact HR.
  - assert (E1 : (idx =? -1) = false) by (apply Z.eqb_neq; exact E).
    destruct (nth_z ks idx) as [kv|] eqn:Ek; [|discriminate].
    destruct kv as [z|z|z|z| |kl|]; try discriminate.
    all: try (destruct (ms_heap s _); discriminate).
    destruct (ms_heap s kl) as [[| | ku | | |]|] eqn:Ekl; try discriminate.
    lstep. lstep. lstep.
    lstep. GET. lstep.
    eapply returns_step.
    { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                           | eapply bounds_false; exact Ek | exact Ek | reflexivity ]. }
    nrm. lstep.
    eapply returns_step.
    { erewrite mstep_invoke by reflexivity.
      eapply do_invoke_string_model;
        [ left; reflexivity | hp | exact rf_eic | exact fu_string
        | unfold mdl; erewrite m_eic; [ reflexivity | hp | hp ] | reflexivity ]. }
    nrm.
    destruct (equals_ignore_case (j_u e) ku qu) eqn:Eq.
    + injection Hw as <-.
      lstep. lstep.
      eapply returns_step.
      { eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | exact Hr ]. }
      unfold iret in HR. rewrite Hr in HR. exact HR.
    + destruct (nth_z cn idx) as [[j|z|z|z| |z|]|] eqn:Ec; try discriminate.
      lstep. lstep. GET. lstep.
      eapply returns_step.
      { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                             | eapply bounds_false; exact Ec | exact Ec | reflexivity ]. }
      nrm. lstep. lstep.
      eapply IH; eassumption.
Qed.

Definition fi_mr : methodref := {| mr_class := CIM; mr_name := "findIndex"; mr_desc := fi_desc; mr_interface := false |}.

Lemma call_fi : forall s top rest nx m q qu hsh rst fs_ tA tbl kA ks cA cn pw i0 r v P,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvVirtual fi_mr, nx) ->
  f_stack (cf_frame top) = VInt hsh :: VRef q :: VRef m :: rst ->
  ms_heap s m = Some (OObj CIM fs_) ->
  assoc "table" fs_ = Some (VRef tA) -> assoc "keys" fs_ = Some (VRef kA) -> assoc "chainNext" fs_ = Some (VRef cA) ->
  ms_heap s tA = Some (OArr TInt tbl) ->
  ms_heap s kA = Some (OArr (TRef STR) ks) -> ms_heap s cA = Some (OArr TInt cn) ->
  ms_heap s q = Some (OStr qu) ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  nth_z tbl (hsh mod 2 ^ pw) = Some (VInt i0) ->
  fi_walk (ms_heap s) ks cn qu i0 (S (length ks)) = Some r ->
  returns cp mdl (with_frames s (set_resume (set_frame top (mkframe nx (VInt r :: rst) (f_locals (cf_frame top)))) None :: rest)) v P ->
  returns cp mdl s v P.
Proof.
  intros s top rest nx m q qu hsh rst fs_ tA tbl kA ks cA cn pw i0 r v P Hfr Hf Hst Hm Ht Hk Hc HtA HkA HcA Hq Hlen Hpw Hb Hw HR.
  assert (Hp2 : 1 <= 2 ^ pw <= 2 ^ 30) by (split; [assert (0 < 2 ^ pw) by (apply Z.pow_pos_nonneg; lia); lia | apply Z.pow_le_mono_r; lia]).
  set (c := set_resume (set_frame top (mkframe (f_pc (cf_frame top)) rst (f_locals (cf_frame top)))) (Some nx)).
  eapply returns_step.
  { erewrite mstep_invoke; [ | exact Hfr | exact Hf | reflexivity | rewrite Hst; reflexivity ].
    cbn [app]. erewrite do_invoke_obj_enter; [ | left; reflexivity | exact Hm | exact rf_fi | reflexivity ].
    unfold enter. cbn -[set_resume set_frame]. reflexivity. }
  change (returns cp mdl (fs s (c :: rest) 0 [] [VRef m; VRef q; VInt hsh; VTop]) v P).
  lstep. GET. lstep. lstep. GET.
  eapply returns_step.
  { eapply mstep_arraylength; [ reflexivity | reflexivity | reflexivity | hp | reflexivity ]. }
  nrm. lstep. lstep. lstep.
  assert (Hw2 : wrap 32 (2 ^ pw - 1) = Z.ones pw)
    by (rewrite Z.ones_equiv; apply wrap_id; [lia | unfold in_range in *; cbn; lia]).
  assert (Hmod : 0 <= hsh mod 2 ^ pw < 2 ^ pw) by (apply Z.mod_pos_bound; lia).
  match goal with |- context [VInt ?X :: VRef tA :: _] =>
    assert (Hx : X = hsh mod 2 ^ pw) by
      (rewrite Hw2, Z.land_ones by lia; apply wrap_id; [lia | unfold in_range in *; cbn; lia]) end.
  rewrite Hx.
  eapply returns_step.
  { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                         | eapply bounds_false; exact Hb | exact Hb | reflexivity ]. }
  nrm. lstep.
  eapply (fi_loop (S (length ks)) s c rest nx m q qu hsh fs_ kA ks cA cn r v P); try eassumption; reflexivity.
Qed.

End Calls.

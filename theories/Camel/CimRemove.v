(** * CaseInsensitiveMap.remove (fix 27aeb4f860d9) on the real bytecode, for any heap.

    [remove_spec]: remove(key) hashes the key, walks the chain of its bucket and
    - if a slot holds a key that equalsIgnoreCase the argument: unlinks the slot
      (from the bucket head or from its predecessor), clears its key and value,
      decrements size and returns the old value;
    - otherwise returns null and changes nothing. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimPut CimTac.
Import ListNotations.
Open Scope Z_scope.

Definition rm_desc := "(Ljava/lang/Object;)Ljava/lang/Object;"%string.
Definition rm_code := ltac:(let x := eval vm_compute in (code_of CIM "remove" rm_desc) in exact x).
Definition rm_m := mk_m "remove" rm_desc 1 rm_code.

Definition rm_frame (m k : Z) : cframe :=
  {| cf_class := CIM; cf_method := rm_m; cf_code := rm_code; cf_rt := Some (TRef OBJ);
     cf_frame := mkframe 0 nil [VRef m; VRef k; VTop; VTop; VTop; VTop; VTop]; cf_resume := None; cf_clinit := false |}.

(** Every element of an Object[]/String[] is a reference or null. *)
Definition allrefs (vs : list value) : Prop :=
  forall i v, nth_z vs i = Some v -> (match v with VNull | VRef _ => true | _ => false end) = true.

Lemma nth_z_exists : forall {A} (l : list A) i, 0 <= i < Z.of_nat (length l) -> exists x, nth_z l i = Some x.
Proof.
  induction l as [|y r IH]; intros i Hi; cbn in *; [lia|].
  destruct (Z.eqb_spec i 0); [eauto|]. apply IH. lia.
Qed.

Lemma nth_z_nth : forall {A} (l : list A) i x d, nth_z l i = Some x -> nth (Z.to_nat i) l d = x.
Proof.
  induction l as [|y r IH]; intros i x d H; cbn in H; [discriminate|].
  destruct (Z.eqb_spec i 0).
  - subst. injection H as <-. reflexivity.
  - pose proof (nth_z_bounds r (i - 1) x H). replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
    cbn. apply IH. exact H.
Qed.

Section Remove.
Variable e : jenv.

(** The chain walk of remove: [Some (Some (prev, cur))] if slot [cur] (after [prev], or
    -1 at the head) holds a key equalsIgnoreCase [q]; [Some None] if the chain ends. *)
Fixpoint rm_walk (h : heap) (ks cn : list value) (q : list Z) (prev cur : Z) (f : nat) : option (option (Z * Z)) :=
  match f with
  | O => None
  | S f => if cur =? -1 then Some None else
      match nth_z ks cur with
      | Some (VRef kl) =>
          match h kl with
          | Some (OStr ku) =>
              match nth_z cn cur with
              | Some (VInt j) => if equals_ignore_case (j_u e) ku q then Some (Some (prev, cur))
                                 else rm_walk h ks cn q cur j f
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

Definition rm_ret (vs : list value) (res : option (Z * Z)) : value :=
  match res with None => VNull | Some (_, c) => nth (Z.to_nat c) vs VNull end.

(** The heap after remove found the key in slot [c] (predecessor [pr]); [j] is the slot after [c]. *)
Definition rm_heap (h : heap) (m tA kA vA cA sz u thr : Z) (af : value * value)
    (tbl ks vs cn : list value) (b pr c j : Z) : heap :=
  let h1 := if pr =? -1 then upd h tA (OArr TInt (set_nth_z tbl b (VInt j)))
            else upd h cA (OArr TInt (set_nth_z cn pr (VInt j))) in
  let h2 := upd h1 kA (OArr (TRef STR) (set_nth_z ks c VNull)) in
  let h3 := upd h2 vA (OArr (TRef OBJ) (set_nth_z vs c VNull)) in
  upd h3 m (OObj CIM (cim_fields tA kA vA cA (sz - 1) u thr af)).

Definition rm_post (h : heap) (n : Z) sts ini (m tA kA vA cA sz u thr : Z) af tbl ks vs cn b (res : option (Z * Z))
  (s' : mstate) : Prop :=
  ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini /\
  match res with
  | None => ms_heap s' = h
  | Some (pr, c) => exists j, nth_z cn c = Some (VInt j) /\
                     ms_heap s' = rm_heap h m tA kA vA cA sz u thr af tbl ks vs cn b pr c j
  end.

Lemma rm_loop : forall f h n sts ini lk m k ku hsh tA kA vA cA sz u thr af tbl ks vs cn b,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) ->
  h k = Some (OStr ku) -> length vs = length ks -> allrefs vs -> tA <> cA ->
  0 <= b < Z.of_nat (length tbl) -> 0 <= sz <= INT_MAX ->
  forall prev cur res, (prev = -1 \/ 0 <= prev < Z.of_nat (length cn)) ->
  rm_walk h ks cn ku prev cur f = Some res ->
  returns cp (mdl e)
    {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := [set_frame (rm_frame m k) (mkframe 29 nil [VRef m; VRef k; VInt hsh; VInt b; VInt prev; VInt cur; VTop])] |}
    (Some (rm_ret vs res)) (rm_post h n sts ini m tA kA vA cA sz u thr af tbl ks vs cn b res).
Proof.
  induction f as [|f IH];
    intros h n sts ini lk m k ku hsh tA kA vA cA sz u thr af tbl ks vs cn b
           Hm HtA HkA HvA HcA Hk Hvl Hrefs Htc Hb Hsz prev cur res Hprev Hw; [discriminate|].
  cbn [rm_walk] in Hw.
  destruct (Z.eqb_spec cur (-1)) as [E|E].
  - injection Hw as <-. subst cur.
    lstep. lstep. lstep. lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
    unfold rm_post. cbn. repeat split.
  - assert (E1 : (cur =? -1) = false) by (apply Z.eqb_neq; exact E).
    destruct (nth_z ks cur) as [kv|] eqn:Ek; [|discriminate].
    destruct kv as [z|z|z|z| |kl|]; try discriminate.
    destruct (h kl) as [[| | ku' | | |]|] eqn:Ekl; try discriminate.
    assert (Hcur : 0 <= cur < Z.of_nat (length ks)) by (eapply nth_z_bounds; exact Ek).
    lstep. lstep. lstep.
    lstep. GET. lstep.
    eapply returns_step.
    { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                           | eapply bounds_false; exact Ek | exact Ek | reflexivity ]. }
    nz. lstep.
    eapply returns_step.
    { eapply mstep_checkcast_ref; [ reflexivity | reflexivity | reflexivity | hp | apply asg_str | reflexivity ]. }
    nz.
    eapply returns_step.
    { erewrite mstep_invoke by reflexivity.
      eapply do_invoke_string_model;
        [ left; reflexivity | hp | exact rf_eic | exact fu_string
        | unfold mdl; erewrite m_eic; [ reflexivity | hp | hp ] | reflexivity ]. }
    nz.
    destruct (nth_z cn cur) as [[j|z|z|z| |z|]|] eqn:Ec; try discriminate.
    destruct (equals_ignore_case (j_u e) ku' ku) eqn:Eq.
    + (* found *)
      injection Hw as <-.
      destruct (nth_z_exists vs cur ltac:(rewrite Hvl; lia)) as (old & Hold).
      pose proof (Hrefs cur old Hold) as Hol.
      assert (Hos : slots old = 1) by (destruct old; try discriminate Hol; reflexivity).
      assert (Ho2 : cat2 old = false) by (destruct old; try discriminate Hol; reflexivity).
      assert (Hret : rm_ret vs (Some (prev, cur)) = old) by (apply nth_z_nth; exact Hold).
      rewrite Hret.
      assert (Hs1 : wrap 32 (sz - 1) = sz - 1) by (apply wrap_id; [lia | unfold in_range, INT_MAX in *; cbn; lia]).
      assert (Hcv : ((cur <? 0) || (Z.of_nat (length vs) <=? cur)) = false) by (eapply bounds_false; exact Hold).
      assert (Hck : ((cur <? 0) || (Z.of_nat (length ks) <=? cur)) = false) by (eapply bounds_false; exact Ek).
      assert (Hbt : ((b <? 0) || (Z.of_nat (length tbl) <=? b)) = false) by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
      assert (Hmt : m <> tA) by (intro E2; subst; rewrite Hm in HtA; discriminate).
      assert (Hmk : m <> kA) by (intro E2; subst; rewrite Hm in HkA; discriminate).
      assert (Hmv : m <> vA) by (intro E2; subst; rewrite Hm in HvA; discriminate).
      assert (Hmc : m <> cA) by (intro E2; subst; rewrite Hm in HcA; discriminate).
      assert (Hkt : kA <> tA) by (intro E2; subst; rewrite HkA in HtA; discriminate).
      assert (Hkv : kA <> vA) by (intro E2; subst; rewrite HkA in HvA; discriminate).
      assert (Hkc : kA <> cA) by (intro E2; subst; rewrite HkA in HcA; discriminate).
      assert (Hvt : vA <> tA) by (intro E2; subst; rewrite HvA in HtA; discriminate).
      assert (Hvc : vA <> cA) by (intro E2; subst; rewrite HvA in HcA; discriminate).
      lstep. lstep. GET. lstep.
      eapply returns_step.
      { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                             | exact Hcv | exact Hold | cbn -[slots]; rewrite Hos; reflexivity ]. }
      nz. lstep.
      destruct (Z.eqb_spec prev (-1)) as [Ep|Ep].
      * subst prev.
        lstep. lstep. lstep.
        lstep. GET. lstep. lstep. GET. lstep.
        eapply returns_step.
        { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                               | eapply bounds_false; exact Ec | exact Ec | reflexivity ]. }
        nz.
        eapply returns_step.
        { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity
                                     | exact Hbt | reflexivity ]. }
        nz. lstep.
        lstep. GET. lstep. lstep.
        eapply returns_step.
        { eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hck | reflexivity ]. }
        nz. lstep. GET. lstep. lstep.
        eapply returns_step.
        { eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hcv | reflexivity ]. }
        nz. lstep. lstep. GET. lstep. lstep. PUT. lstep.
        eapply returns_now.
        { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity
                                     | cbn; destruct old; try discriminate Hol; reflexivity ]. }
        unfold rm_post. cbn [with_frames ms_heap ms_next ms_statics ms_inited].
        refine (conj eq_refl (conj eq_refl (conj eq_refl _))). exists j. split; [exact Ec | reflexivity].
      * assert (Ep' : (prev =? -1) = false) by (apply Z.eqb_neq; exact Ep).
        assert (Hpb : ((prev <? 0) || (Z.of_nat (length cn) <=? prev)) = false)
          by (destruct Hprev as [Hp|Hp]; [contradiction | apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia]).
        lstep. lstep. lstep.
        lstep. GET. lstep. lstep. GET. lstep.
        eapply returns_step.
        { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                               | eapply bounds_false; exact Ec | exact Ec | reflexivity ]. }
        nz.
        eapply returns_step.
        { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity
                                     | exact Hpb | reflexivity ]. }
        nz.
        lstep. GET. lstep. lstep.
        eapply returns_step.
        { eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hck | reflexivity ]. }
        nz. lstep. GET. lstep. lstep.
        eapply returns_step.
        { eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hcv | reflexivity ]. }
        nz. lstep. lstep. GET. lstep. lstep. PUT. lstep.
        eapply returns_now.
        { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity
                                     | cbn; destruct old; try discriminate Hol; reflexivity ]. }
        unfold rm_post, rm_heap. rewrite Ep'. cbn [with_frames ms_heap ms_next ms_statics ms_inited].
        refine (conj eq_refl (conj eq_refl (conj eq_refl _))). exists j. split; [exact Ec | reflexivity].
    + lstep. lstep. lstep. lstep. GET. lstep.
      eapply returns_step.
      { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                             | eapply bounds_false; exact Ec | exact Ec | reflexivity ]. }
      nz. lstep. lstep.
      eapply IH; try eassumption.
      right. eapply nth_z_bounds. exact Ec.
Qed.

Theorem remove_spec : forall h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks vs cn pw i0 res,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> length vs = length ks -> allrefs vs -> tA <> cA ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 -> 0 <= sz <= INT_MAX ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None ->
  nth_z tbl (cih_spec e ku mod 2 ^ pw) = Some (VInt i0) ->
  rm_walk h ks cn ku (-1) i0 (S (length ks)) = Some res ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [rm_frame m k] |}
    (Some (rm_ret vs res)) (rm_post h n sts ini m tA kA vA cA sz u thr af tbl ks vs cn (cih_spec e ku mod 2 ^ pw) res).
Proof.
  intros h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks vs cn pw i0 res
         Hm HtA HkA HvA HcA Hk Hmax Hvl Hrefs Htc Hlen Hpw Hsz He Hi Hb Hw.
  assert (Hbk : wrap 32 (Z.land (cih_spec e ku) (wrap 32 (2 ^ pw - 1))) = cih_spec e ku mod 2 ^ pw) by (apply bucket_eq; lia).
  assert (Hbb : 0 <= cih_spec e ku mod 2 ^ pw < Z.of_nat (length tbl)) by (rewrite Hlen; apply Z.mod_pos_bound; lia).
  lstep.
  eapply returns_step.
  { eapply mstep_checkcast_ref; [ reflexivity | reflexivity | reflexivity | hp | apply asg_str | reflexivity ]. }
  nz.
  eapply (call_cih e); [ reflexivity | reflexivity | reflexivity | exact Hk | exact Hmax | exact He | exact Hi | ].
  nz. lstep. lstep. lstep. GET. ALEN. lstep. lstep. lstep. lstep.
  lstep. lstep.
  lstep. GET. lstep.
  eapply returns_step.
  { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                         | eapply bounds_false; exact Hb | exact Hb | reflexivity ]. }
  nz. lstep.
  eapply rm_loop; try eassumption. left; reflexivity.
Qed.


(** ** get and containsKey *)
Definition get_desc := "(Ljava/lang/Object;)Ljava/lang/Object;"%string.
Definition get_code := ltac:(let x := eval vm_compute in (code_of CIM "get" get_desc) in exact x).
Definition get_m := mk_m "get" get_desc 1 get_code.
Definition ck_desc := "(Ljava/lang/Object;)Z"%string.
Definition ck_code := ltac:(let x := eval vm_compute in (code_of CIM "containsKey" ck_desc) in exact x).
Definition ck_m := mk_m "containsKey" ck_desc 1 ck_code.

Definition get_frame (m k : Z) : cframe :=
  {| cf_class := CIM; cf_method := get_m; cf_code := get_code; cf_rt := Some (TRef OBJ);
     cf_frame := mkframe 0 nil [VRef m; VRef k; VTop]; cf_resume := None; cf_clinit := false |}.
Definition ck_frame (m k : Z) : cframe :=
  {| cf_class := CIM; cf_method := ck_m; cf_code := ck_code; cf_rt := Some TBool;
     cf_frame := mkframe 0 nil [VRef m; VRef k]; cf_resume := None; cf_clinit := false |}.

Theorem get_spec : forall h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks vs cn pw i0 r,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> length vs = length ks -> allrefs vs ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None ->
  nth_z tbl (cih_spec e ku mod 2 ^ pw) = Some (VInt i0) ->
  fi_walk e h ks cn ku i0 (S (length ks)) = Some r ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [get_frame m k] |}
    (Some (if r =? -1 then VNull else nth (Z.to_nat r) vs VNull))
    (fun s' => ms_heap s' = h /\ ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks vs cn pw i0 r
         Hm HtA HkA HvA HcA Hk Hmax Hvl Hrefs Hlen Hpw He Hi Hb Hw.
  lstep. lstep.
  eapply returns_step.
  { eapply mstep_checkcast_ref; [ reflexivity | reflexivity | reflexivity | hp | apply asg_str | reflexivity ]. }
  nz.
  eapply (call_fi1 e); [ reflexivity | reflexivity | reflexivity | exact Hm | apply cim_fields_reads | reflexivity | reflexivity | reflexivity
                       | exact HtA | exact HkA | exact HcA | exact Hk | exact Hmax | exact He | exact Hi
                       | exact Hlen | exact Hpw | exact Hb | exact Hw | ].
  nz. lstep. lstep. lstep.
  destruct (Z.eqb_spec r (-1)) as [E|E].
  - subst r. lstep. lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
    cbn. repeat split.
  - assert (E' : (r =? -1) = false) by (apply Z.eqb_neq; exact E).
    (* r is a slot found by the walk, so it is in bounds *)
    assert (Hr : 0 <= r < Z.of_nat (length ks)).
    { clear -Hw E. revert i0 Hw. generalize (S (length ks)) as f. induction f as [|f IH]; intros i0 Hw; cbn in Hw; [discriminate|].
      destruct (i0 =? -1) eqn:Ei; [injection Hw as <-; lia|].
      destruct (nth_z ks i0) as [[z|z|z|z| |kl|]|] eqn:Ek; try discriminate.
      destruct (h kl) as [[| | ku' | | |]|]; try discriminate.
      destruct (equals_ignore_case (j_u e) ku' ku).
      - injection Hw as <-. eapply nth_z_bounds. exact Ek.
      - destruct (nth_z cn i0) as [[j|z|z|z| |z|]|]; try discriminate. eapply IH. exact Hw. }
    destruct (nth_z_exists vs r ltac:(rewrite Hvl; lia)) as (old & Hold).
    pose proof (Hrefs r old Hold) as Hol.
    assert (Hos : slots old = 1) by (destruct old; try discriminate Hol; reflexivity).
    rewrite (nth_z_nth vs r old VNull Hold).
    lstep. lstep. GET. lstep.
    eapply returns_step.
    { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                           | eapply bounds_false; exact Hold | exact Hold | cbn -[slots]; rewrite Hos; reflexivity ]. }
    nz. lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity
                                 | cbn; destruct old; try discriminate Hol; reflexivity ]. }
    cbn. repeat split.
Qed.

Theorem containsKey_spec : forall h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks cn pw i0 r,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) -> h cA = Some (OArr TInt cn) ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None ->
  nth_z tbl (cih_spec e ku mod 2 ^ pw) = Some (VInt i0) ->
  fi_walk e h ks cn ku i0 (S (length ks)) = Some r ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [ck_frame m k] |}
    (Some (VInt (if r =? -1 then 0 else 1)))
    (fun s' => ms_heap s' = h /\ ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku tA kA vA cA sz u thr af tbl ks cn pw i0 r
         Hm HtA HkA HcA Hk Hmax Hlen Hpw He Hi Hb Hw.
  lstep. lstep.
  eapply returns_step.
  { eapply mstep_checkcast_ref; [ reflexivity | reflexivity | reflexivity | hp | apply asg_str | reflexivity ]. }
  nz.
  eapply (call_fi1 e); [ reflexivity | reflexivity | reflexivity | exact Hm | apply cim_fields_reads | reflexivity | reflexivity | reflexivity
                       | exact HtA | exact HkA | exact HcA | exact Hk | exact Hmax | exact He | exact Hi
                       | exact Hlen | exact Hpw | exact Hb | exact Hw | ].
  nz.
  destruct (r =? -1) eqn:E'.
  - lstep. lstep. lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
    cbn. repeat split.
  - lstep. lstep. lstep. lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
    cbn. repeat split.
Qed.

End Remove.

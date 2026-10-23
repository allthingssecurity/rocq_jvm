(** * CaseInsensitiveMap.put (fix 27aeb4f860d9) on the real bytecode, for any heap.

    [put_present]: the key is in the map (findIndex finds slot idx): the value in slot
    idx is replaced and the old value returned; nothing else changes.
    [put_new_fast]: the key is not in the map, no resize is due (size < threshold) and
    there is a free slot (usedSlots < keys.length): the key and value go to slot
    usedSlots, the slot is pushed on the front of its bucket's chain, size and
    usedSlots grow by one.
    The other two paths of put (resize; compaction or growth of the slot arrays) are in
    [CimPutSlow.v]. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls.
Import ListNotations.
Open Scope Z_scope.

Definition put_desc := "(Ljava/lang/String;Ljava/lang/Object;)Ljava/lang/Object;"%string.
Definition dd_desc := "(Ljava/lang/String;I)Ljava/lang/String;"%string.
Definition put_code := ltac:(let x := eval vm_compute in (code_of CIM "put" put_desc) in exact x).
Definition dd_code := ltac:(let x := eval vm_compute in (code_of CIM "deduplicateKey" dd_desc) in exact x).
Definition put_m := mk_m "put" put_desc 1 put_code.
Definition dd_m := mk_m "deduplicateKey" dd_desc 10 dd_code.
Lemma rf_dd : resolve_full cp CIM "deduplicateKey" dd_desc = Some (CIM, dd_m). Proof. vm_compute. reflexivity. Qed.
Lemma asg_str : forall u, assignable cp 64 (runtime_type (OStr u)) STR = Some true. Proof. reflexivity. Qed.

Definition OBJ := "java/lang/Object"%string.
Definition KNOWN := static_key CIM "knownTable".

(** The fields of a CaseInsensitiveMap object; [af] are those of AbstractMap. *)
Definition cim_fields (tA kA vA cA sz u thr : Z) (af : list (string * value)) : list (string * value) :=
  [("table", VRef tA); ("keys", VRef kA); ("values", VRef vA); ("chainNext", VRef cA);
   ("size", VInt sz); ("usedSlots", VInt u); ("threshold", VInt thr)] ++ af.

Definition put_frame (m k : Z) (v : value) : cframe :=
  {| cf_class := CIM; cf_method := put_m; cf_code := put_code; cf_rt := Some (TRef OBJ);
     cf_frame := mkframe 0 nil [VRef m; VRef k; v; VTop; VTop; VTop; VTop]; cf_resume := None; cf_clinit := false |}.

(** A value that may be stored into an Object[] without getting stuck. *)
Definition vok (h : heap) (v : value) : Prop :=
  match v with
  | VNull => True
  | VRef l => exists o, h l = Some o /\ assignable cp 64 (runtime_type o) OBJ = Some true
  | _ => False
  end.

Section Put.
Variable e : jenv.

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
                        | cbn -[wrap i2c Z.mul iinc cat2 upd Z.pow Z.modulo]; use_hyps; cbn -[wrap i2c Z.mul iinc upd Z.pow Z.modulo]; reflexivity
                        | cbn -[cat2 upd]; use_hyps; reflexivity ]
  | try nz ].

Ltac neq := first [ assumption | apply not_eq_sym; assumption | lia ].
Ltac hp := cbn [ms_heap ms_statics ms_inited];
  repeat first [ rewrite upd_same | rewrite upd_other by neq ];
  first [ eassumption | reflexivity ].

Ltac GET := eapply returns_step;
  [ eapply mstep_getfield; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | reflexivity ] | try nz ].
Ltac PUT := eapply returns_step;
  [ eapply mstep_putfield; [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | hp
                           | reflexivity | reflexivity ] | try nz ].
Ltac RET := eapply returns_step;
  [ eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ]
  | try nz ].

Lemma bucket_eq : forall hsh pw, 0 <= pw <= 30 ->
  wrap 32 (Z.land hsh (wrap 32 (2 ^ pw - 1))) = hsh mod 2 ^ pw.
Proof.
  intros hsh pw Hpw.
  assert (Hp2 : 1 <= 2 ^ pw <= 2 ^ 30) by (split; [assert (0 < 2 ^ pw) by (apply Z.pow_pos_nonneg; lia); lia | apply Z.pow_le_mono_r; lia]).
  assert (Hw2 : wrap 32 (2 ^ pw - 1) = Z.ones pw)
    by (rewrite Z.ones_equiv; apply wrap_id; [lia | unfold in_range in *; cbn; lia]).
  assert (Hmod : 0 <= hsh mod 2 ^ pw < 2 ^ pw) by (apply Z.mod_pos_bound; lia).
  rewrite Hw2, Z.land_ones by lia. apply wrap_id; [lia | unfold in_range in *; cbn; lia].
Qed.

(** deduplicateKey(key, hash) with no registered known keys: returns key. *)
Definition dd_mr : methodref := {| mr_class := CIM; mr_name := "deduplicateKey"; mr_desc := dd_desc; mr_interface := false |}.

Lemma call_dd : forall s top rest nx k hsh r v P,
  ms_frames s = top :: rest ->
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvStatic dd_mr, nx) ->
  f_stack (cf_frame top) = VInt hsh :: VRef k :: r ->
  erroneous cp 64 (ms_statics s) CIM = false -> init_needed cp 64 (ms_inited s) CIM = None ->
  assoc KNOWN (ms_statics s) = Some VNull ->
  returns cp (mdl e) (with_frames s (set_resume (set_frame top (mkframe nx (VRef k :: r) (f_locals (cf_frame top)))) None :: rest)) v P ->
  returns cp (mdl e) s v P.
Proof.
  intros s top rest nx k hsh r v P Hfr Hf Hst He Hi HK HR.
  eapply returns_step.
  { erewrite mstep_invoke; [ | exact Hfr | exact Hf | reflexivity | rewrite Hst; reflexivity ].
    cbn [app]. erewrite do_invoke_static_enter; [ | exact He | exact Hi | exact rf_dd | reflexivity ].
    unfold enter. cbn -[set_resume set_frame]. reflexivity. }
  eapply returns_step.
  { eapply mstep_getstatic; [ reflexivity | reflexivity | exact He | exact Hi | exact HK | reflexivity ]. }
  lstep. lstep. lstep. lstep. RET. exact HR.
Qed.

(** The common prefix of put: hash, deduplicate (no known keys), findIndex. *)
Lemma put_prefix : forall h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0 idx P r,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  nth_z tbl (cih_spec e ku mod 2 ^ pw) = Some (VInt i0) ->
  fi_walk e h ks cn ku i0 (S (length ks)) = Some idx ->
  (match v with VNull | VRef _ => true | _ => false end) = true ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := [set_frame (put_frame m k v) (mkframe 19 nil [VRef m; VRef k; v; VInt (cih_spec e ku); VInt idx; VTop; VTop])] |} r P ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := [put_frame m k v] |} r P.
Proof.
  intros h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0 idx P r
         Hm HtA HkA HvA HcA Hk Hmax Hlen Hpw He Hi HK Hb Hw Hv HR.
  assert (Hc2 : cat2 v = false) by (destruct v; try discriminate Hv; reflexivity).
  assert (Hs2 : slots v = 1) by (destruct v; try discriminate Hv; reflexivity).
  lstep.
  eapply (call_cih e); [ reflexivity | reflexivity | reflexivity | exact Hk | exact Hmax | exact He | exact Hi | ].
  nz. lstep. lstep. lstep.
  eapply call_dd; [ reflexivity | reflexivity | reflexivity | exact He | exact Hi | exact HK | ].
  nz. lstep. lstep. lstep. lstep.
  eapply (call_fi e); [ reflexivity | reflexivity | reflexivity | exact Hm | reflexivity | reflexivity | reflexivity
                      | exact HtA | exact HkA | exact HcA | exact Hk | exact Hlen | exact Hpw | exact Hb | exact Hw | ].
  nz. lstep. exact HR.
Qed.

Definition put_post_frame := 0.

Theorem put_present : forall h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0 idx old,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  nth_z tbl (cih_spec e ku mod 2 ^ pw) = Some (VInt i0) ->
  fi_walk e h ks cn ku i0 (S (length ks)) = Some idx -> idx <> -1 ->
  nth_z vs idx = Some old -> (match old with VNull | VRef _ => true | _ => false end) = true -> vok h v ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some old)
    (fun s' => ms_heap s' = upd h vA (OArr (TRef OBJ) (set_nth_z vs idx v)) /\ ms_next s' = n /\
               ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0 idx old
         Hm HtA HkA HvA HcA Hk Hmax Hlen Hpw He Hi HK Hb Hw Hne Hold Hol Hv.
  assert (Ho2 : cat2 old = false) by (destruct old; try discriminate Hol; reflexivity).
  assert (Hos : slots old = 1) by (destruct old; try discriminate Hol; reflexivity).
  assert (Hv' : (match v with VNull | VRef _ => true | _ => false end) = true) by (destruct v; try contradiction; reflexivity).
  assert (Hc2 : cat2 v = false) by (destruct v; try discriminate Hv'; reflexivity).
  assert (Hs2 : slots v = 1) by (destruct v; try discriminate Hv'; reflexivity).
  eapply put_prefix; try eassumption.
  assert (E : (idx =? -1) = false) by (apply Z.eqb_neq; exact Hne).
  lstep. lstep. lstep.
  lstep. GET. lstep.
  eapply returns_step.
  { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                         | eapply bounds_false; exact Hold | exact Hold | cbn -[slots]; rewrite Hos; reflexivity ]. }
  nz. lstep. lstep. GET. lstep. lstep.
  destruct v as [z|z|z|z| |vl|]; try contradiction.
  - eapply returns_step.
    { eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                                 | eapply bounds_false; exact Hold | reflexivity ]. }
    nz. lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity
                                 | cbn; destruct old; try discriminate Hol; reflexivity ]. }
    cbn. repeat split.
  - destruct Hv as (o & Ho & Ha).
    eapply returns_step.
    { eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                                | eapply bounds_false; exact Hold | hp | reflexivity | exact Ha | reflexivity ]. }
    nz. lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity
                                 | cbn; destruct old; try discriminate Hol; reflexivity ]. }
    cbn. repeat split.
Qed.
Theorem put_new_fast : forall h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0,
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) ->
  tA <> cA ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX ->
  Z.of_nat (length tbl) = 2 ^ pw -> 0 <= pw <= 30 ->
  length vs = length ks -> length cn = length ks -> Z.of_nat (length ks) <= INT_MAX ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  nth_z tbl (cih_spec e ku mod 2 ^ pw) = Some (VInt i0) ->
  fi_walk e h ks cn ku i0 (S (length ks)) = Some (-1) ->
  0 <= sz < thr -> thr <= INT_MAX -> 0 <= u < Z.of_nat (length ks) -> vok h v ->
  (match v with VRef vl => vl <> m /\ vl <> kA | _ => True end) ->
  let b := cih_spec e ku mod 2 ^ pw in
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some VNull)
    (fun s' => ms_heap s' m = Some (OObj CIM (cim_fields tA kA vA cA (sz + 1) (u + 1) thr af)) /\
               ms_heap s' kA = Some (OArr (TRef STR) (set_nth_z ks u (VRef k))) /\
               ms_heap s' vA = Some (OArr (TRef OBJ) (set_nth_z vs u v)) /\
               ms_heap s' cA = Some (OArr TInt (set_nth_z cn u (VInt i0))) /\
               ms_heap s' tA = Some (OArr TInt (set_nth_z tbl b (VInt u))) /\
               (forall y, y <> m -> y <> kA -> y <> vA -> y <> cA -> y <> tA -> ms_heap s' y = h y) /\
               ms_next s' = n /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k v tA kA vA cA sz u thr af tbl ks vs cn pw ku i0
         Hm HtA HkA HvA HcA Htc Hk Hmax Hlen Hpw Hvl Hcl HK2 He Hi HK Hb Hw Hsz Hthr Hu Hv Hvd b.
  assert (Hv' : (match v with VNull | VRef _ => true | _ => false end) = true) by (destruct v; try contradiction; reflexivity).
  assert (Hc2 : cat2 v = false) by (destruct v; try discriminate Hv'; reflexivity).
  assert (Hs2 : slots v = 1) by (destruct v; try discriminate Hv'; reflexivity).
  assert (E1 : (sz <? thr) = true) by (apply Z.ltb_lt; lia).
  assert (E2 : (u <? Z.of_nat (length ks)) = true) by (apply Z.ltb_lt; lia).
  assert (Hu1 : wrap 32 (u + 1) = u + 1) by (apply wrap_id; [lia | unfold in_range, INT_MAX in *; cbn; lia]).
  assert (Hs1 : wrap 32 (sz + 1) = sz + 1) by (apply wrap_id; [lia | unfold in_range, INT_MAX in *; cbn; lia]).
  assert (Hbk : wrap 32 (Z.land (cih_spec e ku) (wrap 32 (2 ^ pw - 1))) = b) by (apply bucket_eq; lia).
  assert (Hbb : 0 <= b < Z.of_nat (length tbl)) by (rewrite Hlen; apply Z.mod_pos_bound; lia).
  assert (Hub : ((u <? 0) || (Z.of_nat (length ks) <=? u)) = false) by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
  assert (Hubv : ((u <? 0) || (Z.of_nat (length vs) <=? u)) = false) by (rewrite Hvl; exact Hub).
  assert (Hubc : ((u <? 0) || (Z.of_nat (length cn) <=? u)) = false) by (rewrite Hcl; exact Hub).
  assert (Hbt : ((b <? 0) || (Z.of_nat (length tbl) <=? b)) = false) by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
  (* distinct objects *)
  assert (Hmt : m <> tA) by (intro E; subst; rewrite Hm in HtA; discriminate).
  assert (Hmk : m <> kA) by (intro E; subst; rewrite Hm in HkA; discriminate).
  assert (Hmv : m <> vA) by (intro E; subst; rewrite Hm in HvA; discriminate).
  assert (Hmc : m <> cA) by (intro E; subst; rewrite Hm in HcA; discriminate).
  assert (Hkt : kA <> tA) by (intro E; subst; rewrite HkA in HtA; discriminate).
  assert (Hkv : kA <> vA) by (intro E; subst; rewrite HkA in HvA; discriminate).
  assert (Hkc : kA <> cA) by (intro E; subst; rewrite HkA in HcA; discriminate).
  assert (Hvt : vA <> tA) by (intro E; subst; rewrite HvA in HtA; discriminate).
  assert (Hvc : vA <> cA) by (intro E; subst; rewrite HvA in HcA; discriminate).
  assert (Hkk : k <> kA) by (intro E; subst; rewrite Hk in HkA; discriminate).
  assert (Hkm : k <> m) by (intro E; subst; rewrite Hk in Hm; discriminate).
  assert (Hkt2 : k <> tA) by (intro E; subst; rewrite Hk in HtA; discriminate).
  assert (Hkv2 : k <> vA) by (intro E; subst; rewrite Hk in HvA; discriminate).
  assert (Hkc2 : k <> cA) by (intro E; subst; rewrite Hk in HcA; discriminate).
  eapply put_prefix; try eassumption.
  (* 19: idx = -1, go to 45 *)
  lstep. lstep. lstep.
  (* 45: size < threshold: no resize *)
  lstep. GET. lstep. GET. lstep.
  (* 67: usedSlots < keys.length: free slot *)
  lstep. GET. lstep. GET.
  eapply returns_step.
  { eapply mstep_arraylength; [ reflexivity | reflexivity | reflexivity | hp | reflexivity ]. }
  nz. lstep.
  (* 157: slot = usedSlots++ *)
  lstep. lstep. GET. lstep. lstep. lstep. try rewrite Hu1. PUT. lstep.
  (* 170: keys[slot] = key *)
  lstep. GET. lstep. lstep.
  eapply returns_step.
  { eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hub | hp
                              | reflexivity | apply asg_str | reflexivity ]. }
  nz.
  (* 178: values[slot] = value *)
  lstep. GET. lstep. lstep.
  destruct v as [z|z|z|z| |vl|]; try contradiction.
  - eapply returns_step.
    { eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hubv | reflexivity ]. }
    nz.
    (* 186: b = hash & (table.length - 1) *)
    lstep. lstep. GET.
    eapply returns_step.
    { eapply mstep_arraylength; [ reflexivity | reflexivity | reflexivity | hp | reflexivity ]. }
    nz. lstep. lstep. lstep. try rewrite Hlen; try rewrite Hbk. lstep.
    (* 197: chainNext[slot] = table[b] *)
    lstep. GET. lstep. lstep. GET. lstep.
    eapply returns_step.
    { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hbt | exact Hb | reflexivity ]. }
    nz.
    eapply returns_step.
    { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hubc | reflexivity ]. }
    nz.
    (* 211: table[b] = slot *)
    lstep. GET. lstep. lstep.
    eapply returns_step.
    { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hbt | reflexivity ]. }
    nz.
    (* 220: size++ *)
    lstep. lstep. GET. lstep. lstep. try rewrite Hs1. PUT.
    lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
    cbn [with_frames ms_heap ms_next ms_statics ms_inited].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj eq_refl (conj eq_refl eq_refl)))))))).
    all: try (intros y Hy1 Hy2 Hy3 Hy4 Hy5).
    all: repeat first [ rewrite upd_same | rewrite upd_other by congruence ]; reflexivity.
  - destruct Hv as (o & Ho & Ha). destruct Hvd as [Hvd1 Hvd2].
    eapply returns_step.
    { eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hubv | hp
                                | reflexivity | exact Ha | reflexivity ]. }
    nz.
    lstep. lstep. GET.
    eapply returns_step.
    { eapply mstep_arraylength; [ reflexivity | reflexivity | reflexivity | hp | reflexivity ]. }
    nz. lstep. lstep. lstep. try rewrite Hlen; try rewrite Hbk. lstep.
    lstep. GET. lstep. lstep. GET. lstep.
    eapply returns_step.
    { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hbt | exact Hb | reflexivity ]. }
    nz.
    eapply returns_step.
    { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hubc | reflexivity ]. }
    nz.
    lstep. GET. lstep. lstep.
    eapply returns_step.
    { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hbt | reflexivity ]. }
    nz.
    lstep. lstep. GET. lstep. lstep. try rewrite Hs1. PUT.
    lstep.
    eapply returns_now.
    { eapply mstep_local_return; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity ]. }
    cbn [with_frames ms_heap ms_next ms_statics ms_inited].
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj eq_refl (conj eq_refl eq_refl)))))))).
    all: try (intros y Hy1 Hy2 Hy3 Hy4 Hy5).
    all: repeat first [ rewrite upd_same | rewrite upd_other by congruence ]; reflexivity.
Qed.

End Put.

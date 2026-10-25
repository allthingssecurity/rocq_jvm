(** * CaseInsensitiveMap.compactRemovedSlots (fix 27aeb4f860d9) on the real bytecode.

    The fix's new method: it moves the entries down over the slots of removed keys,
    keeping their order, relinks the chains through the array [newIndex], and frees
    the slots at the end.  [c1], [c2], [c3] are its three loops written as Rocq
    functions over the array contents (partial: [None] where the bytecode would fail,
    e.g. an index out of bounds); [call_compact] says the bytecode computes exactly them. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimPut CimTac.
Import ListNotations.
Open Scope Z_scope.

Definition cm_code := ltac:(let x := eval vm_compute in (code_of CIM "compactRemovedSlots" "()V") in exact x).
Definition cm_m := mk_m "compactRemovedSlots" "()V" 2 cm_code.
Lemma rf_cm : resolve_full cp CIM "compactRemovedSlots" "()V" = Some (CIM, cm_m). Proof. vm_compute. reflexivity. Qed.

Definition cmframe (pc : Z) (stk lv : list value) : cframe :=
  {| cf_class := CIM; cf_method := cm_m; cf_code := cm_code; cf_rt := None;
     cf_frame := mkframe pc stk lv; cf_resume := None; cf_clinit := false |}.

(** Loop 1: newIndex[i] = number of keys in slots before i, for the slots holding a key. *)
Fixpoint c1 (ks : list value) (i : Z) (f : nat) (n : Z) (ni : list value) : option (Z * list value) :=
  match f with
  | O => Some (n, ni)
  | S f =>
      match nth_z ks i with
      | Some VNull => c1 ks (i + 1) f n ni
      | Some (VRef _) => if (0 <=? i) && (i <? Z.of_nat (length ni)) then c1 ks (i + 1) f (n + 1) (set_nth_z ni i (VInt n)) else None
      | _ => None
      end
  end.

(** Loop 2: every bucket head is renumbered. *)
Fixpoint c2 (ni tbl : list value) (b : Z) (f : nat) : option (list value) :=
  match f with
  | O => Some tbl
  | S f =>
      match nth_z tbl b with
      | Some (VInt x) =>
          if x =? -1 then c2 ni tbl (b + 1) f
          else match nth_z ni x with Some (VInt y) => c2 ni (set_nth_z tbl b (VInt y)) (b + 1) f | _ => None end
      | _ => None
      end
  end.

Definition vok_b (h : heap) (v : value) : bool :=
  match v with
  | VNull => true
  | VRef l => match h l with Some o => match assignable cp 64 (runtime_type o) OBJ with Some true => true | _ => false end | None => false end
  | _ => false
  end.

(** Loop 3: every entry moves to its new slot, with its successor renumbered. *)
Definition not_in4 (a b c d t : Z) (v : value) : bool :=
  match v with VRef l => negb (l =? a) && negb (l =? b) && negb (l =? c) && negb (l =? d) && negb (l =? t) | _ => true end.

Fixpoint c3 (h : heap) (kA vA cA niA tA : Z) (ni : list value) (i : Z) (f : nat) (ks vs cn : list value) : option (list value * list value * list value) :=
  match f with
  | O => Some (ks, vs, cn)
  | S f =>
      match nth_z ks i with
      | Some VNull => c3 h kA vA cA niA tA ni (i + 1) f ks vs cn
      | Some (VRef kl) =>
          match nth_z ni i, nth_z cn i, nth_z vs i, h kl with
          | Some (VInt j), Some (VInt nx), Some vv, Some (OStr _) =>
              let ny := if nx =? -1 then Some (-1) else match nth_z ni nx with Some (VInt y) => Some y | _ => None end in
              match ny with
              | Some y =>
                  if (0 <=? j) && (j <? Z.of_nat (length cn)) && (j <? Z.of_nat (length ks)) && (j <? Z.of_nat (length vs))
                     && vok_b h vv && not_in4 kA vA cA niA tA vv && not_in4 kA vA cA niA tA (VRef kl)
                  then c3 h kA vA cA niA tA ni (i + 1) f (set_nth_z ks j (VRef kl)) (set_nth_z vs j vv) (set_nth_z cn j (VInt y))
                  else None
              | None => None
              end
          | _, _, _, _ => None
          end
      | _ => None
      end
  end.

Definition fill_null (es : list value) (f t : Z) : list value :=
  firstn (Z.to_nat f) es ++ repeat VNull (Z.to_nat (t - f)) ++ skipn (Z.to_nat t) es.

Lemma snz_len : forall {A} (l : list A) i v, length (set_nth_z l i v) = length l.
Proof. induction l as [|x r IH]; intros i v; cbn; [reflexivity|]. destruct (i =? 0); cbn; [reflexivity|]. now rewrite IH. Qed.

Ltac hfact := repeat first [ rewrite upd_same | rewrite upd_other by congruence ]; first [ reflexivity | eassumption ].

Section Compact.
Variable e : jenv.

Lemma c1_loop : forall f h nx sts ini lk c rs m niA fs0 kA ks u ni i cnt r v P,
  h m = Some (OObj CIM fs0) -> cim_reads fs0 -> assoc "keys" fs0 = Some (VRef kA) -> assoc "usedSlots" fs0 = Some (VInt u) ->
  h kA = Some (OArr (TRef STR) ks) -> h niA = Some (OArr TInt ni) -> niA <> m -> niA <> kA ->
  Z.to_nat (u - i) = f -> 0 <= i <= u -> u <= MAX_ARRAY -> 0 <= cnt <= i ->
  c1 ks i f cnt ni = Some r ->
  (forall h', h' niA = Some (OArr TInt (snd r)) -> (forall y, y <> niA -> h' y = h y) ->
     returns cp (mdl e) {| ms_heap := h'; ms_next := nx; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := set_frame (cmframe 0 nil [VRef m; VTop; VTop; VTop; VTop; VTop])
                      (mkframe 41 nil [VRef m; VRef niA; VInt (fst r); VInt u; VTop; VTop]) :: c :: rs |} v P) ->
  returns cp (mdl e) {| ms_heap := h; ms_next := nx; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := set_frame (cmframe 0 nil [VRef m; VTop; VTop; VTop; VTop; VTop])
                      (mkframe 11 nil [VRef m; VRef niA; VInt cnt; VInt i; VTop; VTop]) :: c :: rs |} v P.
Proof.
  induction f as [|f IH]; intros h nx sts ini lk c rs m niA fs0 kA ks u ni i cnt r v P
    Hm Hrd Hk Hu HkA Hni Hnm Hnk Hf Hi Hmax Hc Hr HK.
  - (* exit *)
    assert (i = u) by lia. subst i. cbn in Hr. injection Hr as <-.
    assert (E : (u <=? u) = true) by (apply Z.leb_le; lia).
    lstep. lstep. GET. lstep.
    apply HK; [exact Hni | reflexivity].
  - assert (Hlt : (u <=? i) = false) by (apply Z.leb_gt; lia).
    assert (Hi1 : wrap 32 (i + 1) = i + 1) by (apply wrap_id; [lia | unfold in_range, MAX_ARRAY in *; cbn; lia]).
    assert (Hii : iinc i 1 = i + 1) by (unfold iinc; exact Hi1).
    cbn [c1] in Hr.
    destruct (nth_z ks i) as [kv|] eqn:Ek; [|discriminate].
    lstep. lstep. GET. lstep.
    lstep. GET. lstep.
    eapply returns_step.
    { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                           | eapply bounds_false; exact Ek | exact Ek | destruct kv; reflexivity ]. }
    nz.
    destruct kv as [z|z|z|z| |kl|]; try discriminate.
    + (* null: skip *)
      lstep. lstep. lstep.
      eapply IH; try eassumption; lia.
    + destruct ((0 <=? i) && (i <? Z.of_nat (length ni))) eqn:Eb; [|discriminate].
      apply andb_true_iff in Eb as [Eb1 Eb2]. apply Z.leb_le in Eb1. apply Z.ltb_lt in Eb2.
      assert (Hc1 : iinc cnt 1 = cnt + 1) by (unfold iinc; apply wrap_id; [lia | unfold in_range, MAX_ARRAY in *; cbn; lia]).
      lstep. lstep. lstep. lstep. lstep.
      eapply returns_step.
      { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity
                                   | apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia | reflexivity ]. }
      nz. lstep. lstep.
      eapply (IH (upd h niA (OArr TInt (set_nth_z ni i (VInt cnt))))); try eassumption.
      * rewrite upd_other by congruence. exact Hm.
      * rewrite upd_other by congruence. exact HkA.
      * apply upd_same.
      * lia.
      * lia.
      * lia.
      * intros h' H1 H2. apply HK; [exact H1 | intros y Hy; rewrite H2 by exact Hy; apply upd_other; exact Hy].
Qed.


Lemma c2_loop : forall f h nx sts ini lk c rs m niA fs0 tA tbl ni n' T b r v P,
  h m = Some (OObj CIM fs0) -> cim_reads fs0 -> assoc "table" fs0 = Some (VRef tA) ->
  h tA = Some (OArr TInt tbl) -> h niA = Some (OArr TInt ni) -> niA <> m -> tA <> m -> tA <> niA ->
  Z.of_nat (length tbl) = T -> Z.to_nat (T - b) = f -> 0 <= b <= T -> T <= MAX_ARRAY ->
  c2 ni tbl b f = Some r ->
  (forall h', h' tA = Some (OArr TInt r) -> (forall y, y <> tA -> h' y = h y) ->
     returns cp (mdl e) {| ms_heap := h'; ms_next := nx; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := set_frame (cmframe 0 nil [VRef m; VTop; VTop; VTop; VTop; VTop])
                      (mkframe 82 nil [VRef m; VRef niA; VInt n'; VInt T; VTop; VTop]) :: c :: rs |} v P) ->
  returns cp (mdl e) {| ms_heap := h; ms_next := nx; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := set_frame (cmframe 0 nil [VRef m; VTop; VTop; VTop; VTop; VTop])
                      (mkframe 43 nil [VRef m; VRef niA; VInt n'; VInt b; VTop; VTop]) :: c :: rs |} v P.
Proof.
  induction f as [|f IH]; intros h nx sts ini lk c rs m niA fs0 tA tbl ni n' T b r v P
    Hm Hrd Ht HtA Hni Hnm Htm Htn HT Hf Hb Hmax Hr HK.
  - assert (b = T) by lia. subst b. cbn in Hr. injection Hr as <-.
    assert (E : (Z.of_nat (length tbl) <=? Z.of_nat (length tbl)) = true) by (apply Z.leb_le; lia).
    subst T. lstep. lstep. GET. ALEN. lstep.
    apply HK; [exact HtA | reflexivity].
  - assert (Hlt : (T <=? b) = false) by (apply Z.leb_gt; lia).
    assert (Hii : iinc b 1 = b + 1) by (unfold iinc; apply wrap_id; [lia | unfold in_range, MAX_ARRAY in *; cbn; lia]).
    cbn [c2] in Hr.
    destruct (nth_z tbl b) as [[x|z|z|z| |z|]|] eqn:Eb; try discriminate.
    assert (Hbb : ((b <? 0) || (Z.of_nat (length tbl) <=? b)) = false) by (eapply bounds_false; exact Eb).
    lstep. lstep. GET. ALEN. rewrite HT. lstep.
    lstep. GET. lstep.
    eapply returns_step.
    { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hbb | exact Eb | reflexivity ]. }
    nz. lstep.
    destruct (x =? -1) eqn:Ex.
    + lstep. lstep. lstep.
      eapply IH; try eassumption; lia.
    + destruct (nth_z ni x) as [[y|z|z|z| |z|]|] eqn:Ey; try discriminate.
      lstep. lstep. GET. lstep. lstep. lstep. GET. lstep.
      eapply returns_step.
      { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hbb | exact Eb | reflexivity ]. }
      nz.
      eapply returns_step.
      { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                             | eapply bounds_false; exact Ey | exact Ey | reflexivity ]. }
      nz.
      eapply returns_step.
      { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity
                                   | exact Hbb | reflexivity ]. }
      nz. lstep. lstep.
      apply (IH (upd h tA (OArr TInt (set_nth_z tbl b (VInt y)))) nx sts ini lk c rs m niA fs0 tA
                (set_nth_z tbl b (VInt y)) ni n' T (b + 1) r v P).
      * rewrite upd_other by congruence. exact Hm.
      * exact Hrd.
      * exact Ht.
      * apply upd_same.
      * rewrite upd_other by congruence. exact Hni.
      * exact Hnm.
      * exact Htm.
      * exact Htn.
      * rewrite snz_len. exact HT.
      * lia.
      * lia.
      * exact Hmax.
      * exact Hr.
      * intros h' H1 H2. apply HK; [exact H1 | intros y0 Hy; rewrite H2 by exact Hy; apply upd_other; exact Hy].
Qed.


Lemma c3_loop : forall f hc h0 nx sts ini lk c rs m niA tA fs0 kA vA cA ni ks vs cn u n' i x4 x5 ks' vs' cn' v P,
  hc m = Some (OObj CIM fs0) -> cim_reads fs0 -> assoc "keys" fs0 = Some (VRef kA) -> assoc "values" fs0 = Some (VRef vA) ->
  assoc "chainNext" fs0 = Some (VRef cA) -> assoc "usedSlots" fs0 = Some (VInt u) ->
  hc kA = Some (OArr (TRef STR) ks) -> hc vA = Some (OArr (TRef OBJ) vs) -> hc cA = Some (OArr TInt cn) ->
  hc niA = Some (OArr TInt ni) -> niA <> cA -> m <> niA -> m <> kA -> m <> vA -> m <> cA ->
  (forall y, y <> kA -> y <> vA -> y <> cA -> y <> niA -> y <> tA -> hc y = h0 y) ->
  Z.to_nat (u - i) = f -> 0 <= i <= u -> u <= MAX_ARRAY ->
  (match x4 with VTop | VInt _ => true | _ => false end) = true ->
  (match x5 with VTop | VInt _ => true | _ => false end) = true ->
  c3 h0 kA vA cA niA tA ni i f ks vs cn = Some (ks', vs', cn') ->
  (forall h' x4' x5', h' kA = Some (OArr (TRef STR) ks') -> h' vA = Some (OArr (TRef OBJ) vs') -> h' cA = Some (OArr TInt cn') ->
     (forall y, y <> kA -> y <> vA -> y <> cA -> h' y = hc y) ->
     (match x4' with VTop | VInt _ => true | _ => false end) = true ->
     (match x5' with VTop | VInt _ => true | _ => false end) = true ->
     returns cp (mdl e) {| ms_heap := h'; ms_next := nx; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := set_frame (cmframe 0 nil [VRef m; VTop; VTop; VTop; VTop; VTop])
                      (mkframe 167 nil [VRef m; VRef niA; VInt n'; VInt u; x4'; x5']) :: c :: rs |} v P) ->
  returns cp (mdl e) {| ms_heap := hc; ms_next := nx; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := set_frame (cmframe 0 nil [VRef m; VTop; VTop; VTop; VTop; VTop])
                      (mkframe 84 nil [VRef m; VRef niA; VInt n'; VInt i; x4; x5]) :: c :: rs |} v P.
Proof.
  induction f as [|f IH]; intros hc h0 nx sts ini lk c rs m niA tA fs0 kA vA cA ni ks vs cn u n' i x4 x5 ks' vs' cn' v P
    Hm Hrd Hk Hv Hc Hu HkA HvA HcA Hni Hnc Hmn Hmk Hmv Hmc Hagr Hf Hi Hmax Hx4 Hx5 Hr HK.
  - assert (i = u) by lia. subst i. cbn in Hr. injection Hr as <- <- <-.
    assert (E : (u <=? u) = true) by (apply Z.leb_le; lia).
    lstep. lstep. GET. lstep.
    apply HK; try assumption. reflexivity.
  - assert (Hlt : (u <=? i) = false) by (apply Z.leb_gt; lia).
    assert (Hii : iinc i 1 = i + 1) by (unfold iinc; apply wrap_id; [lia | unfold in_range, MAX_ARRAY in *; cbn; lia]).
    assert (Hkv : kA <> vA) by (intro E; subst; rewrite HkA in HvA; discriminate).
    assert (Hkc : kA <> cA) by (intro E; subst; rewrite HkA in HcA; discriminate).
    assert (Hvc : vA <> cA) by (intro E; subst; rewrite HvA in HcA; discriminate).
    assert (Hkn : kA <> niA) by (intro E; subst; rewrite HkA in Hni; discriminate).
    assert (Hvn : vA <> niA) by (intro E; subst; rewrite HvA in Hni; discriminate).
    cbn [c3] in Hr.
    destruct (nth_z ks i) as [kv|] eqn:Ek; [|discriminate].
    assert (Hik : ((i <? 0) || (Z.of_nat (length ks) <=? i)) = false) by (eapply bounds_false; exact Ek).
    lstep. lstep. GET. lstep.
    lstep. GET. lstep.
    eapply returns_step.
    { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                           | exact Hik | exact Ek | destruct kv; reflexivity ]. }
    nz.
    destruct kv as [z|z|z|z| |kl|]; try discriminate.
    + (* empty slot: skip *)
      lstep. lstep. lstep.
      apply (IH hc h0 nx sts ini lk c rs m niA tA fs0 kA vA cA ni ks vs cn u n' (i + 1) x4 x5 ks' vs' cn' v P);
        try assumption; [ clear -Hf; lia | clear -Hi Hlt; lia ].
    + destruct (nth_z ni i) as [[j|z|z|z| |z|]|] eqn:Ej; try discriminate.
      destruct (nth_z cn i) as [[nxi|z|z|z| |z|]|] eqn:En; try discriminate.
      destruct (nth_z vs i) as [vv|] eqn:Ev; try discriminate.
      destruct (h0 kl) as [[| | ku | | |]|] eqn:Ekl; try discriminate.
      set (ny := if nxi =? -1 then Some (-1) else match nth_z ni nxi with Some (VInt y) => Some y | _ => None end) in Hr.
      destruct ny as [y|] eqn:Eny; [|discriminate].
      destruct ((0 <=? j) && (j <? Z.of_nat (length cn)) && (j <? Z.of_nat (length ks)) && (j <? Z.of_nat (length vs))
                && vok_b h0 vv && not_in4 kA vA cA niA tA vv && not_in4 kA vA cA niA tA (VRef kl)) eqn:Eok; [|discriminate].
      repeat rewrite andb_true_iff in Eok.
      destruct Eok as ((((((Ej0 & Ejc) & Ejk) & Ejv) & Evok) & Evn) & Ekn).
      apply Z.leb_le in Ej0. apply Z.ltb_lt in Ejc. apply Z.ltb_lt in Ejk. apply Z.ltb_lt in Ejv.
      assert (Hkl : kl <> kA /\ kl <> vA /\ kl <> cA /\ kl <> niA /\ kl <> tA).
      { unfold not_in4 in Ekn. repeat rewrite andb_true_iff in Ekn. destruct Ekn as ((((A1 & A2) & A3) & A4) & A5).
        apply negb_true_iff, Z.eqb_neq in A1, A2, A3, A4, A5. tauto. }
      destruct Hkl as (Hkl1 & Hkl2 & Hkl3 & Hkl4 & Hkl5).
      assert (Hkl0 : hc kl = Some (OStr ku)) by (rewrite Hagr by assumption; exact Ekl).
      assert (Hjc : ((j <? 0) || (Z.of_nat (length cn) <=? j)) = false) by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
      assert (Hjk : ((j <? 0) || (Z.of_nat (length ks) <=? j)) = false) by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
      assert (Hjv : ((j <? 0) || (Z.of_nat (length vs) <=? j)) = false) by (apply orb_false_iff; split; [apply Z.ltb_ge | apply Z.leb_gt]; lia).
      assert (Hiv : ((i <? 0) || (Z.of_nat (length vs) <=? i)) = false) by (eapply bounds_false; exact Ev).
      (* 101: j = newIndex[i] *)
      lstep. lstep. lstep.
      eapply returns_step.
      { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                             | eapply bounds_false; exact Ej | exact Ej | reflexivity ]. }
      nz. lstep.
      (* 106: next = chainNext[i] *)
      lstep. GET. lstep.
      eapply returns_step.
      { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                             | eapply bounds_false; exact En | exact En | reflexivity ]. }
      nz. lstep.
      (* 114: chainNext[j] = next == -1 ? -1 : newIndex[next] *)
      lstep. GET. lstep. lstep. lstep.
      destruct (nxi =? -1) eqn:Enx.
      * injection Eny as <-.
        lstep. lstep. lstep.
        eapply returns_step.
        { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity
                                     | exact Hjc | reflexivity ]. }
        nz.
        (* 135: keys[j] = keys[i] *)
        lstep. GET. lstep. lstep. GET. lstep.
        eapply returns_step.
        { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                               | exact Hik | exact Ek | reflexivity ]. }
        nz.
        eapply returns_step.
        { eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hjk | hp
                                    | reflexivity | apply asg_str | reflexivity ]. }
        nz.
        (* 148: values[j] = values[i] *)
        lstep. GET. lstep. lstep. GET. lstep.
        assert (Hvv : (match vv with VNull | VRef _ => true | _ => false end) = true) by (destruct vv; try discriminate Evok; reflexivity).
        eapply returns_step.
        { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                               | exact Hiv | exact Ev | destruct vv; try discriminate Hvv; reflexivity ]. }
        nz.
        destruct vv as [z|z|z|z| |vl|]; try discriminate Hvv.
        -- eapply returns_step.
           { eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hjv | reflexivity ]. }
           nz. lstep. lstep.
           apply (IH _ h0 nx sts ini lk c rs m niA tA fs0 kA vA cA ni (set_nth_z ks j (VRef kl)) (set_nth_z vs j VNull)
                     (set_nth_z cn j (VInt (-1))) u n' (i + 1) (VInt j) (VInt nxi) ks' vs' cn' v P);
             [ hfact | exact Hrd | exact Hk | exact Hv | exact Hc | exact Hu | hfact | hfact | hfact | hfact
             | exact Hnc | exact Hmn | exact Hmk | exact Hmv | exact Hmc
             | intros y0 H1 H2 H3 H4 H5; repeat rewrite upd_other by congruence; apply Hagr; assumption
             | clear -Hf; lia | clear -Hi Hlt; lia | exact Hmax | reflexivity | reflexivity | exact Hr
             | intros h' x4' x5' H1 H2 H3 H4 H5 H6; apply HK; try assumption;
               intros y0 Y1 Y2 Y3; rewrite H4 by assumption; repeat rewrite upd_other by congruence; reflexivity ].
        -- unfold vok_b in Evok. destruct (h0 vl) as [o|] eqn:Eo; [|discriminate].
           destruct (assignable cp 64 (runtime_type o) OBJ) as [[|]|] eqn:Ea; try discriminate.
           unfold not_in4 in Evn. repeat rewrite andb_true_iff in Evn. destruct Evn as ((((B1 & B2) & B3) & B4) & B5).
           apply negb_true_iff, Z.eqb_neq in B1, B2, B3, B4, B5.
           assert (Hvl0 : hc vl = Some o) by (rewrite Hagr by assumption; exact Eo).
           eapply returns_step.
           { eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hjv | hp
                                       | reflexivity | exact Ea | reflexivity ]. }
           nz. lstep. lstep.
           apply (IH _ h0 nx sts ini lk c rs m niA tA fs0 kA vA cA ni (set_nth_z ks j (VRef kl)) (set_nth_z vs j (VRef vl))
                     (set_nth_z cn j (VInt (-1))) u n' (i + 1) (VInt j) (VInt nxi) ks' vs' cn' v P);
             [ hfact | exact Hrd | exact Hk | exact Hv | exact Hc | exact Hu | hfact | hfact | hfact | hfact
             | exact Hnc | exact Hmn | exact Hmk | exact Hmv | exact Hmc
             | intros y0 H1 H2 H3 H4 H5; repeat rewrite upd_other by congruence; apply Hagr; assumption
             | clear -Hf; lia | clear -Hi Hlt; lia | exact Hmax | reflexivity | reflexivity | exact Hr
             | intros h' x4' x5' H1 H2 H3 H4 H5 H6; apply HK; try assumption;
               intros y0 Y1 Y2 Y3; rewrite H4 by assumption; repeat rewrite upd_other by congruence; reflexivity ].
      * destruct (nth_z ni nxi) as [[y'|z|z|z| |z|]|] eqn:Ey; try discriminate Eny. injection Eny as <-.
        lstep. lstep. lstep.
        eapply returns_step.
        { eapply mstep_xaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                               | eapply bounds_false; exact Ey | exact Ey | reflexivity ]. }
        nz.
        eapply returns_step.
        { eapply mstep_xastore_prim; [ reflexivity | reflexivity | reflexivity | reflexivity | hp | reflexivity
                                     | exact Hjc | reflexivity ]. }
        nz.
        lstep. GET. lstep. lstep. GET. lstep.
        eapply returns_step.
        { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                               | exact Hik | exact Ek | reflexivity ]. }
        nz.
        eapply returns_step.
        { eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hjk | hp
                                    | reflexivity | apply asg_str | reflexivity ]. }
        nz.
        lstep. GET. lstep. lstep. GET. lstep.
        assert (Hvv : (match vv with VNull | VRef _ => true | _ => false end) = true) by (destruct vv; try discriminate Evok; reflexivity).
        eapply returns_step.
        { eapply mstep_aaload; [ reflexivity | reflexivity | reflexivity | hp | reflexivity
                               | exact Hiv | exact Ev | destruct vv; try discriminate Hvv; reflexivity ]. }
        nz.
        destruct vv as [z|z|z|z| |vl|]; try discriminate Hvv.
        -- eapply returns_step.
           { eapply mstep_aastore_null; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hjv | reflexivity ]. }
           nz. lstep. lstep.
           apply (IH _ h0 nx sts ini lk c rs m niA tA fs0 kA vA cA ni (set_nth_z ks j (VRef kl)) (set_nth_z vs j VNull)
                     (set_nth_z cn j (VInt y')) u n' (i + 1) (VInt j) (VInt nxi) ks' vs' cn' v P);
             [ hfact | exact Hrd | exact Hk | exact Hv | exact Hc | exact Hu | hfact | hfact | hfact | hfact
             | exact Hnc | exact Hmn | exact Hmk | exact Hmv | exact Hmc
             | intros y0 H1 H2 H3 H4 H5; repeat rewrite upd_other by congruence; apply Hagr; assumption
             | clear -Hf; lia | clear -Hi Hlt; lia | exact Hmax | reflexivity | reflexivity | exact Hr
             | intros h' x4' x5' H1 H2 H3 H4 H5 H6; apply HK; try assumption;
               intros y0 Y1 Y2 Y3; rewrite H4 by assumption; repeat rewrite upd_other by congruence; reflexivity ].
        -- unfold vok_b in Evok. destruct (h0 vl) as [o|] eqn:Eo; [|discriminate].
           destruct (assignable cp 64 (runtime_type o) OBJ) as [[|]|] eqn:Ea; try discriminate.
           unfold not_in4 in Evn. repeat rewrite andb_true_iff in Evn. destruct Evn as ((((B1 & B2) & B3) & B4) & B5).
           apply negb_true_iff, Z.eqb_neq in B1, B2, B3, B4, B5.
           assert (Hvl0 : hc vl = Some o) by (rewrite Hagr by assumption; exact Eo).
           eapply returns_step.
           { eapply mstep_aastore_ref; [ reflexivity | reflexivity | reflexivity | hp | reflexivity | exact Hjv | hp
                                       | reflexivity | exact Ea | reflexivity ]. }
           nz. lstep. lstep.
           apply (IH _ h0 nx sts ini lk c rs m niA tA fs0 kA vA cA ni (set_nth_z ks j (VRef kl)) (set_nth_z vs j (VRef vl))
                     (set_nth_z cn j (VInt y')) u n' (i + 1) (VInt j) (VInt nxi) ks' vs' cn' v P);
             [ hfact | exact Hrd | exact Hk | exact Hv | exact Hc | exact Hu | hfact | hfact | hfact | hfact
             | exact Hnc | exact Hmn | exact Hmk | exact Hmv | exact Hmc
             | intros y0 H1 H2 H3 H4 H5; repeat rewrite upd_other by congruence; apply Hagr; assumption
             | clear -Hf; lia | clear -Hi Hlt; lia | exact Hmax | reflexivity | reflexivity | exact Hr
             | intros h' x4' x5' H1 H2 H3 H4 H5 H6; apply HK; try assumption;
               intros y0 Y1 Y2 Y3; rewrite H4 by assumption; repeat rewrite upd_other by congruence; reflexivity ].
Qed.


Definition fillO_desc := "([Ljava/lang/Object;IILjava/lang/Object;)V"%string.
Lemma rf_fillO : resolve_full cp "java/util/Arrays" "fill" fillO_desc = None. Proof. vm_compute. reflexivity. Qed.
Lemma err_arr2 : forall st, erroneous cp 64 st "java/util/Arrays" = false. Proof. intros. vm_compute. reflexivity. Qed.
Lemma in_arr2 : forall st, init_needed cp 64 st "java/util/Arrays" = None. Proof. intros. vm_compute. reflexivity. Qed.

Lemma m_fill_null : forall s a X es f t, ms_heap s a = Some (OArr (TRef X) es) -> 0 <= f <= t -> t <= Z.of_nat (length es) ->
  jdk_model cp e "java/util/Arrays" "fill" fillO_desc [VRef a; VInt f; VInt t; VNull] s =
  MOk None (set_heap s a (OArr (TRef X) (fill_null es f t))).
Proof.
  intros s a X es f t H Hf Ht. unfold jdk_model. cbv -[ms_heap set_heap firstn skipn repeat app slen_v Z.ltb Z.to_nat Z.sub].
  rewrite H.
  replace (t <? f) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (f <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (slen_v es <? t) with false by (symmetry; apply Z.ltb_ge; unfold slen_v; lia).
  reflexivity.
Qed.

Definition cm_mr : methodref := {| mr_class := CIM; mr_name := "compactRemovedSlots"; mr_desc := "()V"; mr_interface := false |}.

(** Calling compactRemovedSlots() from any frame. *)
Lemma call_compact : forall h nx sts ini lk top rest nxt r m tA kA vA cA sz u thr af tbl ks vs cn n' ni tbl' ks' vs' cn' v P,
  fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) = Some (Invoke InvVirtual cm_mr, nxt) ->
  f_stack (cf_frame top) = VRef m :: r ->
  h m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af)) ->
  h tA = Some (OArr TInt tbl) -> h kA = Some (OArr (TRef STR) ks) ->
  h vA = Some (OArr (TRef OBJ) vs) -> h cA = Some (OArr TInt cn) -> tA <> cA ->
  m < nx -> tA < nx -> kA < nx -> vA < nx -> cA < nx ->
  0 <= u <= MAX_ARRAY -> Z.of_nat (length tbl) <= MAX_ARRAY ->
  c1 ks 0 (Z.to_nat u) 0 (repeat (VInt 0) (Z.to_nat u)) = Some (n', ni) ->
  c2 ni tbl 0 (Z.to_nat (Z.of_nat (length tbl))) = Some tbl' ->
  c3 h kA vA cA nx tA ni 0 (Z.to_nat u) ks vs cn = Some (ks', vs', cn') ->
  0 <= n' <= u -> u <= Z.of_nat (length ks') -> u <= Z.of_nat (length vs') ->
  (forall h', h' m = Some (OObj CIM (cim_fields tA kA vA cA sz n' thr af)) ->
     h' nx = Some (OArr TInt ni) -> h' tA = Some (OArr TInt tbl') ->
     h' kA = Some (OArr (TRef STR) (fill_null ks' n' u)) -> h' vA = Some (OArr (TRef OBJ) (fill_null vs' n' u)) ->
     h' cA = Some (OArr TInt cn') ->
     (forall y, y <> m -> y <> nx -> y <> tA -> y <> kA -> y <> vA -> y <> cA -> h' y = h y) ->
     returns cp (mdl e) {| ms_heap := h'; ms_next := nx + 1; ms_statics := sts; ms_inited := ini; ms_locks := lk;
       ms_frames := set_resume (set_frame top (mkframe nxt r (f_locals (cf_frame top)))) None :: rest |} v P) ->
  returns cp (mdl e) {| ms_heap := h; ms_next := nx; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := top :: rest |} v P.
Proof.
  intros h nx sts ini lk top rest nxt r m tA kA vA cA sz u thr af tbl ks vs cn n' ni tbl' ks' vs' cn' v P
         Hf Hst Hm HtA HkA HvA HcA Htc Hnm Hnt Hnk Hnv Hnc Hu HT Hc1 Hc2 Hc3 Hn' Hlk Hlv HK.
  assert (Hmt : m <> tA) by (intro E; subst; rewrite Hm in HtA; discriminate).
  assert (Hmk : m <> kA) by (intro E; subst; rewrite Hm in HkA; discriminate).
  assert (Hmv : m <> vA) by (intro E; subst; rewrite Hm in HvA; discriminate).
  assert (Hmc : m <> cA) by (intro E; subst; rewrite Hm in HcA; discriminate).
  assert (Hkt : kA <> tA) by (intro E; subst; rewrite HkA in HtA; discriminate).
  assert (Hkv : kA <> vA) by (intro E; subst; rewrite HkA in HvA; discriminate).
  assert (Hkc : kA <> cA) by (intro E; subst; rewrite HkA in HcA; discriminate).
  assert (Hvt : vA <> tA) by (intro E; subst; rewrite HvA in HtA; discriminate).
  assert (Hvc : vA <> cA) by (intro E; subst; rewrite HvA in HcA; discriminate).
  assert (Hxm : nx <> m) by lia. assert (Hxt : nx <> tA) by lia. assert (Hxk : nx <> kA) by lia.
  assert (Hxv : nx <> vA) by lia. assert (Hxc : nx <> cA) by lia.
  set (c := set_resume (set_frame top (mkframe (f_pc (cf_frame top)) r (f_locals (cf_frame top)))) (Some nxt)).
  eapply returns_step.
  { erewrite mstep_invoke; [ | reflexivity | exact Hf | reflexivity | rewrite Hst; reflexivity ].
    cbn [app]. erewrite do_invoke_obj_enter; [ | left; reflexivity | exact Hm | exact rf_cm | reflexivity ].
    unfold enter. cbn -[set_resume set_frame]. reflexivity. }
  change (returns cp (mdl e) {| ms_heap := h; ms_next := nx; ms_statics := sts; ms_inited := ini; ms_locks := lk;
     ms_frames := set_frame (cmframe 0 nil [VRef m; VTop; VTop; VTop; VTop; VTop])
                    (mkframe 0 nil [VRef m; VTop; VTop; VTop; VTop; VTop]) :: c :: rest |} v P).
  lstep. GET.
  eapply returns_step.
  { eapply mstep_newarray; [ reflexivity | reflexivity | reflexivity | reflexivity
                           | apply Z.ltb_ge; lia | apply Z.ltb_ge; lia | reflexivity ]. }
  nz. lstep. lstep. lstep. lstep. lstep.
  eapply (c1_loop (Z.to_nat (u - 0)) (upd h nx (OArr TInt (repeat (VInt 0) (Z.to_nat u)))) (nx + 1) sts ini lk c rest m nx
            (cim_fields tA kA vA cA sz u thr af) kA ks u (repeat (VInt 0) (Z.to_nat u)) 0 0 (n', ni) v P);
    [ hfact | apply cim_fields_reads | reflexivity | reflexivity | hfact | apply upd_same | exact Hxm | exact Hxk | reflexivity | lia | lia | lia
    | replace (u - 0) with u by lia; exact Hc1 | ].
  cbn [fst snd]. intros h1 H1a H1b.
  lstep. lstep.
  eapply (c2_loop (Z.to_nat (Z.of_nat (length tbl) - 0)) h1 (nx + 1) sts ini lk c rest m nx
            (cim_fields tA kA vA cA sz u thr af) tA tbl ni n' (Z.of_nat (length tbl)) 0 tbl' v P);
    [ rewrite H1b by congruence; hfact | apply cim_fields_reads | reflexivity | rewrite H1b by congruence; hfact | exact H1a
    | exact Hxm | apply not_eq_sym; exact Hmt | apply not_eq_sym; exact Hxt | reflexivity | reflexivity | lia | exact HT
    | replace (Z.of_nat (length tbl) - 0) with (Z.of_nat (length tbl)) by lia; exact Hc2 | ].
  intros h2 H2a H2b.
  lstep. lstep.
  eapply (c3_loop (Z.to_nat (u - 0)) h2 h (nx + 1) sts ini lk c rest m nx tA (cim_fields tA kA vA cA sz u thr af)
            kA vA cA ni ks vs cn u n' 0 VTop VTop ks' vs' cn' v P);
    [ rewrite H2b, H1b by congruence; hfact | apply cim_fields_reads | reflexivity | reflexivity | reflexivity | reflexivity
    | rewrite H2b, H1b by congruence; hfact | rewrite H2b, H1b by congruence; hfact | rewrite H2b, H1b by congruence; hfact
    | rewrite H2b by congruence; exact H1a | congruence | congruence | congruence | congruence | congruence
    | intros y Y1 Y2 Y3 Y4 Y5; rewrite H2b, H1b by congruence; apply upd_other; congruence
    | reflexivity | lia | lia | reflexivity | reflexivity | replace (u - 0) with u by lia; exact Hc3 | ].
  intros h3 x4 x5 H3a H3b H3c H3d H3x4 H3x5.
  assert (Hc2' : cat2 x4 = false /\ cat2 x5 = false) by (destruct x4, x5; try discriminate; split; reflexivity).
  assert (H3m : h3 m = Some (OObj CIM (cim_fields tA kA vA cA sz u thr af))) by (rewrite H3d, H2b, H1b by congruence; hfact).
  lstep. GET. lstep. lstep. GET. lstep.
  eapply returns_step.
  { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
    eapply do_invoke_static_model;
      [ apply err_arr2 | apply in_arr2 | exact rf_fillO | unfold mdl; apply m_fill_null; [ hp | lia | lia ] | reflexivity ]. }
  unfold set_heap. nz. lstep. GET. lstep. lstep. GET. lstep.
  eapply returns_step.
  { erewrite mstep_invoke; [ | reflexivity | reflexivity | reflexivity | reflexivity ]. cbn [app].
    eapply do_invoke_static_model;
      [ apply err_arr2 | apply in_arr2 | exact rf_fillO | unfold mdl; apply m_fill_null; [ hp | lia | lia ] | reflexivity ]. }
  unfold set_heap. nz. lstep. lstep. PUT.
  eapply returns_step.
  { eapply mstep_return_to; [ reflexivity | reflexivity | reflexivity | reflexivity | cbn; reflexivity | reflexivity ]. }
  nz.
  apply HK.
  - hfact.
  - repeat rewrite upd_other by congruence. rewrite H3d by congruence. rewrite H2b by congruence. exact H1a.
  - repeat rewrite upd_other by congruence. rewrite H3d by congruence. exact H2a.
  - repeat first [ rewrite upd_same | rewrite upd_other by congruence ]. reflexivity.
  - repeat first [ rewrite upd_same | rewrite upd_other by congruence ]. reflexivity.
  - repeat rewrite upd_other by congruence. exact H3c.
  - intros y Y1 Y2 Y3 Y4 Y5 Y6. repeat rewrite upd_other by congruence.
    rewrite H3d, H2b, H1b by congruence. apply upd_other. congruence.
Qed.

End Compact.

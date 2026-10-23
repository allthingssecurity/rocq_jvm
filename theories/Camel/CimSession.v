(** * CaseInsensitiveMap (fix): every sequence of get / put / remove calls.

    The fixed class behaves like an insertion-ordered map whose keys compare ignoring case,
    and its slot arrays stay bounded for the whole sequence, however many keys are put
    and removed: they never grow past [max(initial length, 3 * threshold)].

    Not covered: [resize()] (the arrays are rebuilt with a float threshold); the theorems
    assume the map holds fewer than [threshold] entries whenever a new key is put. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import CimProg CimCalls CimPut CimRemove CimAbs CimAbs2 CimMap CimMap2 CimMap3.
Import ListNotations.
Open Scope Z_scope.

Section Session.
Variable e : jenv.
Variable good : list Z -> Prop.
Hypothesis eq_sym : forall a b, good a -> good b -> eqic e a b = eqic e b a.
Hypothesis eq_trans : forall a b c, good a -> good b -> good c -> eqic e a b = true -> eqic e b c = true -> eqic e a c = true.
Hypothesis eq_hash : forall a b, good a -> good b -> eqic e a b = true -> cih_spec e a = cih_spec e b.

(** The abstract put: replace the value of the entry whose key equals [q] ignoring case
    (keeping that entry's key and place), or add the entry at the end. *)
Definition a_put (h : heap) (A : list (Z * value)) (k : Z) (q : list Z) (v : value) : list (Z * value) :=
  if a_mem e h A q then a_set e h A q v else app A [(k, v)].

Lemma a_get_absent : forall h A q, a_mem e h A q = false -> a_get e h A q = VNull.
Proof.
  intros h A q. induction A as [|[k w] r IH]; intros H; [reflexivity|]. cbn [a_mem a_get] in *.
  destruct (kunits h k) as [u|]; [|apply IH; exact H].
  destruct (eqic e u q); [discriminate|]. apply IH. exact H.
Qed.

Lemma a_set_in : forall h A q v kk vv, In (kk, vv) (a_set e h A q v) -> In (kk, vv) A \/ vv = v.
Proof.
  intros h A q v kk vv. induction A as [|[k w] r IH]; intros H; [destruct H|]. cbn [a_set] in H.
  destruct (kunits h k) as [u|]; [destruct (eqic e u q)|].
  - destruct H as [H|H]; [injection H as <- <-; right; reflexivity | left; right; exact H].
  - destruct H as [H|H]; [left; left; exact H | destruct (IH H); [left; right; assumption | right; assumption]].
  - destruct H as [H|H]; [left; left; exact H | destruct (IH H); [left; right; assumption | right; assumption]].
Qed.

Lemma a_remove_in : forall h A q kk vv, In (kk, vv) (a_remove e h A q) -> In (kk, vv) A.
Proof.
  intros h A q kk vv. induction A as [|[k w] r IH]; intros H; [destruct H|]. cbn [a_remove] in H.
  destruct (kunits h k) as [u|]; [destruct (eqic e u q)|].
  - right. exact H.
  - destruct H as [H|H]; [left; exact H | right; apply IH; exact H].
  - destruct H as [H|H]; [left; exact H | right; apply IH; exact H].
Qed.

Lemma entries_length : forall ks vs S, length (entries ks vs S) = length S.
Proof. intros. unfold entries. apply map_length. Qed.

(** The invariant kept between calls: the representation, nothing allocated at or above the
    allocation pointer, the stored values are nulls or non-array objects, and the slot arrays
    have at least two slots. *)
Definition cim_inv (h : heap) (n m : Z) (A : list (Z * value)) (K : nat) (thr : Z) : Prop :=
  cim_rep e good h m A K thr /\ fresh h n /\ vals_ok h m A /\ (2 <= K)%nat.

Lemma inv_frame : forall h h' n n' m A' K' thr, fresh h n -> hframe h h' m n n' ->
  (forall kk vv, In (kk, vv) A' -> vgood h m vv) -> cim_rep e good h' m A' K' thr -> (2 <= K')%nat ->
  cim_inv h' n' m A' K' thr.
Proof.
  intros h h' n n' m A' K' thr Hfr Hf Hvals Hrep HK. destruct (Hf Hfr) as (Hpl & Hfr').
  refine (conj Hrep (conj Hfr' (conj _ HK))).
  intros kk vv H. apply (vgood_frame h h' m vv Hpl). exact (Hvals kk vv H).
Qed.

(** ** put, whatever path it takes *)
Theorem put_map : forall h n sts ini lk m k ku v A K thr,
  cim_inv h n m A K thr -> 3 * thr <= MAX_ARRAY -> thr <= INT_MAX ->
  h k = Some (OStr ku) -> slen ku <= INT_MAX -> good ku ->
  erroneous cp 64 sts CIM = false -> init_needed cp 64 ini CIM = None -> assoc KNOWN sts = Some VNull ->
  vgood h m v -> (a_mem e h A ku = true \/ Z.of_nat (length A) < thr) ->
  returns cp (mdl e) {| ms_heap := h; ms_next := n; ms_statics := sts; ms_inited := ini; ms_locks := lk;
                         ms_frames := [put_frame m k v] |}
    (Some (a_get e h A ku))
    (fun s' => exists K', cim_inv (ms_heap s') (ms_next s') m (a_put h A k ku v) K' thr /\
       (K' = K \/ (Z.of_nat K' = Z.of_nat K + Z.of_nat K / 2 /\ Z.of_nat K / 2 < Z.of_nat (length A) /\
                   Z.of_nat (length A) < thr)) /\
       same_strings h (ms_heap s') /\ ms_statics s' = sts /\ ms_inited s' = ini).
Proof.
  intros h n sts ini lk m k ku v A K thr (Hrep & Hfr & Hvals & HK2) H3 Hthr' Hk Hmax Hg He Hi HKn Hv Hcase.
  assert (Hvok : vok h v) by (eapply vgood_vok; eauto).
  assert (HvA' : forall kk vv, In (kk, vv) (app A [(k, v)]) -> vgood h m vv).
  { intros kk vv Hin. apply in_app_or in Hin as [Hin|[Hin|[]]]; [exact (Hvals kk vv Hin) | injection Hin as <- <-; exact Hv]. }
  unfold a_put. destruct (a_mem e h A ku) eqn:Em.
  - (* the key is there: its value is replaced *)
    eapply returns_weaken.
    { apply (put_present_map e good eq_sym eq_trans eq_hash h n sts ini lk m k ku v A K thr); assumption. }
    intros s' (P1 & P2 & P3 & P4 & P5 & P6). exists K. refine (conj _ (conj (or_introl eq_refl) (conj P2 (conj P5 P6)))).
    apply (inv_frame h (ms_heap s') n (ms_next s') m); try assumption.
    intros kk vv Hin. destruct (a_set_in h A ku v kk vv Hin) as [H|<-]; [exact (Hvals kk vv H) | exact Hv].
  - (* a new key *)
    rewrite (a_get_absent h A ku Em).
    assert (Hlt : Z.of_nat (length A) < thr) by (destruct Hcase; [congruence | assumption]).
    destruct (rep_elim e good h m A K thr Hrep)
      as (tA & kA & vA & cA & sz & u & af & tbl & ks & vs & cn & pw & Hm & HtA & HkA & HvA & HcA & Htc & Hrl & Hsz & HA).
    pose proof Hrl as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    subst A.
    rewrite entries_length in Hlt. rewrite entries_length.
    assert (Hszt : sz < thr) by lia.
    assert (Hvd : match v with VRef vl => vl <> m /\ (forall t es, h vl <> Some (OArr t es)) | _ => True end).
    { destruct v as [z|z|z|z| |vl|]; try exact I. destruct Hv as ((Hlm & o & Ho & Hna) & _).
      split; [exact Hlm | intros t es E; rewrite Ho in E; injection E as E; exact (Hna t es E)]. }
    destruct (Z_lt_le_dec u (Z.of_nat K)) as [Hfree|Hfull].
    + (* a free slot at the end *)
      assert (Hlv : length vs = length ks) by congruence.
      assert (Hlc : length cn = length ks) by congruence.
      assert (HKm : Z.of_nat (length ks) <= MAX_ARRAY) by (rewrite R3; exact R6).
      assert (Hnull : forall q, u <= q < Z.of_nat (length ks) -> nth_z ks q = Some VNull) by (rewrite R3; exact R9).
      assert (Hfree' : u < Z.of_nat (length ks)) by (rewrite R3; exact Hfree).
      assert (Hu0 : 0 <= u) by lia.
      eapply returns_weaken.
      { apply (put_new_free_map e good eq_sym eq_hash h n sts ini lk m k ku v tA kA vA cA sz u af tbl ks vs cn pw thr);
          assumption. }
      intros s' (P1 & P2 & P3 & P4 & P5 & P6). rewrite R3 in P1.
      exists K. refine (conj _ (conj (or_introl eq_refl) (conj _ (conj P5 P6)))).
      * apply (inv_frame h (ms_heap s') n (ms_next s') m); assumption.
      * intros y u0. symmetry. apply P2.
    + assert (Hu : u = Z.of_nat K) by lia.
      destruct (Z_le_gt_dec sz (Z.of_nat K / 2)) as [Hhalf|Hhalf].
      * (* compaction *)
        assert (HK1 : (1 <= K)%nat) by lia.
        eapply returns_weaken.
        { apply (put_compact_map e good eq_sym eq_hash h n sts ini lk m k ku v tA kA vA cA sz u af tbl ks vs cn pw thr K);
            assumption. }
        intros s' (P1 & P2 & P3 & P4 & P5).
        exists K. refine (conj _ (conj (or_introl eq_refl) (conj _ (conj P4 P5)))).
        -- apply (inv_frame h (ms_heap s') n (ms_next s') m); assumption.
        -- intros y u0. symmetry. apply P2.
      * (* growth *)
        assert (HKm : Z.of_nat K + Z.of_nat K / 2 <= MAX_ARRAY) by (clear -Hhalf Hszt H3; Z.div_mod_to_equations; lia).
        assert (Hhalf' : Z.of_nat K / 2 < sz) by lia.
        eapply returns_weaken.
        { apply (put_grow_map e good eq_sym eq_hash h n sts ini lk m k ku v tA kA vA cA sz u af tbl ks vs cn pw thr K);
            assumption. }
        intros s' (P1 & P2 & P3 & P4 & P5).
        assert (HK' : (2 <= Z.to_nat (Z.of_nat K + Z.of_nat K / 2))%nat)
          by (pose proof (Z.div_pos (Z.of_nat K) 2 ltac:(lia) ltac:(lia)); lia).
        exists (Z.to_nat (Z.of_nat K + Z.of_nat K / 2)).
        refine (conj _ (conj (or_intror _) (conj _ (conj P4 P5)))).
        -- apply (inv_frame h (ms_heap s') n (ms_next s') m); assumption.
        -- pose proof (Z.div_pos (Z.of_nat K) 2 ltac:(lia) ltac:(lia)). split; [lia | split; lia].
        -- intros y u0. symmetry. apply P2.
Qed.

(** ** Every sequence of calls *)

Inductive cim_op := CGet (k : Z) | CPut (k : Z) (v : value) | CRemove (k : Z).

(** A key argument: a string, of a case-insensitive kind the assumptions cover. *)
Definition key_ok (h : heap) (k : Z) (ku : list Z) : Prop :=
  h k = Some (OStr ku) /\ good ku /\ slen ku <= INT_MAX.

(** The map holds [A], and its slot arrays have at most [B] slots. *)
Definition bounded (s : mstate) (m : Z) (A : list (Z * value)) (thr B : Z) : Prop :=
  exists K, cim_rep e good (ms_heap s) m A K thr /\ Z.of_nat K <= B.

(** [session ops m thr B A s]: starting from [s], where the map [m] holds [A], each call of
    the sequence returns what the abstract map says, after it the map holds the abstract
    result with at most [B] slots, and the rest of the sequence behaves the same:
    - [get(k)] returns the value of the entry whose key equals [k] ignoring case, or null;
    - [put(k, v)] returns the old value (or null), and replaces it, or adds [(k, v)] at the end;
    - [remove(k)] returns the old value (or null), and drops that entry. *)
Fixpoint session (ops : list cim_op) (m thr B : Z) (A : list (Z * value)) (s : mstate) : Prop :=
  match ops with
  | [] => True
  | CGet k :: r =>
      forall ku, key_ok (ms_heap s) k ku ->
      returns cp (mdl e) (with_frames s [get_frame m k]) (Some (a_get e (ms_heap s) A ku))
        (fun s' => bounded s' m A thr B /\ session r m thr B A s')
  | CPut k v :: r =>
      forall ku, key_ok (ms_heap s) k ku -> vgood (ms_heap s) m v ->
      (a_mem e (ms_heap s) A ku = true \/ Z.of_nat (length A) < thr) ->
      returns cp (mdl e) (with_frames s [put_frame m k v]) (Some (a_get e (ms_heap s) A ku))
        (fun s' => bounded s' m (a_put (ms_heap s) A k ku v) thr B /\
                   session r m thr B (a_put (ms_heap s) A k ku v) s')
  | CRemove k :: r =>
      forall ku, key_ok (ms_heap s) k ku ->
      returns cp (mdl e) (with_frames s [rm_frame m k]) (Some (a_get e (ms_heap s) A ku))
        (fun s' => bounded s' m (a_remove e (ms_heap s) A ku) thr B /\
                   session r m thr B (a_remove e (ms_heap s) A ku) s')
  end.

(** What the calls need from the rest of the program: the class is initialised. *)
Definition cim_env (s : mstate) : Prop :=
  erroneous cp 64 (ms_statics s) CIM = false /\ init_needed cp 64 (ms_inited s) CIM = None /\
  assoc KNOWN (ms_statics s) = Some VNull.

Theorem session_ok : forall ops m thr B A K s,
  cim_inv (ms_heap s) (ms_next s) m A K thr -> cim_env s ->
  Z.of_nat K <= B -> 3 * thr <= B -> 3 * thr <= MAX_ARRAY -> thr <= INT_MAX ->
  session ops m thr B A s.
Proof.
  induction ops as [|op ops IH]; intros m thr B A K s Hinv Henv HKB H3B H3 Hthr; [exact I|].
  destruct s as [h n sts ini lk fr]. destruct Henv as (E1 & E2 & E3).
  cbn [ms_heap ms_next ms_statics ms_inited] in Hinv, E1, E2, E3.
  destruct op as [k | k v | k]; cbn [session]; unfold with_frames; cbn [ms_heap ms_next ms_statics ms_inited ms_locks].
  - intros ku (Hk & Hg & Hmax).
    eapply returns_weaken.
    { apply (get_map e good eq_sym eq_trans eq_hash h n sts ini lk m k ku A K thr); try assumption. exact (proj1 Hinv). }
    intros s' (P1 & P2 & P3 & P4).
    split; [exists K; rewrite P1; split; [exact (proj1 Hinv) | exact HKB]|].
    apply (IH m thr B A K s'); try assumption.
    + rewrite P1, P2. exact Hinv.
    + unfold cim_env. rewrite P3, P4. exact (conj E1 (conj E2 E3)).
  - intros ku (Hk & Hg & Hmax) Hv Hc.
    eapply returns_weaken.
    { apply (put_map h n sts ini lk m k ku v A K thr); assumption. }
    intros s' (K' & P1 & P2 & P3 & P4 & P5).
    assert (HK'B : Z.of_nat K' <= B).
    { destruct P2 as [->|(Q1 & Q2 & Q3)]; [exact HKB|]. rewrite Q1. clear -Q2 Q3 H3B. Z.div_mod_to_equations. lia. }
    split; [exists K'; split; [exact (proj1 P1) | exact HK'B]|].
    apply (IH m thr B _ K' s'); try assumption.
    unfold cim_env. rewrite P4, P5. exact (conj E1 (conj E2 E3)).
  - intros ku (Hk & Hg & Hmax).
    destruct Hinv as (Hrep & Hfr & Hvals & HK2).
    eapply returns_weaken.
    { apply (remove_map e good eq_sym eq_trans eq_hash h n sts ini lk m k ku A K thr); assumption. }
    intros s' (P1 & P2 & P3 & P4 & P5 & P6).
    split; [exists K; split; [exact P1 | exact HKB]|].
    apply (IH m thr B _ K s'); try assumption.
    + apply (inv_frame h (ms_heap s') n (ms_next s') m); try assumption.
      intros kk vv Hin. exact (Hvals kk vv (a_remove_in h A ku kk vv Hin)).
    + unfold cim_env. rewrite P5, P6. exact (conj E1 (conj E2 E3)).
Qed.

End Session.

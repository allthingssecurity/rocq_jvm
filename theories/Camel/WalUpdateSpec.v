(** * The whole-class contract of camel-wal [TransactionLog.update] (fix), for every ring buffer.

    [WalUpdate.update_live] / [update_dead] are about the bytecode of
    [update] and of everything it calls (canUpdate(LayerInfo), the getters,
    canUpdate(IIII)Z, LogEntry.setEntryState, the slf4j calls), for any heap.
    Here they are combined with the ring-buffer semantics of [WalSpec]: for a
    log of capacity [cap] after [n] adds, given the LayerInfo that [add]
    returned for entry [k] (index k mod cap, layer k / cap),
    - if entry k is still in the buffer (n - cap <= k), [update] sets the
      state of exactly that entry's LogEntry and returns its container;
    - otherwise it returns null and leaves every existing object unchanged. *)

From Stdlib Require Import ZArith String List Bool Lia.
From JVM.Core Require Import Int Instr Desc Semantics Machine Logic.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Camel Require Import WalSpec WalUpdate.
Import ListNotations.
Open Scope Z_scope.

(** canUpdate(IIII)Z of the fix decides liveness for every reachable state. *)
Lemma cu4_live : forall cap n k, reachable cap n k ->
  cu4_val (cur_layer cap n) (cur_index cap n) (ent_layer cap k) (ent_index cap k)
  = if live cap n k then 1 else 0.
Proof.
  intros cap n k Hr.
  destruct (live_linear cap n k Hr) as (Hlive & HeL & HeI & HcI & Hsame & HcL).
  set (cL := cur_layer cap n) in *. set (cI := cur_index cap n) in *.
  set (eL := ent_layer cap k) in *. set (eI := ent_index cap k) in *.
  assert (Hw : wrap 32 (eL + 1) = eL + 1 \/ (eL = INT_MAX /\ wrap 32 (eL + 1) = INT_MIN)).
  { destruct (Z.eq_dec eL INT_MAX) as [E|E].
    - right. split; [exact E|]. rewrite E. reflexivity.
    - left. apply wrap_id; [lia|]. unfold in_range, INT_MAX in *; simpl in *; lia. }
  unfold cu4_val. unfold INT_MAX, INT_MIN in *.
  case_eq (live cap n k); intro L.
  - apply Hlive in L. destruct L as [E | [E1 E2]].
    + replace ((cL =? eL) && (eI <=? cI)) with true by
        (symmetry; apply andb_true_iff; split; [apply Z.eqb_eq | apply Z.leb_le]; specialize (Hsame E); lia).
      reflexivity.
    + destruct ((cL =? eL) && (eI <=? cI)); [reflexivity|].
      destruct Hw as [Hw | [Hm _]]; [|lia].
      rewrite Hw.
      replace ((cL =? eL + 1) && (cI <=? eI)) with true by
        (symmetry; apply andb_true_iff; split; [apply Z.eqb_eq | apply Z.leb_le]; lia).
      reflexivity.
  - assert (NL : ~ (eL = cL \/ (eL + 1 = cL /\ cI <= eI))) by (rewrite <- Hlive; congruence).
    replace ((cL =? eL) && (eI <=? cI)) with false
      by (symmetry; apply andb_false_iff; destruct (Z.eq_dec cL eL); [right; apply Z.leb_gt; lia | left; apply Z.eqb_neq; lia]).
    destruct Hw as [Hw | [Hm Hw]]; rewrite Hw.
    + replace ((cL =? eL + 1) && (cI <=? eI)) with false
        by (symmetry; apply andb_false_iff; destruct (Z.eq_dec cL (eL + 1)); [right; apply Z.leb_gt; lia | left; apply Z.eqb_neq; lia]).
      reflexivity.
    + replace (cL =? - 2 ^ 31) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Section Contract.
Variable e : jenv.

(** The heap facts that hold for a log after [n] adds (the representation
    invariant of TransactionLog, as far as [update] reads it), for one entry
    [k]: the log object [t], the LayerInfo [li] that add returned for entry
    k, and, if entry k is live, the array slot that holds its container. *)
Theorem update_contract : forall s0 t li stv cap n k arr b lg vf,
  reachable cap n k ->
  ms_frames s0 = [upd_frame t li stv] ->
  ms_heap s0 t = Some (OObj TL (tl_fields cap arr (cur_index cap n) (cur_layer cap n))) ->
  ms_heap s0 li = Some (OObj LI (li_fields (ent_index cap k) (ent_layer cap k) b)) ->
  (match stv with VNull | VRef _ => true | _ => false end) = true ->
  (match vf with VNull | VRef _ => true | _ => false end) = true ->
  erroneous wp 64 (ms_statics s0) TL = false -> init_needed wp 64 (ms_inited s0) TL = None ->
  erroneous wp 64 (ms_statics s0) ES = false -> init_needed wp 64 (ms_inited s0) ES = None ->
  assoc LOGK (ms_statics s0) = Some (VRef lg) -> assoc FAILEDK (ms_statics s0) = Some vf ->
  ms_heap s0 lg = Some (OObj LOGC nil) ->
  t < ms_next s0 -> li < ms_next s0 -> lg < ms_next s0 ->
  (* the slot of a live entry holds its container, whose LogEntry is [le] *)
  (live cap n k = true -> exists es c x pos le st0 km kk vm vv,
      ms_heap s0 arr = Some (OArr (TRef EC) es) /\ Z.of_nat (length es) = cap /\
      nth_z es (ent_index cap k) = Some (VRef c) /\
      ms_heap s0 c = Some (OObj EC (ec_fields x (VRef le) pos)) /\
      ms_heap s0 le = Some (OObj LE (le_fields st0 km kk vm vv)) /\
      arr < ms_next s0 /\ c < ms_next s0 /\ le < ms_next s0) ->
  if live cap n k then
    exists c le km kk vm vv,
      returns wp (mdl e) s0 (Some (VRef c))
        (fun s' => ms_heap s' le = Some (OObj LE (le_fields stv km kk vm vv)) /\
                   (forall y, y < ms_next s0 -> y <> le -> ms_heap s' y = ms_heap s0 y) /\ env_same s0 s')
  else
    returns wp (mdl e) s0 (Some VNull)
      (fun s' => (forall y, y < ms_next s0 -> ms_heap s' y = ms_heap s0 y) /\ env_same s0 s').
Proof.
  intros s0 t li stv cap n k arr b lg vf Hr Hfr Ht Hli Hstv Hvf He Hi He2 Hi2 HLOG HF Hlg Ht' Hli' Hlg' Hslot.
  pose proof (cu4_live cap n k Hr) as Hcu.
  destruct (live cap n k) eqn:L.
  - destruct (Hslot eq_refl) as (es & c & x & pos & le & st0 & km & kk & vm & vv & Ha & Hlen & Hn & Hc & Hle & Ha' & Hc' & Hle').
    exists c, le, km, kk, vm, vv.
    destruct Hr as (Hcap & Hk & Hl).
    eapply update_live; eauto.
    unfold ent_index. pose proof (Z.mod_pos_bound k cap ltac:(lia)). lia.
  - eapply update_dead; eauto.
Qed.
End Contract.

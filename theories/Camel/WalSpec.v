(** * Specification of camel-wal [TransactionLog.canUpdate] (CAMEL-26088).

    [TransactionLog] is a ring buffer of [capacity] slots.  [add] stores the
    k-th entry (k = 0, 1, ...) at slot [k mod capacity] of layer
    [k / capacity] and then increments [currentIndex]; it starts a new layer
    lazily, when [currentIndex >= capacity] at the next [add].  So after
    [n >= 1] adds:
      currentLayer = (n-1) / capacity,  currentIndex = (n-1) mod capacity + 1,
    and after 0 adds both are 0.  The entry added k-th is still in the
    buffer ("live") iff it was not overwritten by one of the later adds, i.e.
    iff  n - capacity <= k < n.

    The intended contract of [canUpdate(currentLayer, currentIndex,
    entryLayer, entryIndex)], as used by [update]: for every reachable state
    and every entry that was added, it returns true exactly for live entries.
    This file defines that contract over the ring-buffer semantics and proves
    the equivalent linear form used by the bytecode proofs.

    These ring-buffer equations describe [add] as read from the Java source;
    the bytecode of [add] itself (fields, arrays) is a Phase 2 target. *)

From Stdlib Require Import ZArith Lia Bool.
From JVM.Core Require Import Int.
Open Scope Z_scope.

Definition cur_layer (cap n : Z) : Z := if n =? 0 then 0 else (n - 1) / cap.
Definition cur_index (cap n : Z) : Z := if n =? 0 then 0 else (n - 1) mod cap + 1.
Definition ent_layer (cap k : Z) : Z := k / cap.
Definition ent_index (cap k : Z) : Z := k mod cap.
Definition live (cap n k : Z) : bool := (n - cap <=? k) && (k <? n).

(** Preconditions: a positive int capacity, an entry that was added, and a
    current layer that fits in an int (no [currentLayer++] overflow yet). *)
Definition reachable (cap n k : Z) : Prop :=
  1 <= cap <= INT_MAX /\ 0 <= k < n /\ (n - 1) / cap <= INT_MAX.

(** The contract, for any implementation [f] of the four-int predicate. *)
Definition canUpdate_contract (f : Z -> Z -> Z -> Z -> bool) : Prop :=
  forall cap n k, reachable cap n k ->
    f (cur_layer cap n) (cur_index cap n) (ent_layer cap k) (ent_index cap k) = live cap n k.

(** ** Linear characterisation *)
Lemma live_linear : forall cap n k, reachable cap n k ->
  let cL := cur_layer cap n in let cI := cur_index cap n in
  let eL := ent_layer cap k in let eI := ent_index cap k in
  (live cap n k = true <-> (eL = cL \/ (eL + 1 = cL /\ cI <= eI))) /\
  0 <= eL <= cL /\ 0 <= eI < cap /\ 1 <= cI <= cap /\ (eL = cL -> eI < cI) /\
  cL <= INT_MAX.
Proof.
  intros cap n k (Hcap & Hk & Hl). cbn zeta.
  unfold cur_layer, cur_index, ent_layer, ent_index, live.
  replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  set (m := n - 1) in *.
  pose proof (Z.div_mod m cap ltac:(lia)) as Dm.
  pose proof (Z.mod_pos_bound m cap ltac:(lia)) as Bm.
  pose proof (Z.div_mod k cap ltac:(lia)) as Dk.
  pose proof (Z.mod_pos_bound k cap ltac:(lia)) as Bk.
  set (q := m / cap) in *. set (r := m mod cap) in *.
  set (q' := k / cap) in *. set (r' := k mod cap) in *.
  assert (Hq'0 : 0 <= q') by (apply Z.div_pos; lia).
  assert (Hqq : q' <= q) by (apply Z.div_le_mono; lia).
  assert (Hsame : q' = q -> r' < r + 1) by (intros E; rewrite E in Dk; lia).
  split; [split|].
  - rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. intros [H1 H2].
    destruct (Z.eq_dec q' q) as [E|E]; [left; exact E|right].
    assert (q' + 1 = q \/ q' + 2 <= q) as [E1|E2] by lia.
    + split; [exact E1|]. lia.
    + exfalso. assert (cap * (q' + 2) <= cap * q) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  - rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. intros [E | [E1 E2]]; split; lia.
  - repeat split; lia.
Qed.

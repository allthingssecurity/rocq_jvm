(* ===================================================================== *)
(*  JVM.Concurrency.Executions                                           *)
(*                                                                       *)
(*  Executions of the Java Memory Model, JLS SE 21 sections 17.4.2-7:    *)
(*  program order (po), synchronization order (so), synchronizes-with    *)
(*  (sw), happens-before (hb), the write-seen function W (rf),           *)
(*  well-formedness (17.4.7), hb-consistency (17.4.5), data races        *)
(*  (17.4.5), sequential consistency (17.4.3) and correctly synchronized *)
(*  programs (17.4.5).                                                   *)
(*                                                                       *)
(*  Representation choices (see docs/track-c-status.md):                 *)
(*                                                                       *)
(*  - An execution is a finite set of events identified by natural      *)
(*    numbers below [ex_n], selected by the boolean [ex_dom].  The       *)
(*    numbering is a *presentation order*: program order is the         *)
(*    numbering restricted to each thread, and the synchronization       *)
(*    order (a total order over all synchronization actions, JLS 17.4.4) *)
(*    is the numbering restricted to synchronization actions.  Plain     *)
(*    (non-synchronization) events may be numbered anywhere consistent   *)
(*    with program order, and the numbering says nothing about which     *)
(*    write a read sees; that is given by [ex_ws] (JLS's W).             *)
(*    Every finite JLS execution can be presented this way, because so   *)
(*    is total on synchronization actions and consistent with po, so     *)
(*    po U so is acyclic and has a linear extension.                     *)
(*                                                                       *)
(*  - Default-value ("initialisation") writes are not events.  A read    *)
(*    with [ex_ws r = None] sees the default value [init l].  This is    *)
(*    the JLS reading in which the default writes happen-before every    *)
(*    other action (they synchronize-with the first action of every      *)
(*    thread, 17.4.4); it avoids the Aspinall-Sevcik problem that the    *)
(*    default writes are not synchronization actions.                    *)
(*                                                                       *)
(*  - Data races are between *plain* accesses only (Jacobs; Lochbihler). *)
(*    Given well-formedness, all accesses to a volatile location are     *)
(*    volatile actions, so this only excludes volatile-volatile pairs,   *)
(*    which the JLS definition would classify as races although they     *)
(*    are the intended means of synchronization.                         *)
(*                                                                       *)
(*  - Thread interruption (17.4.4, Thread.interrupt) is not modelled.    *)
(* ===================================================================== *)

From Stdlib Require Import List Arith Bool Lia Relations.
From JVM.Concurrency Require Import Events Order.
Import ListNotations.
Open Scope bool_scope.

Section Executions.
  Context {L V M C X : Type}.

  (** Which locations are volatile (fields declared [volatile]), and the
      default value of each location (zero, false or null). *)
  Variable vol : L -> bool.
  Variable init : L -> V.
  (** Monitors must have decidable equality to count lock actions. *)
  Variable M_eq_dec : forall m m' : M, {m = m'} + {m <> m'}.

  Record execution : Type := mkExec {
    ex_n   : nat;                       (* events are numbered below ex_n  *)
    ex_dom : nat -> bool;               (* which numbers are events        *)
    ex_lab : nat -> event L V M C X;    (* thread and action of each event *)
    ex_ws  : nat -> option nat          (* W: the write seen by each read;
                                           None = the default value       *)
  }.

  Definition D (E : execution) (i : nat) : Prop := ex_dom E i = true.
  Definition tid_of (E : execution) (i : nat) : tid := ev_tid (ex_lab E i).
  Definition act (E : execution) (i : nat) : action L V M C X := ev_act (ex_lab E i).
  Definition sync (E : execution) (i : nat) : Prop := is_sync (act E i) = true.

  (** * Orders and relations (JLS 17.4.3-17.4.5) *)

  (** Program order: same thread, earlier. *)
  Definition po (E : execution) (i j : nat) : Prop :=
    D E i /\ D E j /\ i < j /\ tid_of E i = tid_of E j.

  (** Synchronization order: the numbering on synchronization actions. *)
  Definition so (E : execution) (i j : nat) : Prop :=
    D E i /\ D E j /\ i < j /\ sync E i /\ sync E j.

  (** Synchronizes-with (JLS 17.4.4):
      - an unlock of m synchronizes-with every so-subsequent lock of m;
      - a volatile write of v synchronizes-with every so-subsequent
        volatile read of v;
      - the action that starts a thread synchronizes-with the first
        action of the started thread;
      - the final action of a thread T synchronizes-with any action that
        detects that T has terminated.
      The default writes are handled by [ex_ws = None] (see the header);
      interruption is not modelled. *)
  Definition sw (E : execution) (i j : nat) : Prop :=
    D E i /\ D E j /\
    match act E i, act E j with
    | AUnlock m, ALock m' => m = m' /\ i < j
    | AVWrite l _, AVRead l' _ => l = l' /\ i < j
    | ASpawn t _, AStart => tid_of E j = t
    | AFinish, AJoin t => t = tid_of E i
    | _, _ => False
    end.

  (** Happens-before: transitive closure of po and sw (JLS 17.4.5). *)
  Definition hb (E : execution) : nat -> nat -> Prop :=
    clos_trans nat (fun i j => po E i j \/ sw E i j).

  (** Reads-from: [rf E w r] iff r sees w, i.e. W(r) = w. *)
  Definition rf (E : execution) (w r : nat) : Prop :=
    D E r /\ ex_ws E r = Some w.

  (** * Well-formedness (JLS 17.4.7) *)

  (** Volatile locations are accessed only by volatile actions, plain
      locations only by plain actions (17.4.7, item 2). *)
  Definition volatile_ok (a : action L V M C X) : Prop :=
    match a with
    | ARead l _ | AWrite l _ => vol l = false
    | AVRead l _ | AVWrite l _ => vol l = true
    | _ => True
    end.

  Definition is_lock_of (m : M) (a : action L V M C X) : bool :=
    match a with ALock m' => if M_eq_dec m m' then true else false | _ => false end.
  Definition is_unlock_of (m : M) (a : action L V M C X) : bool :=
    match a with AUnlock m' => if M_eq_dec m m' then true else false | _ => false end.

  (** Number of events below [i] satisfying [p]. *)
  Definition count_before (E : execution) (p : nat -> bool) (i : nat) : nat :=
    length (filter (fun j => ex_dom E j && p j) (seq 0 i)).

  Definition locks_before (E : execution) (t : tid) (m : M) (i : nat) : nat :=
    count_before E (fun j => Nat.eqb (tid_of E j) t && is_lock_of m (act E j)) i.
  Definition unlocks_before (E : execution) (t : tid) (m : M) (i : nat) : nat :=
    count_before E (fun j => Nat.eqb (tid_of E j) t && is_unlock_of m (act E j)) i.

  Record wf (E : execution) : Prop := {
    (* events are numbered below ex_n *)
    wf_bound : forall i, D E i -> i < ex_n E;
    (* 17.4.7(1): every read sees a write to the same variable, with the
       value read; None means the default value *)
    wf_ws : forall r l v, D E r -> read_of (act E r) = Some (l, v) ->
      match ex_ws E r with
      | Some w => D E w /\ write_of (act E w) = Some (l, v)
      | None => v = init l
      end;
    (* W is only defined on reads *)
    wf_ws_none : forall i, D E i -> read_of (act E i) = None -> ex_ws E i = None;
    (* 17.4.7(2): volatile variables only by volatile actions *)
    wf_vol : forall i, D E i -> volatile_ok (act E i);
    (* 17.4.7(5): synchronization-order consistency for volatile reads:
       W(r) is not so-after r, and no write to the variable is so-between
       W(r) and r (for the default value: no write so-before r) *)
    wf_so_vol : forall r l v, D E r -> act E r = AVRead l v ->
      match ex_ws E r with
      | Some w => w < r /\
          forall w', D E w' -> write_loc (act E w') = Some l -> ~ (w < w' /\ w' < r)
      | None => forall w', D E w' -> write_loc (act E w') = Some l -> ~ w' < r
      end;
    (* 17.4.7(3) / 17.4.4: so is consistent with mutual exclusion: when t
       locks m, no other thread holds m *)
    wf_mutex : forall i m t, D E i -> act E i = ALock m -> t <> tid_of E i ->
      locks_before E t m i = unlocks_before E t m i;
    (* a thread only unlocks monitors it holds *)
    wf_unlock : forall i m, D E i -> act E i = AUnlock m ->
      unlocks_before E (tid_of E i) m i < locks_before E (tid_of E i) m i;
    (* the first action of every thread is AStart, and only it *)
    wf_start_first : forall i, D E i ->
      (forall j, D E j -> j < i -> tid_of E j <> tid_of E i) -> act E i = AStart;
    wf_start_only_first : forall i j, D E i -> D E j -> act E j = AStart ->
      tid_of E i = tid_of E j -> j <= i;
    (* AFinish is the last action of its thread *)
    wf_finish_last : forall i j, D E i -> D E j -> act E i = AFinish ->
      tid_of E j = tid_of E i -> j <= i;
    (* a thread is started (in so) before any of its actions *)
    wf_spawn_before : forall i j t c, D E i -> D E j -> act E i = ASpawn t c ->
      tid_of E j = t -> i < j;
    (* termination is detected only after it happened *)
    wf_join_after : forall j t, D E j -> act E j = AJoin t ->
      exists i, D E i /\ i < j /\ tid_of E i = t /\ act E i = AFinish
  }.

  (** * hb-consistency (JLS 17.4.5)

      For every read r: not hb(r, W(r)), and there is no write w to the
      same variable with hb(W(r), w) and hb(w, r).  When r sees the
      default value, the default write happens-before everything, so the
      condition is that no write to the variable happens-before r. *)
  Definition hb_consistent (E : execution) : Prop :=
    forall r l v, D E r -> read_of (act E r) = Some (l, v) ->
    match ex_ws E r with
    | Some w => ~ hb E r w /\
        forall w', write_loc (act E w') = Some l -> ~ (hb E w w' /\ hb E w' r)
    | None => forall w', write_loc (act E w') = Some l -> ~ hb E w' r
    end.

  (** * Data races (JLS 17.4.5)

      Two different plain accesses to the same variable, at least one of
      them a write, not ordered by happens-before. *)
  Definition race (E : execution) (i j : nat) : Prop :=
    D E i /\ D E j /\ i <> j /\
    (exists l, plain_loc (act E i) = Some l /\ plain_loc (act E j) = Some l) /\
    (is_plain_write (act E i) = true \/ is_plain_write (act E j) = true) /\
    ~ hb E i j /\ ~ hb E j i.

  Definition race_free (E : execution) : Prop := forall i j, ~ race E i j.

  (** * Sequential consistency (JLS 17.4.3)

      A total order [ord] (an injective ranking of the events) consistent
      with program order, in which every read sees the last preceding
      write to its variable (or the default value if there is none).  We
      also require consistency with the synchronization order, so that
      the total order respects mutual exclusion (Aspinall and Sevcik
      point out that the JLS definition omits this). *)
  Definition sees_last (E : execution) (ord : nat -> nat) (r : nat) : Prop :=
    forall l v, read_of (act E r) = Some (l, v) ->
    match ex_ws E r with
    | Some w => D E w /\ write_of (act E w) = Some (l, v) /\ ord w < ord r /\
        forall w', D E w' -> write_loc (act E w') = Some l -> ord w' < ord r ->
          ord w' <= ord w
    | None => v = init l /\
        forall w', D E w' -> write_loc (act E w') = Some l -> ~ ord w' < ord r
    end.

  Record sc_order (E : execution) (ord : nat -> nat) : Prop := {
    sc_inj : forall i j, D E i -> D E j -> ord i = ord j -> i = j;
    sc_po : forall i j, po E i j -> ord i < ord j;
    sc_so : forall i j, so E i j -> ord i < ord j;
    sc_reads : forall r, D E r -> sees_last E ord r
  }.

  Definition sequentially_consistent (E : execution) : Prop :=
    exists ord, sc_order E ord.

  (** * Executions of a program (intra-thread consistency, 17.4.7(4))

      The events of thread [t], in program order, form a finite run of
      the thread-local semantics from the thread's initial state: the
      program's initial state for the main thread, and a state given by
      [tinit c] for a thread started by an event [ASpawn t c]. *)
  Definition thread_ids (E : execution) (t : tid) : list nat :=
    filter (fun i => ex_dom E i && Nat.eqb (tid_of E i) t) (seq 0 (ex_n E)).

  Definition proj (E : execution) (t : tid) : list (action L V M C X) :=
    map (act E) (thread_ids E t).

  Definition thread_init (P : program L V M C X) (E : execution) (t : tid)
      (s0 : tstate (p_lts P)) : Prop :=
    (t = p_main P /\ s0 = p_init P) \/
    (t <> p_main P /\ exists i c, D E i /\ act E i = ASpawn t c /\ tinit (p_lts P) c s0).

  Definition exec_of (P : program L V M C X) (E : execution) : Prop :=
    forall t, (exists i, D E i /\ tid_of E i = t) ->
      exists s0 s, thread_init P E t s0 /\ trun (p_lts P) s0 (proj E t) s.

  (** A program is correctly synchronized iff all its sequentially
      consistent executions are free of data races (JLS 17.4.5). *)
  Definition correctly_synchronized (P : program L V M C X) : Prop :=
    forall E, wf E -> exec_of P E -> sequentially_consistent E -> race_free E.

  (** * Basic lemmas *)

  Lemma is_lock_of_sync m a : is_lock_of m a = true -> is_sync a = true.
  Proof. destruct a; simpl; congruence. Qed.

  Lemma is_unlock_of_sync m a : is_unlock_of m a = true -> is_sync a = true.
  Proof. destruct a; simpl; congruence. Qed.

  Lemma read_of_cases (a : action L V M C X) l v :
    read_of a = Some (l, v) -> a = ARead l v \/ a = AVRead l v.
  Proof. destruct a; simpl; try discriminate; intros H; injection H as <- <-; auto. Qed.

  Lemma write_loc_cases (a : action L V M C X) l :
    write_loc a = Some l -> (exists v, a = AWrite l v) \/ (exists v, a = AVWrite l v).
  Proof.
    unfold write_loc. destruct a; simpl; try discriminate;
      intros H; injection H as <-; eauto.
  Qed.

  Lemma write_of_loc (a : action L V M C X) l v :
    write_of a = Some (l, v) -> write_loc a = Some l.
  Proof. unfold write_loc. intros ->. reflexivity. Qed.

  Lemma po_dom E i j : po E i j -> D E i /\ D E j.
  Proof. unfold po. tauto. Qed.

  Lemma sw_dom E i j : sw E i j -> D E i /\ D E j.
  Proof. unfold sw. tauto. Qed.

  Lemma hb_dom E i j : hb E i j -> D E i /\ D E j.
  Proof.
    induction 1 as [i j [H|H]|i k j _ [IH1 _] _ [_ IH2]].
    - apply po_dom; auto.
    - apply sw_dom; auto.
    - auto.
  Qed.

  Section WF.
    Variable E : execution.
    Hypothesis Hwf : wf E.

    (** In a well-formed execution, sw is contained in so. *)
    Lemma sw_so i j : sw E i j -> so E i j.
    Proof.
      intros (Di & Dj & H). unfold so, sync.
      destruct (act E i) eqn:Ai; try contradiction;
        destruct (act E j) eqn:Aj; try contradiction;
        repeat split; auto; try tauto.
      - (* spawn -> start *)
        eapply wf_spawn_before; eauto.
      - (* finish -> join *)
        destruct (wf_join_after _ Hwf j t Dj Aj) as (k & Dk & Hkj & Hk & Ak).
        assert (i <= k) by (apply (wf_finish_last _ Hwf k i); auto; congruence).
        lia.
    Qed.

    Lemma hb_lt i j : hb E i j -> i < j.
    Proof.
      apply (clos_trans_rank _ (fun x => x)). intros a b [H|H].
      - apply H.
      - apply sw_so in H. apply H.
    Qed.

    Lemma hb_irrefl i : ~ hb E i i.
    Proof. intros H. apply hb_lt in H. lia. Qed.

    (** Writes and reads of a plain location are plain actions. *)
    Lemma plain_write i l : D E i -> write_loc (act E i) = Some l -> vol l = false ->
      exists v, act E i = AWrite l v.
    Proof.
      intros Di Hw Hv. pose proof (wf_vol _ Hwf i Di) as Hok.
      destruct (write_loc_cases _ _ Hw) as [[v' Ha]|[v' Ha]]; rewrite Ha in Hok; simpl in Hok.
      - eauto.
      - congruence.
    Qed.

    Lemma volatile_write i l : D E i -> write_loc (act E i) = Some l -> vol l = true ->
      exists v, act E i = AVWrite l v.
    Proof.
      intros Di Hw Hv. pose proof (wf_vol _ Hwf i Di) as Hok.
      destruct (write_loc_cases _ _ Hw) as [[v' Ha]|[v' Ha]]; rewrite Ha in Hok; simpl in Hok.
      - congruence.
      - eauto.
    Qed.
  End WF.

End Executions.

Arguments execution : clear implicits.

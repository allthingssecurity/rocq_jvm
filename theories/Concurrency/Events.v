(* ===================================================================== *)
(*  JVM.Concurrency.Events                                               *)
(*                                                                       *)
(*  Abstract event interface for the Java Memory Model (JLS 17.4).       *)
(*                                                                       *)
(*  Everything here is parametric in:                                    *)
(*    L : memory locations (see [location] below for the JVM instance)   *)
(*    V : values                                                         *)
(*    M : monitors (in the JVM: object references)                       *)
(*    C : "spawn payload" -- what a thread start carries so that the     *)
(*        new thread's initial state can be built (in the JVM: the       *)
(*        java.lang.Thread object whose run() is executed)               *)
(*    X : labels of external / observable actions (I/O, native calls)    *)
(*                                                                       *)
(*  Track A is expected to instantiate these with its own types and to   *)
(*  provide a thread-local labelled transition system ([lts] below)      *)
(*  whose heap/static/array accesses become [ARead]/[AWrite]/... labels. *)
(* ===================================================================== *)

From Stdlib Require Import List Arith.
Import ListNotations.

(** Thread identifiers. *)
Definition tid := nat.

(** * Locations

    The JMM speaks about "variables": instance fields, static fields and
    array elements (JLS 17.4.1).  We give a canonical parametric location
    type; the rest of the development is generic in [L] so Track A may
    use this type or its own. *)
Inductive location (Addr Field Static : Type) : Type :=
| LField  (a : Addr) (f : Field)   (* instance field  a.f        *)
| LStatic (s : Static)             (* static field   C.f         *)
| LArray  (a : Addr) (i : nat).    (* array element  a[i]        *)
Arguments LField {Addr Field Static} a f.
Arguments LStatic {Addr Field Static} s.
Arguments LArray {Addr Field Static} a i.

Section Actions.
  Context {L V M C X : Type}.

  (** * Actions (JLS 17.4.2 "inter-thread actions")

      Thread start and the thread's first action are distinguished:
      [ASpawn t c] is performed by the *parent* (Thread.start()), and
      [AStart] is the first action of the *child*.  [AFinish] is the
      last action of a thread; [AJoin t] is any action that detects that
      thread [t] has terminated (Thread.join(), isAlive() = false). *)
  Inductive action : Type :=
  | ARead    (l : L) (v : V)      (* normal (plain) read        *)
  | AWrite   (l : L) (v : V)      (* normal (plain) write       *)
  | AVRead   (l : L) (v : V)      (* volatile read              *)
  | AVWrite  (l : L) (v : V)      (* volatile write             *)
  | ALock    (m : M)              (* monitorenter               *)
  | AUnlock  (m : M)              (* monitorexit                *)
  | ASpawn   (t : tid) (c : C)    (* Thread.start() of thread t *)
  | AStart                        (* first action of a thread   *)
  | AFinish                       (* last action of a thread    *)
  | AJoin    (t : tid)            (* detects termination of t   *)
  | AExternal (x : X).            (* external / observable      *)

  (** Synchronization actions (JLS 17.4.2): volatile accesses, lock,
      unlock, first/last action of a thread, starting a thread and
      detecting termination.  Plain accesses and external actions are
      not synchronization actions. *)
  Definition is_sync (a : action) : bool :=
    match a with
    | AVRead _ _ | AVWrite _ _ | ALock _ | AUnlock _
    | ASpawn _ _ | AStart | AFinish | AJoin _ => true
    | ARead _ _ | AWrite _ _ | AExternal _ => false
    end.

  (** Location and value written, for both plain and volatile writes. *)
  Definition write_of (a : action) : option (L * V) :=
    match a with
    | AWrite l v | AVWrite l v => Some (l, v)
    | _ => None
    end.

  (** Location and value read, for both plain and volatile reads. *)
  Definition read_of (a : action) : option (L * V) :=
    match a with
    | ARead l v | AVRead l v => Some (l, v)
    | _ => None
    end.

  Definition write_loc (a : action) : option L :=
    match write_of a with Some (l, _) => Some l | None => None end.

  (** Location of a *plain* (non-volatile) memory access. *)
  Definition plain_loc (a : action) : option L :=
    match a with
    | ARead l _ | AWrite l _ => Some l
    | _ => None
    end.

  Definition is_plain_write (a : action) : bool :=
    match a with AWrite _ _ => true | _ => false end.

  (** Events: an action performed by a thread.  Event *identity* is the
      position of the event in an execution (see Executions.v), so two
      equal [event] records at different positions are different
      events. *)
  Record event : Type := mkEv { ev_tid : tid; ev_act : action }.

  Definition trace := list event.

  (** * Thread-local semantics

      A thread-local labelled transition system.  [tstep s None s'] is a
      silent (thread-internal) step, [tstep s (Some a) s'] a step
      performing inter-thread action [a].  Reads are *inputs*: the
      thread-local semantics does not know memory and must accept the
      read value as given (cf. [receptive] below); the memory model
      (SC interleaving or JMM) decides which values reads may return.

      [tinit c s0] says that a thread spawned with payload [c] may start
      in state [s0].  The thread itself is expected to emit [AStart] as
      its first action and [AFinish] as its last (well-formedness
      conditions in Executions.v enforce this at the execution level).

      Track A instantiates [tstate] with its frame stack / thread state
      and [tstep] with the single-threaded interpreter, turning
      getfield/putfield/getstatic/putstatic/xaload/xastore into
      [ARead]/[AWrite] (or [AVRead]/[AVWrite] for volatile fields),
      monitorenter/monitorexit and synchronized methods into
      [ALock]/[AUnlock], Thread.start into [ASpawn], Thread.join into
      [AJoin], and native I/O into [AExternal]. *)
  Record lts : Type := mkLTS {
    tstate : Type;
    tstep  : tstate -> option action -> tstate -> Prop;
    tinit  : C -> tstate -> Prop
  }.

  (** Receptiveness (input-enabledness) for plain reads: if a thread can
      read some value from [l], it can read any value from [l].  This is
      the standard assumption that makes the JMM's "intra-thread
      semantics with arbitrary read values" meaningful; it holds for any
      interpreter that treats the read value as an input. *)
  Definition receptive (S : lts) : Prop :=
    forall s l v s', tstep S s (Some (ARead l v)) s' ->
      forall v', exists s'', tstep S s (Some (ARead l v')) s''.

  (** Finite runs of a thread, labelled with the sequence of
      inter-thread actions performed (silent steps are dropped). *)
  Inductive trun (S : lts) : tstate S -> list action -> tstate S -> Prop :=
  | trun_nil  s : trun S s [] s
  | trun_tau  s s' as_ s'' :
      tstep S s None s' -> trun S s' as_ s'' -> trun S s as_ s''
  | trun_act  s a s' as_ s'' :
      tstep S s (Some a) s' -> trun S s' as_ s'' -> trun S s (a :: as_) s''.

  (** * Programs

      A program is a thread-local LTS plus the main thread's identity
      and initial state.  All other threads are created by [ASpawn]. *)
  Record program : Type := mkProg {
    p_lts : lts;
    p_main : tid;
    p_init : tstate p_lts
  }.

  (** ** Basic lemmas about thread runs *)

  Lemma trun_app (S : lts) s as1 s' as2 s'' :
    trun S s as1 s' -> trun S s' as2 s'' -> trun S s (as1 ++ as2) s''.
  Proof.
    induction 1; intros; simpl; eauto using trun.
  Qed.

  (** Splitting a run at any point of its action sequence. *)
  Lemma trun_app_inv (S : lts) s as1 as2 s'' :
    trun S s (as1 ++ as2) s'' ->
    exists s', trun S s as1 s' /\ trun S s' as2 s''.
  Proof.
    intros H. remember (as1 ++ as2) as l eqn:E.
    revert as1 as2 E.
    induction H; intros as1 as2 E.
    - destruct as1; [|discriminate]. destruct as2; [|discriminate].
      exists s. split; constructor.
    - destruct (IHtrun as1 as2 E) as (s1 & H1 & H2).
      exists s1. split; [eapply trun_tau; eauto | exact H2].
    - destruct as1 as [|a1 as1'].
      + exists s. split; [constructor|]. simpl in E. subst.
        eapply trun_act; eauto.
      + simpl in E. injection E as -> E.
        destruct (IHtrun as1' as2 E) as (s1 & H1 & H2).
        exists s1. split; [eapply trun_act; eauto | exact H2].
  Qed.

  (** A run performing exactly one action decomposes as
      silent steps, the action, silent steps. *)
  Lemma trun_single_inv (S : lts) s a s'' :
    trun S s [a] s'' ->
    exists s1 s2, trun S s [] s1 /\ tstep S s1 (Some a) s2 /\ trun S s2 [] s''.
  Proof.
    intros H. remember [a] as l eqn:E. induction H.
    - discriminate.
    - destruct (IHtrun E) as (s1 & s2 & H1 & H2 & H3).
      exists s1, s2. split; [eapply trun_tau; eauto | auto].
    - injection E as -> ->. exists s, s'. repeat split; auto. constructor.
  Qed.

  (** Receptiveness lifted to runs: a run ending in a plain read can be
      redirected to read any other value. *)
  Lemma trun_snoc_read (S : lts) :
    receptive S ->
    forall s0 as_ l v s, trun S s0 (as_ ++ [ARead l v]) s ->
    forall v', exists s', trun S s0 (as_ ++ [ARead l v']) s'.
  Proof.
    intros HR s0 as_ l v s H v'.
    apply trun_app_inv in H as (s1 & H1 & H2).
    apply trun_single_inv in H2 as (s2 & s3 & H2 & H3 & _).
    destruct (HR _ _ _ _ H3 v') as (s4 & H4).
    exists s4. eapply trun_app; [exact H1|].
    apply (trun_app S _ [] _ [ARead l v'] s4 H2).
    eapply trun_act; [exact H4| constructor].
  Qed.

End Actions.

Arguments action : clear implicits.
Arguments event : clear implicits.
Arguments trace : clear implicits.
Arguments lts : clear implicits.
Arguments program : clear implicits.

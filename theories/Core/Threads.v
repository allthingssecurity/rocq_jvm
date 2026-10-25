(** * Threads: the multi-threaded JVM as an interleaving of single-thread machine steps.

    Every thread has its own frame stack and its own monitor entry counts; the heap, the
    statics and the class-initialisation state are shared. A step picks one thread and runs
    one step of the single-thread machine [mstep_of] (Machine.v, unchanged) on it, after the
    thread layer has dealt with what needs more than one thread:
    - monitors (JLS 17.1, JVMS monitorenter/monitorexit and ACC_SYNCHRONIZED): a thread blocks
      on a monitor that another thread holds; synchronized methods enter their monitor on
      invocation and exit it on normal and abrupt return;
    - wait / notify / notifyAll (JLS 17.2): wait sets, release and reacquisition of the
      monitor with its entry count; IllegalMonitorStateException and IllegalArgumentException;
    - Thread.start / join / isAlive / currentThread / sleep / yield, through the native hooks
      of the model class java.lang.Thread (harness/jdkmodel/src/java/lang/Thread.java);
    - class initialisation (JLS 12.4.2): a thread that would start initialising a class whose
      initialisation another thread is running blocks until it is done.

    This is the sequentially consistent semantics. By the DRF-SC theorems of
    Concurrency/DRF.v, for data-race-free programs these are all behaviours the Java memory
    model allows; for racy programs the JMM allows more (TRUST.md). JDK model calls are atomic
    steps.

    Nondeterminism: which thread steps, which waiter [notify] wakes, and spurious wakeups /
    timeouts of [wait] (JLS 17.2.1). [tstep] is the relation over all of them; [trun] is an
    executable run for a given scheduler, used by the differential tests. *)

From Stdlib Require Import ZArith String List Bool.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
Import ListNotations.
Open Scope Z_scope.

Inductive tstatus : Type :=
| TRun
| TWait (l : Z) (cnt : Z) (deadline : option Z)  (** in the wait set of monitor [l]; [cnt] entries to restore;
                                       a timed wait ends at [deadline] (nanoTime) at the latest; the pc stays at the invoke *)
| TReacq (l : Z) (cnt : Z) (intr : bool)  (** notified, woken or interrupted ([intr]): must reacquire
                                       [l] [cnt] times, then wait returns or throws InterruptedException *)
| TSleep (intr : bool) (deadline : Z) (** in Thread.sleep until the clock reaches [deadline]; [intr]: interrupted *)
| TDone (v : option value)         (** run() / the entry method returned *)
| TDead (exn : Z).                 (** an exception left the thread *)

Record thread := mkth {
  th_obj : Z;                      (** its java.lang.Thread object; -1 for the main thread
                                       until Thread.currentThread() first asks for it *)
  th_frames : list cframe;
  th_locks : list (Z * Z);         (** monitor entry counts of this thread *)
  th_sync : list (nat * Z);        (** (frame depth, monitor) of the running synchronized methods *)
  th_status : tstatus;
}.

Record tmstate := mktm {
  tm_heap : heap;
  tm_next : Z;
  tm_statics : list (string * value);
  tm_inited : list string;
  tm_initing : list (string * nat);  (** class whose initialisation thread [i] is running *)
  tm_threads : list thread;
  tm_clock : Z;                       (** System.nanoTime: advanced by the scheduler *)
}.

Definition THREAD := "java/lang/Thread".
Definition IMSE := "java/lang/IllegalMonitorStateException".
Definition not_owner := ascii_units "current thread is not owner".
Definition main_units := ascii_units "main".
Definition set_field (k : string) (v : value) (fs : list (string * value)) : list (string * value) :=
  match set_assoc k v fs with Some fs' => fs' | None => fs end.

(** ** Helpers *)

Fixpoint nth_th (ts : list thread) (i : nat) : option thread :=
  match ts, i with
  | t :: _, O => Some t
  | _ :: r, S j => nth_th r j
  | nil, _ => None
  end.

Fixpoint set_th (ts : list thread) (i : nat) (t : thread) : list thread :=
  match ts, i with
  | _ :: r, O => t :: r
  | x :: r, S j => x :: set_th r j t
  | nil, _ => nil
  end.

(** Does a thread other than [i] hold monitor [l]? *)
Fixpoint held_other (ts : list thread) (k i : nat) (l : Z) : bool :=
  match ts with
  | nil => false
  | t :: r => (negb (Nat.eqb k i) && (0 <? lock_count (th_locks t) l)) || held_other r (S k) i l
  end.

Definition other_initing (tm : tmstate) (i : nat) (c : string) : bool :=
  existsb (fun e => String.eqb (fst e) c && negb (Nat.eqb (snd e) i)) (tm_initing tm).

(** The single-thread machine state of thread [i]: the shared part, its frames and its
    monitor counts. Classes another thread is initialising are not "started" in its view, so
    the machine makes the thread start their initialisation, which the thread layer turns into
    blocking. *)
Definition view (tm : tmstate) (i : nat) (t : thread) : mstate :=
  {| ms_heap := tm_heap tm; ms_next := tm_next tm; ms_statics := tm_statics tm;
     ms_inited := filter (fun c => negb (other_initing tm i c)) (tm_inited tm);
     ms_locks := th_locks t; ms_frames := th_frames t |}.

Definition clinit_classes (fs : list cframe) : list string :=
  map cf_class (filter cf_clinit fs).

(** Put a thread's new machine state back. *)
Definition merge (tm : tmstate) (i : nat) (t : thread) (s : mstate) (st : tstatus) (sync : list (nat * Z)) : tmstate :=
  let hidden := filter (fun c => other_initing tm i c) (tm_inited tm) in
  {| tm_heap := ms_heap s; tm_next := ms_next s; tm_statics := ms_statics s;
     tm_inited := app (ms_inited s) hidden;
     tm_initing := app (filter (fun e => negb (Nat.eqb (snd e) i)) (tm_initing tm))
                       (map (fun c => (c, i)) (clinit_classes (ms_frames s)));
     tm_threads := set_th (tm_threads tm) i
                     {| th_obj := th_obj t; th_frames := ms_frames s; th_locks := ms_locks s;
                        th_sync := sync; th_status := st |};
     tm_clock := tm_clock tm |}.

Definition with_locks (s : mstate) (ls : list (Z * Z)) : mstate :=
  {| ms_heap := ms_heap s; ms_next := ms_next s; ms_statics := ms_statics s;
     ms_inited := ms_inited s; ms_locks := ls; ms_frames := ms_frames s |}.

(** Exit the monitors of the synchronized methods whose frames are gone. *)
Fixpoint release_sync (sync : list (nat * Z)) (depth : nat) (ls : list (Z * Z)) : list (nat * Z) * list (Z * Z) :=
  match sync with
  | (d, l) :: r =>
      if Nat.ltb depth d then release_sync r depth ((l, lock_count ls l - 1) :: ls)
      else (sync, ls)
  | nil => (nil, ls)
  end.

Definition ACC_SYNCHRONIZED : Z := 32.
Definition is_sync_method (m : method) : bool := Z.testbit (m_access m) 5.

(** The result of trying one step of one thread. *)
Inductive tres : Type :=
| TRNext (tm : tmstate)
| TRBlocked                        (** cannot step now (monitor, join, class initialisation) *)
| TRStuck (why : string).

(** A step of the thread's frames through the single-thread machine, with the thread-layer
    bookkeeping: blocking on class initialisation, entry of synchronized methods, exit of
    their monitors, termination. *)
Definition machine_step (p : program) (mdl : model) (tm : tmstate) (i : nat) (t : thread) : tres :=
  let s := view tm i t in
  let depth0 := length (th_frames t) in
  let finish (s' : mstate) (st : tstatus) :=
      let (sync', ls') := release_sync (th_sync t) (length (ms_frames s')) (ms_locks s') in
      TRNext (merge tm i t (with_locks s' ls') st sync') in
  match mstep_of p mdl s with
  | MStuck why => TRStuck why
  | MReturn v s' => finish s' (TDone v)
  | MUncaught e s' => finish s' (TDead e)
  | MNext s' =>
      if existsb (other_initing tm i) (clinit_classes (ms_frames s')) then TRBlocked else
      match ms_frames s' with
      | top :: _ =>
          if Nat.ltb depth0 (length (ms_frames s')) && negb (cf_clinit top) && is_sync_method (cf_method top) then
            (* a synchronized method was invoked: enter its monitor *)
            let mon := if Z.testbit (m_access (cf_method top)) 3
                       then Some (intern s' (OCls (cf_class top)))
                       else match f_locals (cf_frame top) with
                            | VRef l :: _ => Some (l, s')
                            | _ => None
                            end in
            match mon with
            | None => TRStuck "synchronized method without receiver"
            | Some (l, s'') =>
                if held_other (tm_threads tm) 0 i l then TRBlocked
                else TRNext (merge tm i t (with_locks s'' ((l, lock_count (ms_locks s'') l + 1) :: ms_locks s''))
                               TRun ((length (ms_frames s''), l) :: th_sync t))
            end
          else finish s' TRun
      | nil => finish s' TRun
      end
  end.

(** The entry frame of a new thread: [this.run()] on its Thread object. *)
Definition run_code : code :=
  {| c_max_stack := 1; c_max_locals := 1; c_length := 5;
     c_instrs := [(0, Load KA 0);
                  (* the model class's runEntry: run(), then the uncaught-exception handler *)
                  (1, Invoke InvSpecial {| mr_class := THREAD; mr_name := "runEntry"; mr_desc := "()V"; mr_interface := false |});
                  (4, Return None)];
     c_handlers := nil |}.
Definition run_method : method := {| m_name := "<thread>"; m_desc := "()V"; m_access := 8; m_code := Some run_code |}.
Definition thread_entry (obj : Z) : cframe :=
  {| cf_class := "<thread>"; cf_method := run_method; cf_code := run_code; cf_rt := None;
     cf_frame := mkframe 0 nil [VRef obj]; cf_resume := None; cf_clinit := false |}.

Fixpoint find_thread (ts : list thread) (o : Z) : option thread :=
  match ts with
  | nil => None
  | t :: r => if Z.eqb (th_obj t) o then Some t else find_thread r o
  end.

Definition alive (t : thread) : bool :=
  match th_status t with TDone _ | TDead _ => false | _ => true end.

(** Wake one ([Some k]: the k-th, counted modulo the wait set) or all ([None]) waiters of [l]. *)
Fixpoint waiters (ts : list thread) (l : Z) : nat :=
  match ts with
  | nil => O
  | t :: r => (match th_status t with TWait l' _ _ => if Z.eqb l l' then 1 else 0 | _ => 0 end + waiters r l)%nat
  end.

Fixpoint wake (ts : list thread) (l : Z) (which : option nat) : list thread :=
  match ts with
  | nil => nil
  | t :: r =>
      match th_status t with
      | TWait l' c _ =>
          if Z.eqb l l' then
            match which with
            | None => {| th_obj := th_obj t; th_frames := th_frames t; th_locks := th_locks t;
                         th_sync := th_sync t; th_status := TReacq l c false |} :: wake r l None
            | Some O => {| th_obj := th_obj t; th_frames := th_frames t; th_locks := th_locks t;
                           th_sync := th_sync t; th_status := TReacq l c false |} :: r
            | Some (S k) => t :: wake r l (Some k)
            end
          else t :: wake r l which
      | _ => t :: wake r l which
      end
  end.

Definition set_clock (tm : tmstate) (c : Z) : tmstate :=
  {| tm_heap := tm_heap tm; tm_next := tm_next tm; tm_statics := tm_statics tm; tm_inited := tm_inited tm;
     tm_initing := tm_initing tm; tm_threads := tm_threads tm; tm_clock := c |}.

Definition with_threads (tm : tmstate) (ts : list thread) : tmstate :=
  {| tm_heap := tm_heap tm; tm_next := tm_next tm; tm_statics := tm_statics tm; tm_inited := tm_inited tm;
     tm_initing := tm_initing tm; tm_threads := ts; tm_clock := tm_clock tm |}.

(** Continue thread [i] after an intercepted invoke: pc [nx], operand stack [st]. *)
Definition advance (tm : tmstate) (i : nat) (t : thread) (top : cframe) (rest : list cframe) (nx : pc)
           (st : list value) (ls : list (Z * Z)) (status : tstatus) : tmstate :=
  with_threads tm (set_th (tm_threads tm) i
    {| th_obj := th_obj t; th_frames := set_frame top (mkframe nx st (f_locals (cf_frame top))) :: rest;
       th_locks := ls; th_sync := th_sync t; th_status := status |}).

Definition throw_in (p : program) (tm : tmstate) (i : nat) (t : thread) (cls : string) (msg : option (list Z)) : tres :=
  match (match msg with Some _ => throw_msg p (view tm i t) cls msg | None => throw_new p (view tm i t) cls end) with
  | MNext s' => TRNext (merge tm i t s' TRun (th_sync t))
  | MUncaught e s' =>
      let (sync', ls') := release_sync (th_sync t) O (ms_locks s') in
      TRNext (merge tm i t (with_locks s' ls') (TDead e) sync')
  | MReturn _ _ => TRStuck "throw returned"
  | MStuck w => TRStuck w
  end.

(** The interrupt status: the field [interrupted] of the thread's Thread object (the model
    class sets it in interrupt() and clears it in interrupted()). *)
Definition intr_key (fs : list (string * value)) : string := own_key THREAD "interrupted" fs.

Definition intr_flag (tm : tmstate) (t : thread) : bool :=
  match tm_heap tm (th_obj t) with
  | Some (OObj _ fs) => match assoc (intr_key fs) fs with Some (VInt b) => negb (b =? 0) | _ => false end
  | _ => false
  end.

Definition clear_intr (tm : tmstate) (t : thread) : tmstate :=
  match tm_heap tm (th_obj t) with
  | Some (OObj c fs) =>
      {| tm_heap := upd (tm_heap tm) (th_obj t) (OObj c (set_field (intr_key fs) (VInt 0) fs));
         tm_next := tm_next tm; tm_statics := tm_statics tm; tm_inited := tm_inited tm;
         tm_initing := tm_initing tm; tm_threads := tm_threads tm; tm_clock := tm_clock tm |}
  | _ => tm
  end.

Definition with_status (t : thread) (ls : list (Z * Z)) (st : tstatus) : thread :=
  {| th_obj := th_obj t; th_frames := th_frames t; th_locks := ls; th_sync := th_sync t; th_status := st |}.

Definition IE := "java/lang/InterruptedException".

(** The interrupt of thread object [o]: a thread in a wait set leaves it (and will throw
    InterruptedException), a sleeping thread wakes up and throws it; a joining thread sees the
    status when it next tries to step. *)
Fixpoint interrupt_in (ts : list thread) (o : Z) : list thread :=
  match ts with
  | nil => nil
  | t :: r =>
      if Z.eqb (th_obj t) o then
        match th_status t with
        | TWait l c _ => with_status t (th_locks t) (TReacq l c true) :: r
        | TSleep _ d => with_status t (th_locks t) (TSleep true d) :: r
        | _ => t :: r
        end
      else t :: interrupt_in r o
  end.

Definition throw_null (p : program) (tm : tmstate) (i : nat) (t : thread) (cls : string) : tres :=
  match throw_msg p (view tm i t) cls None with
  | MNext s' => TRNext (merge tm i t s' TRun (th_sync t))
  | MUncaught e s' =>
      let (sync', ls') := release_sync (th_sync t) O (ms_locks s') in
      TRNext (merge tm i t (with_locks s' ls') (TDead e) sync')
  | MReturn _ _ => TRStuck "throw returned"
  | MStuck w => TRStuck w
  end.

(** One step of thread [i]; [ch] chooses the waiter a [notify] wakes. *)
Definition thread_step0 (p : program) (mdl : model) (ch : nat) (tm : tmstate) (i : nat) : tres :=
  match nth_th (tm_threads tm) i with
  | None => TRBlocked
  | Some t =>
  match th_status t with
  | TDone _ | TDead _ | TWait _ _ None => TRBlocked
  | TWait l c (Some d) =>
      (* a timed wait times out once the clock has reached its deadline (JLS 17.2.1) *)
      if tm_clock tm <? d then TRBlocked
      else TRNext (with_threads tm (set_th (tm_threads tm) i (with_status t (th_locks t) (TReacq l c false))))
  | TReacq l c intr =>
      (* reacquire the monitor, then finish the wait invoke (still at its pc) *)
      if held_other (tm_threads tm) 0 i l then TRBlocked
      else
        let t1 := with_status t ((l, c) :: th_locks t) TRun in
        let tm1 := with_threads tm (set_th (tm_threads tm) i t1) in
        if intr then throw_null p (clear_intr tm1 t1) i t1 IE
        else match th_frames t1 with
             | top :: rest =>
                 match fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) with
                 | Some (Invoke _ mr, nx) =>
                     let n := if String.eqb (mr_desc mr) "(J)V" then 2%nat else 1%nat in
                     match pop_n n (f_stack (cf_frame top)) with
                     | Some (_, r) => TRNext (advance tm1 i t1 top rest nx r ((l, c) :: th_locks t) TRun)
                     | None => TRStuck "wait: stack"
                     end
                 | _ => TRStuck "wait: no invoke"
                 end
             | nil => TRStuck "wait: no frame"
             end
  | TSleep intr d =>
      (* the sleep ends when interrupted, or once its time has passed (never early: JLS 17.10) *)
      let t1 := with_status t (th_locks t) TRun in
      let tm1 := with_threads tm (set_th (tm_threads tm) i t1) in
      if intr then throw_in p (clear_intr tm1 t1) i t1 IE (Some (ascii_units "sleep interrupted"))
      else if tm_clock tm <? d then TRBlocked
      else match th_frames t1 with
           | top :: rest =>
               match fetch (c_instrs (cf_code top)) (f_pc (cf_frame top)) (c_length (cf_code top)) with
               | Some (Invoke _ _, nx) =>
                   match f_stack (cf_frame top) with
                   | _ :: r => TRNext (advance tm1 i t1 top rest nx r (th_locks t) TRun)
                   | nil => TRStuck "sleep: stack"
                   end
               | _ => TRStuck "sleep: no invoke"
               end
           | nil => TRStuck "sleep: no frame"
           end
  | TRun =>
  match th_frames t with
  | nil => TRBlocked
  | top :: rest =>
  let f := cf_frame top in
  match fetch (c_instrs (cf_code top)) (f_pc f) (c_length (cf_code top)) with
  | Some (Monitorenter, _) =>
      match f_stack f with
      | VRef l :: _ => if held_other (tm_threads tm) 0 i l then TRBlocked else machine_step p mdl tm i t
      | _ => machine_step p mdl tm i t
      end
  | Some (Invoke k mr, nx) =>
      let st := f_stack f in
      if String.eqb (mr_class mr) THREAD && String.eqb (mr_name mr) "start0" then
        match st with
        | VRef o :: r =>
            let nt := {| th_obj := o; th_frames := [thread_entry o]; th_locks := nil; th_sync := nil; th_status := TRun |} in
            let tm' := advance tm i t top rest nx r (th_locks t) TRun in
            TRNext (with_threads tm' (app (tm_threads tm') [nt]))
        | _ => TRStuck "Thread.start0: receiver"
        end
      else if String.eqb (mr_class mr) THREAD && String.eqb (mr_name mr) "join0" then
        match st with
        | VRef o :: r =>
            if intr_flag tm t then throw_null p (clear_intr tm t) i t IE else
            match find_thread (tm_threads tm) o with
            | Some u => if alive u then TRBlocked else TRNext (advance tm i t top rest nx r (th_locks t) TRun)
            | None => TRNext (advance tm i t top rest nx r (th_locks t) TRun)
            end
        | _ => TRStuck "Thread.join0: receiver"
        end
      else if String.eqb (mr_class mr) THREAD && String.eqb (mr_name mr) "isAlive0" then
        match st with
        | VRef o :: r =>
            let b := match find_thread (tm_threads tm) o with Some u => alive u | None => false end in
            TRNext (advance tm i t top rest nx (VInt (if b then 1 else 0) :: r) (th_locks t) TRun)
        | _ => TRStuck "Thread.isAlive0: receiver"
        end
      else if String.eqb (mr_class mr) THREAD && String.eqb (mr_name mr) "currentThread" then
        if 0 <=? th_obj t then TRNext (advance tm i t top rest nx (VRef (th_obj t) :: st) (th_locks t) TRun)
        else
          match instance_fields p 64 THREAD with
          | None => TRStuck "Thread.currentThread: java.lang.Thread model not loaded"
          | Some fs =>
              (* the main thread: name "main", normal priority, started *)
              let nm := tm_next tm in
              let o := nm + 1 in
              let fs' := set_field "started" (VInt 1) (set_field "priority" (VInt 5) (set_field "name" (VRef nm) fs)) in
              let tm1 := {| tm_heap := upd (upd (tm_heap tm) nm (OStr main_units)) o (OObj THREAD fs'); tm_next := o + 1;
                            tm_statics := tm_statics tm; tm_inited := tm_inited tm; tm_initing := tm_initing tm;
                            tm_threads := set_th (tm_threads tm) i
                              {| th_obj := o; th_frames := th_frames t; th_locks := th_locks t;
                                 th_sync := th_sync t; th_status := TRun |};
                            tm_clock := tm_clock tm |} in
              match nth_th (tm_threads tm1) i with
              | Some t1 => TRNext (advance tm1 i t1 top rest nx (VRef o :: st) (th_locks t) TRun)
              | None => TRStuck "currentThread"
              end
          end
      else if String.eqb (mr_class mr) THREAD && String.eqb (mr_name mr) "interrupt0" then
        match st with
        | VRef o :: r =>
            let tm' := advance tm i t top rest nx r (th_locks t) TRun in
            TRNext (with_threads tm' (interrupt_in (tm_threads tm') o))
        | _ => TRStuck "Thread.interrupt0: receiver"
        end
      else if String.eqb (mr_class mr) THREAD && String.eqb (mr_name mr) "sleep0" then
        if intr_flag tm t then throw_in p (clear_intr tm t) i t IE (Some (ascii_units "sleep interrupted"))
        else match st with
             | VLong ms :: _ =>
                 TRNext (with_threads tm (set_th (tm_threads tm) i
                   (with_status t (th_locks t) (TSleep false (tm_clock tm + ms * 1000000)))))
             | _ => TRStuck "Thread.sleep0: argument"
             end
      else if String.eqb (mr_class mr) THREAD && String.eqb (mr_name mr) "yield0" then
        TRNext (advance tm i t top rest nx st (th_locks t) TRun)
      else if String.eqb (mr_class mr) "java/lang/System" && String.eqb (mr_desc mr) "()J"
              && (String.eqb (mr_name mr) "nanoTime" || String.eqb (mr_name mr) "currentTimeMillis") then
        (* the clock of the run; currentTimeMillis counts from 0 here (the epoch is not modelled) *)
        let v := if String.eqb (mr_name mr) "nanoTime" then tm_clock tm else tm_clock tm / 1000000 in
        TRNext (advance tm i t top rest nx (VLong v :: st) (th_locks t) TRun)
      else if (String.eqb (mr_name mr) "wait" && (String.eqb (mr_desc mr) "()V" || String.eqb (mr_desc mr) "(J)V"))
              && negb (match k with InvStatic => true | _ => false end) then
        let timed := String.eqb (mr_desc mr) "(J)V" in
        match (if timed then match st with VLong ms :: VRef o :: r => Some (o, ms, r) | VLong _ :: VNull :: _ => None | _ => None end
               else match st with VRef o :: r => Some (o, 0, r) | _ => None end) with
        | None => throw_in p tm i t NPE None
        | Some (o, ms, r) =>
            (* Object.wait(long) checks the timeout first, then the VM checks the owner, then
               the interrupt status (JDK 21, ObjectMonitor::wait) *)
            let c := lock_count (th_locks t) o in
            if ms <? 0 then throw_in p tm i t "java/lang/IllegalArgumentException" (Some (ascii_units "timeout value is negative"))
            else if c <=? 0 then throw_in p tm i t IMSE (Some not_owner)
            else if intr_flag tm t then throw_null p (clear_intr tm t) i t IE
            else TRNext (with_threads tm (set_th (tm_threads tm) i (with_status t ((o, 0) :: th_locks t) (TWait o c (if timed && (0 <? ms) then Some (tm_clock tm + ms * 1000000) else None)))))
        end
      else if (String.eqb (mr_name mr) "notify" || String.eqb (mr_name mr) "notifyAll") && String.eqb (mr_desc mr) "()V"
              && negb (match k with InvStatic => true | _ => false end) then
        match st with
        | VRef o :: r =>
            if lock_count (th_locks t) o <=? 0 then throw_in p tm i t IMSE (Some not_owner)
            else
              let tm' := advance tm i t top rest nx r (th_locks t) TRun in
              let n := waiters (tm_threads tm') o in
              let which := if String.eqb (mr_name mr) "notify" then Some (Nat.modulo ch (Nat.max n 1)) else None in
              TRNext (with_threads tm' (wake (tm_threads tm') o which))
        | _ => throw_in p tm i t NPE None
        end
      else machine_step p mdl tm i t
  | _ => machine_step p mdl tm i t
  end
  end
  end
  end.

(** A thread that terminates wakes the threads waiting on its Thread object (as the JDK's
    exit notifies, which timed join relies on). *)
Definition after_step (tm : tmstate) (i : nat) : tmstate :=
  match nth_th (tm_threads tm) i with
  | Some u => if alive u then tm else with_threads tm (wake (tm_threads tm) (th_obj u) None)
  | None => tm
  end.

Definition thread_step (p : program) (mdl : model) (ch : nat) (tm : tmstate) (i : nat) : tres :=
  match thread_step0 p mdl ch tm i with
  | TRNext tm' => TRNext (after_step tm' i)
  | r => r
  end.

(** ** The step relation: some thread steps, or a waiting thread wakes up spontaneously
    (a spurious wakeup or a timeout, JLS 17.2.1), or time passes (System.nanoTime). *)
Inductive tstep (p : program) (mdl : model) : tmstate -> tmstate -> Prop :=
| ts_thread : forall tm i ch tm', thread_step p mdl ch tm i = TRNext tm' -> tstep p mdl tm tm'
| ts_wakeup : forall tm i t l c b, nth_th (tm_threads tm) i = Some t -> th_status t = TWait l c b ->
    tstep p mdl tm (with_threads tm (set_th (tm_threads tm) i
      {| th_obj := th_obj t; th_frames := th_frames t; th_locks := th_locks t; th_sync := th_sync t;
         th_status := TReacq l c false |}))
| ts_tick : forall tm d, 0 <= d -> tstep p mdl tm (set_clock tm (tm_clock tm + d)).

(** ** Executable runs, for the differential tests. *)

Inductive tresult : Type :=
| TRValue (v : option value) (tm : tmstate)    (** the main thread (index 0) returned *)
| TRExc (exn : Z) (tm : tmstate)               (** an exception left the main thread *)
| TRDeadlock (tm : tmstate)                     (** no thread can step and main has not finished *)
| TRStuckRun (why : string)
| TROutOfFuel.

(** A scheduler gives, for each step number, a number; the run picks the thread at that
    position (modulo the number of threads that can step) and uses it for notify too. *)
Definition scheduler := nat -> nat.

Fixpoint steppable (p : program) (mdl : model) (ch : nat) (tm : tmstate) (i n : nat) : list (nat * tres) :=
  match n with
  | O => nil
  | S n' => match thread_step p mdl ch tm i with
            | TRBlocked => steppable p mdl ch tm (S i) n'
            | r => (i, r) :: steppable p mdl ch tm (S i) n'
            end
  end.

Fixpoint nth_choice {A} (l : list A) (k : nat) : option A :=
  match l, k with
  | x :: _, O => Some x
  | _ :: r, S j => nth_choice r j
  | nil, _ => None
  end.

(** The earliest deadline of a timed wait or a sleep. *)
Fixpoint next_deadline (ts : list thread) : option Z :=
  match ts with
  | nil => None
  | t :: r =>
      let d := match th_status t with TWait _ _ (Some d) => Some d | TSleep false d => Some d | _ => None end in
      match d, next_deadline r with
      | Some x, Some y => Some (Z.min x y)
      | Some x, None => Some x
      | None, e => e
      end
  end.

(** Executable runs. Each step advances the clock by 1 ns. When no thread can step, the clock
    jumps to the earliest deadline (then the timed waits and sleeps that end there can step; the
    scheduler chooses among them). With [ticks], jumping to the earliest deadline is also one of
    the scheduler's choices at every step (the last one), so a schedule can let a timeout happen
    while other threads are still running. *)
Fixpoint trun_gen (ticks : bool) (p : program) (mdl : model) (sch : scheduler) (fuel : nat) (step : nat) (tm : tmstate)
  : tresult :=
  match option_map th_status (nth_th (tm_threads tm) O) with
  | Some (TDone v) => TRValue v tm
  | Some (TDead e) => TRExc e tm
  | _ =>
    match fuel with
    | O => TROutOfFuel
    | S fuel' =>
      let ch := sch step in
      let cands := steppable p mdl ch tm O (length (tm_threads tm)) in
      let future := match next_deadline (tm_threads tm) with
                    | Some d => if tm_clock tm <? d then Some d else None
                    | None => None
                    end in
      match cands with
      | nil =>
          match future with
          | Some d => trun_gen ticks p mdl sch fuel' (S step) (set_clock tm d)
          | None => TRDeadlock tm
          end
      | _ =>
        let n := length cands in
        let k := Nat.modulo ch (if ticks && match future with Some _ => true | None => false end then S n else n) in
        if Nat.eqb k n then
          match future with
          | Some d => trun_gen ticks p mdl sch fuel' (S step) (set_clock tm d)
          | None => TRStuckRun "scheduler"
          end
        else
        match nth_choice cands k with
        | Some (_, TRNext tm') => trun_gen ticks p mdl sch fuel' (S step) (set_clock tm' (tm_clock tm' + 1))
        | Some (_, TRStuck w) => TRStuckRun w
        | _ => TRStuckRun "scheduler"
        end
      end
    end
  end.

Definition trun := trun_gen false.

(** The initial state: one thread running the entry frame of [Machine.entry_state]. *)
Definition tm_of (s : mstate) : tmstate :=
  {| tm_heap := ms_heap s; tm_next := ms_next s; tm_statics := ms_statics s; tm_inited := ms_inited s;
     tm_initing := nil;
     tm_threads := [{| th_obj := -1; th_frames := ms_frames s; th_locks := ms_locks s; th_sync := nil;
                       th_status := TRun |}];
     tm_clock := 0 |}.

(** As [call_static_threads], from clock reading [clock0] (nanoseconds; currentTimeMillis is
    [clock0 / 10^6]): a theorem chooses the time at which the run starts. *)
Definition call_static_threads_at (p : program) (mdl : model) (sch : scheduler) (fuel : nat) (clock0 : Z)
           (cls name desc : string) (args : list value) : tresult :=
  match entry_state cls name desc args with
  | Some s => trun p mdl sch fuel O (set_clock (tm_of s) clock0)
  | None => TRStuckRun "entry: bad descriptor or arguments"
  end.

(** The general entry point: start clock [clock0], and [ticks] as in [trun_gen]. *)
Definition call_static_threads_gen (p : program) (mdl : model) (sch : scheduler) (fuel : nat) (clock0 : Z) (ticks : bool)
           (cls name desc : string) (args : list value) : tresult :=
  match entry_state cls name desc args with
  | Some s => trun_gen ticks p mdl sch fuel O (set_clock (tm_of s) clock0)
  | None => TRStuckRun "entry: bad descriptor or arguments"
  end.

Definition call_static_threads (p : program) (mdl : model) (sch : scheduler) (fuel : nat) (cls name desc : string)
           (args : list value) : tresult :=
  match entry_state cls name desc args with
  | Some s => trun p mdl sch fuel O (tm_of s)
  | None => TRStuckRun "entry: bad descriptor or arguments"
  end.

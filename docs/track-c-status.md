# Track C status: threads and the Java Memory Model

Updated 2026-10-24. Rocq 9.3.0 + rocq-stdlib 9.2.0, stdlib only. Plan: `docs/track-c-survey.md`, section 3.

**No `Axiom`, no `Admitted`, no `Abort` in `theories/Concurrency/`.** `Print Assumptions` prints
"Closed under the global context" for every theorem listed below.

## Files

Dependency order for `_RocqProject`: `Events`, `Order`, `Executions`, `DRF`, `Examples`.

| File | Lines | Compile time | Content |
|---|---|---|---|
| `theories/Concurrency/Events.v` | 227 | 0.8 s | actions, events, thread-local LTS, `receptive`, runs (`trun`), programs (earlier agent) |
| `theories/Concurrency/Order.v` | 304 | 1.4 s | `acyclic`, `toposort` (every finite decidable acyclic relation has an injective ranking), least elements, lemmas about filters over `seq` |
| `theories/Concurrency/Executions.v` | 347 | 1.1 s | executions, po/so/sw/hb/rf, well-formedness, hb-consistency, races, SC, executions of a program, correctly synchronized programs |
| `theories/Concurrency/DRF.v` | 915 | 2.7 s | theorem (a); sub-executions; theorem (b) |
| `theories/Concurrency/Examples.v` | 311 | 2.2 s | the JLS 17.4.8 out-of-thin-air example |

Times are wall clock for a single `rocq compile -Q theories JVM <file>` on this machine.

## Definitions (Executions.v)

Everything is parametric in the types `L V M C X` (locations, values, monitors, spawn payloads, external
labels) of Events.v and in three section parameters:
- `vol : L -> bool`: which locations are volatile;
- `init : L -> V`: the default value of each location;
- `M_eq_dec`: decidable equality of monitors (used only to count lock actions).

**Execution** (`execution`): `ex_n` (events are numbered below it), `ex_dom : nat -> bool` (which numbers
are events), `ex_lab` (thread id and action of each event), `ex_ws : nat -> option nat` (JLS's write-seen
function W; `None` means the read sees the default value).

**Representation choices** (deviations in form, not in content, from JLS 17.4):
1. The numbering is a *presentation order*. Program order `po` is the numbering restricted to each thread,
   and the synchronization order `so` is the numbering restricted to synchronization actions. Plain events
   can be numbered anywhere consistent with po. The numbering says nothing about which write a read sees.
   Any finite JLS execution can be presented this way: so is total on synchronization actions and
   consistent with po, so po ∪ so is acyclic and can be linearised. This is a claim about the encoding;
   it is not formalised.
2. Default writes are not events. `ex_ws r = None` means r sees `init l`. This matches the JLS reading in which
   the default writes happen-before everything (17.4.4: they synchronize-with the first action of every
   thread). It also avoids the Aspinall–Ševčík problem that default writes are not synchronization actions.
3. A data race needs two *plain* accesses (Jacobs's fix, as in Lochbihler). Well-formedness forces volatile
   locations to be accessed only by volatile actions, so the only pairs this excludes are volatile–volatile ones.
4. The SC total order must also be consistent with `so`, so it respects mutual exclusion. Aspinall and Ševčík
   note that the JLS definition omits this.
5. Not modelled: interruption (the 17.4.4 interrupt edges), `wait`/`notify`, final fields (17.5), VarHandle
   access modes, infinite executions.

| Name | JLS | Meaning |
|---|---|---|
| `po`, `so` | 17.4.3, 17.4.4 | as above |
| `sw` | 17.4.4 | unlock m → later lock m; volatile write v → later volatile read v; `ASpawn t` → `AStart` of t; `AFinish` of t → `AJoin t` |
| `hb` | 17.4.5 | `clos_trans (po ∪ sw)` |
| `rf E w r` | 17.4.7 | `D E r /\ ex_ws E r = Some w` |
| `wf` | 17.4.7 | record of 12 conditions. (1) each read sees a write in the execution to the same variable with the value read, or the default value. W is defined only on reads. (2) `volatile_ok`. (3) mutual exclusion: when t locks m, every other thread has as many unlocks as locks of m before it (`wf_mutex`), and a thread unlocks only monitors it holds (`wf_unlock`). (5) so-consistency for volatile reads (`wf_so_vol`). Thread structure: `AStart` is exactly the first action of each thread, `AFinish` is the last, a spawn precedes all actions of the spawned thread, and a join comes after the joined thread's `AFinish`. Condition (4), intra-thread consistency, is `exec_of` below. |
| `hb_consistent` | 17.4.5 | for every read r: not hb(r, W(r)), and no write w to the variable with hb(W(r), w) and hb(w, r). For the default value: no write to the variable hb-before r |
| `race`, `race_free` | 17.4.5 | two different plain accesses to one variable, at least one a write, unordered by hb |
| `sees_last`, `sc_order`, `sequentially_consistent` | 17.4.3 | an injective ranking consistent with po and so in which every read sees the last earlier write to its variable (or the default value, if no write precedes it) |
| `thread_ids`, `proj`, `thread_init`, `exec_of` | 17.4.7(4) | the actions of each thread, in po order, form a run (`trun`) of the program's LTS from the thread's initial state: `p_init` for the main thread, `tinit c` for a thread started by an `ASpawn t c` in the execution |
| `correctly_synchronized` | 17.4.5 | every well-formed, SC execution of the program is race-free |

## Theorems

| Theorem | File | Statement |
|---|---|---|
| `toposort` | Order.v | `forall n R, (forall i j, {R i j}+{~R i j}) -> (forall i j, R i j -> i < n /\ j < n) -> acyclic R -> exists ord, (forall i j, i < n -> j < n -> ord i = ord j -> i = j) /\ (forall i j, R i j -> ord i < ord j)` |
| `drf_execution_sc_order` | DRF.v | `wf vol init M_eq_dec E -> hb_consistent E -> race_free E -> sc_order init E (fun i => i)` |
| **`drf_execution_sc`** (theorem (a)) | DRF.v | `wf vol init M_eq_dec E -> hb_consistent E -> race_free E -> sequentially_consistent init E` |
| **`drf_sc_no_thin_air`** (theorem (b)) | DRF.v | `forall (L_eq_dec : forall l l' : L, {l = l'} + {l <> l'}) P E, receptive (p_lts P) -> correctly_synchronized vol init M_eq_dec P -> wf vol init M_eq_dec E -> exec_of P E -> hb_consistent E -> acyclic (fun i j => po E i j \/ so E i j \/ rf E i j) -> sequentially_consistent init E /\ race_free E` |
| `prog_correctly_synchronized` | Examples.v | the 17.4.8 program (main spawns `r1 = x; if (r1 != 0) y = 1` and `r2 = y; if (r2 != 0) x = 1`) is correctly synchronized |
| `oota_wf`, `oota_exec`, `oota_hb_consistent` | Examples.v | the execution `oota` with r1 = r2 = 1 is well-formed, an execution of the program, and hb-consistent |
| `oota_not_sc` | Examples.v | `~ sequentially_consistent init0 oota` |
| **`hb_model_not_drf_sc`** | Examples.v | `exists P E, receptive (p_lts P) /\ correctly_synchronized vol0 init0 unit_eq_dec P /\ wf vol0 init0 unit_eq_dec E /\ exec_of P E /\ hb_consistent E /\ ~ sequentially_consistent init0 E` |
| **`oota_cyclic`** | Examples.v | `~ acyclic (fun i j => po oota i j \/ so oota i j \/ rf oota i j)` (cycle 5 -po→ 6 -rf→ 9 -po→ 10 -rf→ 5) |
| `prog_drf_sc` | Examples.v | an instance of (b) for the example program |
| `oota_racy` | Examples.v | `~ race_free oota` (follows from (a), because `oota` is not SC) |

### Proof structure
- **(a)** The SC order is the presentation order. A plain read r with W(r) = w races with w unless the two are
  hb-ordered. hb-consistency excludes hb(r, w), so hb(w, r), and hb is contained in the numbering. Any other
  write w' to the same variable is hb-ordered with both w and r (race-freedom), and hb-consistency forbids
  w <hb w' <hb r. So w' comes before w or after r. A volatile read sees the so-latest write because of
  `wf_so_vol`. All case splits on hb are done under a goal of `False`, so the proof needs no excluded middle.
- **(b)** `toposort` gives a linear extension T of po ∪ so ∪ rf. sw ⊆ so, so hb ⊆ T. The proof shows, by
  strong induction on T, that every read sees the T-latest write. Take a plain read r for which this fails,
  and let x be the T-latest write before r.
  * `redirect` builds the SC execution made of the T-prefix before r plus r changed to read x
    (`trun_snoc_read`, which uses receptiveness). This is an SC execution of P, so it is race-free, so
    hb(x, r).
  * `cut` builds the SC execution made of the T-prefix alone. It is race-free, so hb(W(r), x).
  * Together, hb(W(r), x) and hb(x, r) contradict hb-consistency.

  Volatile reads are never the failing read, because T restricted to synchronization actions is so.
  Both constructions are instances of `sub` (closed under po and so predecessors; only plain read values
  change). `wf_sub`, `thread_ids_sub` and `thread_init_sub` move well-formedness and intra-thread consistency
  to them. T itself is the SC witness for E. This proof does not use theorem (a).

## What is assumed

No axioms. The theorems take the following as explicit hypotheses or parameters:
- `vol`, `init`, `M_eq_dec` (section parameters). `L_eq_dec` is a hypothesis of (b) only; it is needed to
  compute the T-latest write.
- `receptive (p_lts P)` in (b): the thread-local semantics accepts any value for a *plain* read. Any
  interpreter that treats the read value as an input satisfies this (see the design below).
- The meta-level claim in representation choice 1 above, that every finite JLS execution can be presented
  with so as the numbering on synchronization actions.

Known looseness:
- `exec_of` does not require spawned thread ids to be fresh or distinct. This lets
  `correctly_synchronized` quantify over a few more executions than the JLS, which makes the hypothesis
  of (b) slightly stronger. The example program still satisfies it.
- The model "hb + acyclic(po ∪ so ∪ rf)" is strictly stronger than the JMM (it forbids load buffering).
  So (b) is **not** DRF-SC for the JLS model. That needs the 17.4.8 commit model (next item).

## Next steps (not started)
1. JLS 17.4.8 justification/commit sequences (port by hand from JinjaThreads, BSD). The plan is DRF-SC for
   legal executions via SC completions, reusing theorem (a) unchanged.
2. Connection to the single-threaded machine (design below).
3. Final fields (17.5), `wait`/`notify`, interrupts, VarHandle modes (JAM-style).

## Design: connecting to `theories/Core/Machine.v` (notes only; Machine.v unchanged)

`Machine.v` is a deterministic step function `mstep_of p mdl s : mstep` on a state `mstate` with a shared
heap (`ms_heap`), statics (`ms_statics`), class-initialisation set (`ms_inited`), monitor counts
(`ms_locks`) and the frame stack (`ms_frames`). The plan is to obtain an `lts` (Events.v) without editing
Machine.v.

**Locations.** Use `location Addr Field Static` from Events.v:
- `getfield`/`putfield`: `LField a f` (`a : Z` is the heap address, `f` the field name; the class must
  be included in `f`, because of hidden fields with the same name);
- `getstatic`/`putstatic`: `LStatic (static_key c n)`;
- `xaload`/`xastore`: `LArray a i`.

`vol` comes from `ACC_VOLATILE` (0x0040) of the resolved field. Array elements are never volatile.
`init` must be the default of the location's type (`default_of`). So the location carries its descriptor,
or `init` is computed from the class files.

**Thread-local state and reads ("read-refresh").** A thread's state is a full single-thread `mstate`. Its heap
and statics act as a *thread-local cache* of memory. A step that executes `getfield` on location l with
label `ARead l v` (or `AVRead` if l is volatile):
1. first overwrites the cache at l with v;
2. then runs `mstep_of`.

The read value is an input that the step accepts for every v, so `receptive` holds by construction. A
`putfield`/`putstatic`/`xastore` step runs `mstep_of` and is labelled `AWrite l v`, where v is the stored
value after `narrow_store`. Every other instruction is a silent step (`None`). The step relation needs a
small classifier that maps the instruction at the current pc and the operand stack to the accessed location.

**Immutable metadata.** Object class, array element type and array length are fixed at allocation.
`getfield`'s check `h l = Some (OObj _ _)` and `arraylength` read only this metadata, so they are not memory
actions. Allocation needs fresh addresses per thread: partition `ms_next` by thread id, or make allocation
an action. With fresh addresses, the default-value semantics (`ex_ws = None` sees `init l`) coincides with
JLS's per-allocation default writes. This includes racy publication, where another thread may read the
default value of a field of a newly published object, which the hb model permits.

**Monitors.**
- `monitorenter` on reference a is `ALock a`; `monitorexit` is `AUnlock a`.
- `synchronized` methods emit `ALock`/`AUnlock` on invoke and return. This includes return by exception;
  `unwind` must emit the unlocks.
- The thread keeps its own reentrancy counts (the existing `ms_locks`, now per thread). This matches
  `wf_unlock`, and the IllegalMonitorStateException branch stays thread-local.
- Mutual exclusion between threads is not checked by the thread. It comes from `wf_mutex` (in the JMM) or
  from the interleaving.

**Threads.**
- `Thread.start()` (a JDK model) emits `ASpawn t a`, where `a` is the `Thread` object reference.
- `tinit a s0` builds a state with one frame for `a.run()`.
- `Thread.join()`/`isAlive() == false` emit `AJoin t`.
- Each thread's first step emits `AStart`. Normal return of the bottom frame (`MReturn`) or an uncaught
  exception (`MUncaught`) emits `AFinish`.

**Shared JVM-internal state needs care.**
- Class initialisation (`ms_inited`, `<clinit>`) is shared, and JLS 12.4.2 synchronises it with a
  per-class initialisation lock. First version: require all classes used by more than one thread to be
  initialised before the first `ASpawn`, as a hypothesis of the theorems. Later: model the 12.4.2 procedure
  with `ALock`/`AUnlock` on a per-class monitor.
- The string intern table: treat it as initialised before threads start, or as synchronised.
- JDK models (`mdl`) that read or write the heap (StringBuilder, arraycopy) must be split into actions. Until
  then, a model call on a shared object is `Stuck`. That is sound: no claim is made about such runs.

**Sanity theorem to prove first.** For a program with a single thread and no spawns, SC executions
correspond exactly to runs of `mstep_of` (each read sees the last write). This shows the read-refresh LTS
does not change single-threaded behaviour, and it lets Track A results be reused.

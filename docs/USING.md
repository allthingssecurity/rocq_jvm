# Using the JVM model on your own bytecode

This guide is for a person or an agent session that wants to use the model to confirm or refute a bug in compiled
Java: a candidate from TLA+, deterministic simulation testing (DST), fuzzing or code review. Camel is the running
example, but nothing here is Camel-specific.

Repository: https://github.com/allthingssecurity/rocq_jvm (branch `main`).

## 1. Setup (once)

| Need | Version | Note |
|---|---|---|
| Rocq | `rocq-core 9.3.0`, `rocq-stdlib 9.2.0` | `opam switch create rocq 5.3.0 && opam install rocq-core.9.3.0 rocq-stdlib.9.2.0 ocamlfind zarith` |
| OCaml | 5.3.0 + ocamlfind + zarith | only for the differential drivers |
| JDK | 21 (HotSpot) | `javac --release 17 -g` produces the class files; `java` runs the HotSpot side of the differential test |
| Python 3 | any | `tools/classdump.py`, `harness/gen_inputs.py`, `harness/compare.py` |

```sh
git clone https://github.com/allthingssecurity/rocq_jvm.git rocq-jvm && cd rocq-jvm
eval $(opam env --switch rocq --set-switch)
rocq makefile -f _RocqProject -o Makefile.rocq
make -f Makefile.rocq theories/Extract.vo       # model only (Core, Loader, Jdk): ~10 min
harness/build.sh                                # everything, incl. the Camel proofs and the 3 drivers: ~1 h
# differential-test prerequisites (not committed):
mkdir -p harness/work/slf4j && (cd harness/work/slf4j && unzip -q -o /path/to/slf4j-api-2.0.x.jar 'org/*')
javac -d harness/work harness/java/*.java && java -cp harness/work UnicodeTables harness/work/unicode-21.txt
```

To build just the model and drivers without the Camel proofs, run `harness/build_driver.sh` (it does not build `threads_main`; see `harness/build.sh` for that line).

Resource notes: a full `make -j1` takes about an hour and peaks around 3 GB. Do not run two full builds at once.

## 2. The workflow: a bug candidate becomes a kernel-checked counterexample

### Step 1. Write a driver: one static method that replays the scenario
Write a small Java class whose static method builds the objects, performs the call sequence from the TLA+/DST trace,
and returns an `int`/`long`/`String` summarizing the outcome. Use only ordinary Java; do **not** stub the code under
test. For a package-private class, put the driver in the same package. Example (`harness/camel/bugs/FilterScenario.java`):

```java
public static String afterLookahead(int wrap) {
    Backing b = new Backing();                       // a tiny finite Iterator over {"a","b","c"}
    Iterator<String> it = wrap == 0 ? b : new FilterIterator<>(b);
    it.next(); it.hasNext(); it.remove();
    return b.remaining();                            // "bc" is right, "ac" is the bug
}
```

Always include a control (here `wrap == 0`, the plain iterator) so that the theorem shows the contract and the
violation side by side.

### Step 2. Compile the exact production source
```sh
tools/build-camel-classes.sh <label> <camel-git-dir> <commit> <module-src-dir> <path/To/Class.java> ...
# e.g. tools/build-camel-classes.sh util-x ~/src/camel bd4d2ba2 core/camel-util/src/main/java org/apache/camel/util/FilterIterator.java
javac --release 17 -g -cp classes/<label> -d classes/<label>-scen MyScenario.java     # the driver, separately
```
This records the commit, javac version and SHA-256 of every class in `classes/<label>/BUILD-INFO`.

### Step 3. Bring the bytes into Rocq
```sh
tools/dump-program.sh classes/<label> MyMain        # -> theories/Classes/MyMain_*.v and MyMain.v (Definition files)
tools/dump-program.sh classes/<label>-scen MyScen
```
Add the printed file names to `_RocqProject` (before `theories/Camel/...`), then run `rocq makefile -f _RocqProject -o Makefile.rocq`.
The `.v` files contain the raw bytes only; the class-file parser runs inside Rocq.

### Step 4. State the outcome as a theorem (template: `theories/Camel/NewBugs.v`)
```coq
From Stdlib Require Import ZArith String List.
From JVM.Core Require Import Int Instr Desc Semantics Machine.
From JVM.Loader Require Import ClassFile.
From JVM.Jdk Require Import Strings Jdk.
From JVM.Classes Require MyMain MyScen.
Import ListNotations. Open Scope Z_scope.

Definition p : program := ltac:(let p := eval vm_compute in
  (match load_program (MyMain.files ++ MyScen.files) with Some p => p | None => [] end) in exact p).
Definition mdl := jdk_model p bug_e.           (* copy bug_u / bug_e from NewBugs.v: ASCII Unicode tables, logging off *)

Theorem my_bug : call_static p mdl 10000 "MyScenario" "afterLookahead" "(I)Ljava/lang/String;" [VInt 1]
                 = (* the observed result *) _ .
```
In practice, write a projection (`str_result`, `int_result` in NewBugs.v) and prove
`projection (call_static ...) = Some <value>` by `vm_compute. reflexivity.` Finish with `Print Assumptions my_bug.`,
which must print *Closed under the global context*.

Results of `call_static`:
- `MRValue (Some v) s` / `MRValue None s`: a normal return.
- `MRExc l s`: an uncaught exception; `exn_class s l` gives its class.
- `MRStuck why`: **a model gap, not a bug in your code.** The string names the missing piece, for example
  "no model for java/nio/file/Files.readAllBytes". Either model it or change the driver to avoid it.
  Many JDK models are Java classes run as bytecode (`classes/jdkmodel`, `classes/threadmodel`): put them
  on the class path after your own classes, or calls into them are STUCK as missing classes.
- `MROutOfFuel`: increase the fuel (the `10000` above).

To pass objects instead of building them in Java, construct the heap yourself and run `mrun`. See
`duration_start` in NewBugs.v, which places a `java/time/Duration` object at address 1.

### Step 5. Cross-check against HotSpot
Before you trust a model result on code that uses new parts of the JDK, run the same driver on random inputs through
the extracted model and through HotSpot:
```sh
echo "classes/<label>-scen:classes/<label>:classes/jdkmodel MyScenario afterLookahead (I)Ljava/lang/String; fresh" > harness/targets-mine.txt
MODE=machine harness/difftest.sh harness/targets-mine.txt 500
```
It must report `mismatches=0`. HotSpot runs with the first directory and the real JDK. The model also loads the
following directories; `classes/jdkmodel` holds the clean-room java.util models (ArrayList, HashMap, ...).

## 3. Concurrency, locks, atomics and time

> **Availability.** The thread layer and the `java.util.concurrent` model classes are developed in the
> model session's working copy. They are on GitHub `main` only from the push that adds `theories/Core/Threads.v`
> (check: `ls theories/Core/Threads.v harness/threads/src`). A checkout without those files has a
> single-threaded machine only: there `new ReentrantLock()` and the atomics are STUCK. The hunt sessions' open
> requests are tracked in `docs/hunt-requests.md` (R1-R9), with what each push delivers.

The thread layer (`theories/Core/Threads.v`) gives an interleaving semantics: monitors, wait/notify,
interrupts, start/join, sleep, timed waits, and a clock for `System.nanoTime`/`currentTimeMillis`.
Clean-room model classes (`harness/threads/src`, built into `classes/threadmodel`) provide `Thread`, `ThreadLocal`,
`ReentrantLock` with `Condition`, `AtomicInteger/Long/Boolean/Reference`, `CountDownLatch`, `Semaphore`,
`TimeUnit`, `Executors`, `ThreadPoolExecutor`, `ScheduledThreadPoolExecutor`, blocking queues, `Future`/`FutureTask`,
`Timer`/`TimerTask`.
`ConcurrentHashMap` is a model class in `harness/jdkmodel`. The semantics is sequentially consistent: it explores
interleavings, but not the extra weak-memory outcomes of racy programs.

**Use the thread layer even for sequential code that touches these classes.** The single-thread entry point
`call_static` does not run `Thread.currentThread`, the clock or the lock models; `call_static_threads` with a
scheduler does, and a program that starts no thread simply has one thread.

```coq
call_static_threads p mdl sch fuel "MyScenario" "race" "(I)I" [VInt 0]   (* : tresult *)
```
- `sch : nat -> nat` is the schedule. At step k it runs runnable thread number `sch k mod (number of runnable
  threads)`. A DST seed or a TLA+ counterexample trace becomes a concrete `sch` (defined by cases on k), so the
  interleaving is replayed exactly and checked by `vm_compute`.
- Possible results: `TRValue`, `TRExc`, `TRDeadlock` (no thread can step: a deadlock witness), `TRStuckRun`
  (model gap) and `TROutOfFuel`.
- The clock starts at 0 (or at the value given to `call_static_threads_at`) and advances by 1 ns per step; when
  every thread waits with a timeout or sleeps, it jumps to a deadline. `Thread.sleep(ms)` ends only once `ms` have
  passed, so a driver makes time pass by sleeping.
- Also modelled: `ThreadPoolExecutor` (core/max sizes, keep-alive, the four rejection policies, hooks) with
  `ScheduledThreadPoolExecutor` as its subclass, `LinkedBlockingQueue`, `ArrayBlockingQueue`, `SynchronousQueue`,
  `DelayQueue`, `Semaphore`, fair and non-fair `ReentrantLock`, `Timer`/`TimerTask`, uncaught-exception handlers,
  `ConcurrentHashMap`, `TreeMap`/`TreeSet`, `String.format` (no floating-point or date conversions).
- `call_static_threads_gen p mdl sch fuel clock0 ticks ...`: with `ticks = true` the schedule may also let time
  pass (jump to the earliest deadline) at any step, so timeouts can fire while other threads run.
- `CompletableFuture` (the JDK's order of dependent actions; pass an explicit executor: the default async
  executor depends on the host, so its threads' names are unknown), `StampedLock`, `CopyOnWriteArrayList/Set`,
  `ConcurrentLinkedQueue/Deque`.
- Identity hash codes come from `j_ihash` of the `jenv` (TRUST.md 5c), and the per-run salt of `Set.of`/`Map.of`
  from `j_seed 0` (TRUST.md 5d): fix them in a counterexample, quantify over them in a proof. Every `jenv` record
  now needs `j_seed := ...` (e.g. `fun _ => 0`).
- Not modelled: `invokeAny`, timed `invokeAll`, `Condition.awaitUntil`, Phaser/CyclicBarrier/Exchanger/
  ForkJoinPool, parallel streams.
- Put `classes/threadmodel` (and `classes/jdkmodel`) on the class path after the code under test; compile
  drivers with `harness/threads/build.sh`.
- Differential test: `MODE=threads harness/difftest.sh targets.txt 300`. Each input runs under 6 schedulers;
  `NONDET` means the outcome depends on the schedule.

The intended combination: TLA+ or DST finds a bad interleaving on a design model, and the thread layer replays it
on the **real bytecode** under that schedule.

## 4. Going further: proofs for every input

A counterexample needs only `vm_compute`. A proof that the fixed code is correct for **every** input is more work.
Templates:
- `theories/Camel/WalCanUpdate.v`: one method, all int inputs (symbolic execution with `Core/Logic.v` lemmas);
- `theories/Camel/CimHash.v`: a loop over any String (an invariant proved by induction);
- `theories/Camel/WalRing.v` and `CimSession.v`: a whole class over every call sequence (a representation invariant).

## 5. What to trust, and the known gaps
- `TRUST.md` lists everything a result depends on: the model's rules, the JDK models, Rocq's kernel and `vm_compute`.
- Not modelled: the weak behaviours of racy programs under the Java memory model, class loaders and
  the verifier, and parts of the JDK (I/O, streams, floating-point formatting, regex lookbehind, java.time
  construction). The modelled library is listed in `TRUST.md` 5b and `STATUS.md`.
  Code that reaches them returns `MRStuck "no model for ..."`. It never silently returns a wrong answer.
- `STATUS.md` lists what has been tested against HotSpot, and how much.

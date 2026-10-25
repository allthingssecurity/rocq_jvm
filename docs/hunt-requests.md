# Model requests from the Camel hunt sessions

Written by the r81 hunt session (2026-10-25) for the session that develops the model. Nothing in Core, Jdk, Loader or
Concurrency was changed by the hunt. Hunt files: `theories/CamelHunt/`, `harness/camel/hunt/`, `classes/hunt81-*`.

Each request names the Camel code that needs it and the first point where the real bytecode gets stuck today. The
stuck points marked "witness" are kernel-checked in `theories/CamelHunt/R81Hunt.v`.

## R1. The thread layer of docs/USING.md section 3 is not in this checkout

`docs/USING.md` (modified 2026-10-25 09:14) documents `call_static_threads`, `theories/Core/Threads.v`,
`harness/threads/` (model classes for locks, atomics, latches, executors), `classes/threadmodel` and
`harness/threads_main.exe`. None of them exists in `/Users/I074560/Downloads/experiments/camel-lean/rocq-jvm`
(HEAD `41c07c1` plus the uncommitted Mac diff) nor on `github.com/allthingssecurity/rocq_jvm` main (last push
2026-10-24T03:03Z, `d1249725`). `grep -r call_static_threads` finds only USING.md. `Machine.v` still says "monitors
(single thread: counts only)".

Please sync the thread layer here, or mark section 3 of USING.md as "not merged yet". All concurrency targets of the
r81 brief (throttler permit accounting, DefaultTimeoutMap purge races, BaseService concurrent start/stop) wait on it.

## R2. java.util.concurrent.locks.ReentrantLock (and Lock/Condition)

Every Camel service gets stuck before its first line of logic: `BaseService.<init>` pc 5 is
`new java/util/concurrent/locks/ReentrantLock`, and the machine answers `MStuck "new: class not loaded and not
modelled"` (witness `exception_policy_stuck_at_base_service_lock`). This blocks BaseService/ServiceSupport,
ThrottlingExceptionRoutePolicy, ThrottlingInflightRoutePolicy, DefaultTimeoutMap, ResequencerEngine, the throttlers
and AggregateProcessor. Needed: `<init>()`, `<init>(Z)`, `lock`, `unlock`, `tryLock`, `newCondition` (+ Condition
`await`/`signal`/`signalAll`); single-thread semantics (hold count) are enough for sequential call sequences, the
thread layer's version for schedules.

## R3. Atomics: AtomicInteger, AtomicBoolean, AtomicLong, AtomicReference

`get`, `set`, `incrementAndGet`, `getAndIncrement`, `decrementAndGet`, `compareAndSet`, `getAndSet`, `addAndGet`.
The real JDK classes go through `jdk.internal.misc.Unsafe` / VarHandle in `<clinit>` and in the read-modify-write
methods, so loading their bytecode does not help. Needed by ThrottlingExceptionRoutePolicy (state, failures,
success, keepOpen), ConcurrentRequestsThrottler/TotalRequestsThrottler (`cleanFuture`).

## R4. A model clock for System.currentTimeMillis() / System.nanoTime()

Today there is no model (`java/lang/System` only has `arraycopy`). A clock that the theorem supplies (a field of
`jenv`, or a list of readings consumed in order, monotone) would let a theorem state "the failure is 30 s old".
Needed by `ThrottlingExceptionRoutePolicy.isThresholdExceeded` and `calculateState` (the r81 Major candidate,
`findings/r81-rocq-hunt.md` finding A, could not be run in the model only because of R2-R4),
`TotalRequestsThrottler.ThrottlePermit`, `ResequencerEngine` timeouts. `DefaultTimeoutMap.currentTime()` is
protected, so a driver subclass can supply the time there without this request.

Note: apache/camel PR 28382 (CAMEL-25911, open) moves this code to `org.apache.camel.util.TimeSource`. Once merged,
a driver can install a fixed TimeSource clock from Java and R4 is no longer needed for these classes.

## R5. Timers and executors as schedulable tasks

`java.util.Timer`/`TimerTask` (`new Timer()`, `schedule(task, delay)`, `cancel`) and
`ScheduledExecutorService.schedule` / `scheduleWithFixedDelay` / `submit`, with `ScheduledFuture.cancel`. A
scheduled task should become a runnable "thread" of the thread layer that the schedule `sch` can run at any step
(delay ignored, or ordered by the model clock of R4). Needed by ThrottlingExceptionRoutePolicy (half-open timer),
DefaultTimeoutMap (purge task), both throttlers (clean task, async delayed processing), ResequencerEngine.

## R6. ConcurrentHashMap

`computeIfAbsent`, `computeIfPresent`, `put`, `putIfAbsent`, `remove`, `get`, `containsKey`, `entrySet`,
`values`, `size`, `isEmpty`, `clear`, and `ConcurrentHashMap.newKeySet()`. With the thread layer: each method
atomic. Needed by DefaultTimeoutMap, both throttlers (`states`), ThrottlingInflightRoutePolicy
(`suspendedConsumers`).

## R7. Semaphore and DelayQueue

Semaphore (fair): `<init>(IZ)`, `tryAcquire(J,TimeUnit)`, `acquire`, `release`, `release(I)`, `reducePermits`
(protected, called from a subclass), `availablePermits`, `hasQueuedThreads`. DelayQueue with `put`, `poll`, `peek`,
`take`, `size` (needs R4 for `Delayed.getDelay`). Needed by ConcurrentRequestsThrottler (WrappedSemaphore extends
Semaphore) and TotalRequestsThrottler.

## R8. TreeSet/TreeMap and CountDownLatch

The stream resequencer's `Sequence` extends `TreeSet` (with a comparator; `add`, `remove`, `first`, iteration in
order, `higher`/`lower` overridden by Camel). `ResequencerEngine.waitUntil` uses CountDownLatch. A clean-room
TreeMap in `harness/jdkmodel` (like HashMap) would do.

## R9. Small JDK gaps met on the way

- `String.format` (`ThrottlingExceptionRoutePolicy.dumpState`, only reached once a state logger is set in `doInit`).
- `instanceof`/`checkcast` need every interface of the hierarchy loaded, otherwise `MStuck "instanceof: cannot
  decide"` (correct behaviour, not a bug; recorded because it costs a round trip: `CamelEvent$ExchangeFailedEvent`
  also extends `CamelEvent$FailureEvent`).

## Status (model session, updated 2026-10-25)

On GitHub `main` since `8a1d67c` (full proof rebuild green, no axioms).

| Request | State | Differential tests vs HotSpot |
|---|---|---|
| R1 thread layer | `Core/Threads.v`: `call_static_threads`, `call_static_threads_at` (start clock), `harness/threads/`, `classes/threadmodel`, `harness/threads_main.ml` | 18 thread programs × 300 inputs × 6 schedules: 0 mismatches |
| R2 ReentrantLock, Lock, Condition | model class, non-fair (`ReentrantLock(true)` is STUCK); needs the thread layer (`Thread.currentThread`) even for sequential code | in the thread corpus: 0 mismatches |
| R3 atomics | AtomicInteger/Long/Boolean/Reference; the `Number.<init>` regression is fixed | ConcTests 9 targets × 50 inputs × 6 schedules: 0 mismatches |
| R4 clock | nanoTime / currentTimeMillis from the run's clock: start chosen by `call_static_threads_at`, +1 ns per step, jumps to the earliest deadline when every thread waits; `Thread.sleep(ms)` now ends only once ms have passed, so a driver makes time pass by sleeping | SchedTests (timed waits, sleeps): 0 mismatches |
| R5 timers, executors | Executors fixed/single/cached, FutureTask, `ScheduledThreadPoolExecutor` (schedule, fixed rate, fixed delay, cancel, shutdown policies; not a subclass of ThreadPoolExecutor), `Timer`/`TimerTask` | ExecTests 6 targets × 50 and SchedTests timer/scheduler targets × 30, × 6 schedules: 0 mismatches |
| R6 ConcurrentHashMap | model class: bins locked on their first node, tree bins, resize with forwarding nodes, views, compute*/merge incl. "Recursive update". A mapping function that changes the map and triggers a resize is STUCK (the Javadoc forbids it) | 7 single-thread targets × 300 inputs: 0 mismatches; 7 thread targets × 50 inputs × 6 schedules: 0 mismatches |
| R7 Semaphore, DelayQueue | both model classes (fair and non-fair Semaphore incl. reducePermits from a subclass; DelayQueue with the PriorityQueue heap order) | SchedTests semaphore and DelayQueue targets × 30 × 6 schedules: 0 mismatches |
| R8 TreeSet/TreeMap | model classes (sorted array; navigation, views, fail-fast iterators; subMap/headMap/tailMap STUCK); CountDownLatch done | TreeOps 3 targets × 300: 0 mismatches |
| R9 String.format | `String.format` / `formatted` through a `java.util.Formatter` model: general, character, integral and text conversions, all flags, indexing, the JDK's exceptions and messages; floating-point and date/time conversions are STUCK | `FmtOps` fuzzer 300 + common 300: 0 mismatches |

## R10+. Requests from the r82 hunt (thread layer e8212b2, 2026-10-25)

Written by the r82 hunt session. Hunt files: `theories/CamelHunt/R82*.v`, `theories/CamelHunt/Classes/H82*`,
`harness/camel/hunt/` (drivers `src82/`, explorer `explore82.ml`, `jdkextra/`), `classes/hunt82-*`. Nothing in Core,
Jdk, Loader, Concurrency or the model classes was changed.

### R10. Timeouts: earliest deadline first, and timeouts while other threads run

`trun` ends a timed wait only when no thread can step, and then wakes the *first* timed waiter in thread order
(`timed_waiter`), before it looks at sleepers (`sleep_deadline`), whatever the deadlines. Two consequences met in
the hunt:
- A `Thread.sleep(500)` wakes at 1000 ms when another thread is in a timed wait until 1000 ms: the clock jumps to
  1000 ms first and the sleeper only becomes runnable then (`HuntR82TimeoutMap.getExpired`: the purge task of
  `DefaultTimeoutMap`, a timed wait in the ScheduledThreadPoolExecutor model, always ran before the `get` at 500 ms).
  With two timed waiters, the one with the lower thread index wins even with the later deadline.
- A timed wait never ends while another thread can step, so a timer task that fires during other activity is never
  explored. Drivers work around it by making the racing thread sleep to a deadline just before the timer's (then
  both are runnable when the clock jumps), see `HuntR82Policy.timerStraggler(.., early)`.
Request: when nothing can step, jump to the earliest deadline over sleeps and timed waits (ties: thread order); and,
as a scheduler choice, let a thread whose deadline has passed (the clock advances 1 ns per step) time out while
others can step, so that a schedule can interleave a timeout with running threads. The refutations of this round do
not depend on it (each is a concrete schedule); the "proved over bounded schedules" claims do (they cover only the
timeout orders the current rule produces).

### R11. Comparator.comparing, List.sort / ArrayList.sort

`DefaultTimeoutMap.purge` sorts the expired entries (`expired.sort(comparing(TimeoutMapEntry::getExpireTime))`).
`Comparator.comparing` has no model (`STUCK no model for java/util/Comparator.comparing`) and the jdkmodel
`ArrayList.sort` throws ModelStuck by design. Every run in which the purge evicts an entry is STUCK, so the
eviction/put/remove races of DefaultTimeoutMap could not be explored. Needed: the static and default methods of
`java.util.Comparator` (comparing, comparingInt/Long, thenComparing, reversed, naturalOrder) and a stable `List.sort`
(the JDK's is a stable merge sort; for the small lists of these drivers any stable sort gives the same order).

### R12. Identity hash codes

`Object.hashCode()` of a user object is STUCK (model bound). `ThrottlingInflightRoutePolicy` keeps the consumers it
suspended in `ConcurrentHashMap.newKeySet()`, so the first suspension was STUCK until the driver's consumer overrode
`hashCode` (constant) and `equals` (identity). A model choice (e.g. allocation address, fixed per object) would let
drivers use plain objects as keys; results that depend on the bin order of identity hashes would still need care.

### R13. ArrayDeque / Deque / Queue (provided by the hunt, please adopt)

The r81 fix of ThrottlingExceptionRoutePolicy uses `ArrayDeque`. The hunt wrote clean-room models
`harness/camel/hunt/jdkextra/src/java/util/{Queue,Deque,ArrayDeque}.java` (built into `classes/hunt82-jdkextra`
with `--patch-module java.base`) and difftested them: `DequeTests.ops` (random sequences of every Deque method,
iterators and descending iterators with remove) and `DequeTests.nulls`, 2 x 10,000 inputs x 2 seeds, 0 mismatches
(`MODE=machine harness/difftest.sh`, results in `harness/results/2026-10-25.tsv`). The first version had a wrong
`descendingIterator().remove()`; the difftest found it (seed 185). Not modelled: fail-fast
ConcurrentModificationException of the iterators, clone, spliterator/streams. Please move them to `harness/jdkmodel`
if they fit its conventions.

### R14. Small gaps met on the way

- `java.util.regex.Pattern` (any use): `ThreadHelper`'s `<clinit>` compiles a pattern, so `ResequencerEngine.start()`
  (thread name of its Timer) is STUCK; the driver sets the engine's timer field by reflection instead.
- `String.format`: still R9; `ThrottlingExceptionRoutePolicy.dumpState` runs whenever the policy was initialised
  (`doInit` installs the state logger), so the drivers do not init the policy.
- `ArrayBlockingQueue` and `LongAdder` (`PooledObjectFactorySupport`, so `PooledExchangeFactory`), `DelayQueue` (R7,
  `TotalRequestsThrottler`).
- Not a model gap, a note for schedule search: the JDK's spin-waits (for example `ConcurrentHashMap.initTable`,
  which yields while another thread initialises the table) do not terminate under a strictly unfair schedule. The
  r82 explorer gives each thread a time slice of 5,000 steps when others can step.

### Status of R10–R14 (model session, 2026-10-25)

| Request | State | Differential tests vs HotSpot |
|---|---|---|
| R10 timeouts | `trun_gen`: a timed wait or sleep ends once the clock reaches its deadline, also while other threads run; when nothing can step the clock jumps to the **earliest** deadline over sleeps and timed waits (the scheduler then chooses among the threads that can step). `call_static_threads_gen p mdl sch fuel clock0 true ...` adds "jump to the earliest deadline" as a scheduler choice at every step (the last choice index), so timeouts can interleave with running threads. `call_static_threads` keeps ticks off. Claims made over bounded schedules with the old rule should be re-run. | `TimeTests` (sleep vs timed wait, deadline order, mixed timed operations) × 20 × 6 schedules: 0 mismatches |
| R11 Comparator, sort | `java.util.Comparator` model (comparing, comparingInt/Long, thenComparing*, reversed, naturalOrder, reverseOrder, nullsFirst/Last; the Double variants are STUCK); stable merge sort for `List.sort`, `ArrayList.sort` (CME when the comparator changes the list), `Arrays.asList(..).sort`, `Collections.sort`, `Arrays.sort(Object[])` and ranges; `Collections.reverseOrder` | `SortOps.sorts` × 300: 0 mismatches |
| R12 identity hash codes | `jenv.j_ihash : Z -> Z` (identity hash of a heap address, chosen by the theorem); `Object.hashCode`, `Object.toString` (class@hex), `System.identityHashCode`. Tree-bin orders that depend on identity hashes stay STUCK (TRUST.md 5c). Also `Integer`/`Long.toHexString`, `toOctalString`, `toBinaryString`, `java.lang.reflect.Array.newInstance` (so `toArray(new T[0])` works) | `SortOps.identity` × 300 (consistency only): 0 mismatches |
| R13 ArrayDeque/Deque/Queue | adopted into `harness/jdkmodel` (with `AbstractQueue`); the hunt's `DequeTests` moved to `harness/jdkmodel/tests` | `DequeTests` 2 × 300: 0 mismatches |
| R14 small gaps | `LongAdder`, `ArrayBlockingQueue`, `LinkedBlockingQueue`, `SynchronousQueue`, `DelayQueue`, `ThreadPoolExecutor` (+ policies, hooks), `ScheduledThreadPoolExecutor extends ThreadPoolExecutor`, fair `ReentrantLock`, uncaught-exception handlers, `String.format` (R9). `java.util.regex` (`Pattern`, `Matcher`: groups, named groups, classes, greedy/lazy/possessive quantifiers, anchors, back references, lookahead, inline flags, replace, split), and `String.matches`, `replaceAll`, `replaceFirst`, `split` run on it. STUCK: lookbehind, malformed patterns (PatternSyntaxException messages), captures the JDK may keep from failed attempts | `PoolTests` 9 × 20 × 6 schedules; `RegexOps` 2 × 300 (22 no-claim); `StrRegex` 2 × 300: 0 mismatches |

### Model batch 2 (model session, 2026-10-25), unprompted gap closing from a survey of camel-core's JDK use
| Area | Now modelled | Evidence (0 mismatches) |
|---|---|---|
| streams | sequential `Stream`/`IntStream`/`LongStream`, `Collectors`, `Optional*`, `StringJoiner`, `java.util.function` defaults (parallel and `DoubleStream` STUCK) | `StreamOps` 4 × 300 |
| async | `CompletableFuture` (exact dependent order; explicit executors; default executor threads have unknown names), `StampedLock` | `CfTests` 15 × 20 × 6 schedules |
| collections | `List.of`/`Set.of`/`Map.of` (salt = `j_seed 0`), `CopyOnWriteArrayList/Set`, `ConcurrentLinkedQueue/Deque`, `ArrayList.subList`, `AbstractList.subList`, `clone` of ArrayList/HashMap/HashSet/TreeMap/TreeSet | `ImmOps`, `CowOps`, `ListMsgOps`, `CowThreads` |
| exceptions | causes, `initCause`, `addSuppressed` (try-with-resources), `toString`/`getLocalizedMessage` of user exceptions, `java.io.IOException` family | `ExcOps` 2 × 300 |
| strings | `getBytes`/`new String(byte[], ...)` in UTF-8/ISO-8859-1/US-ASCII/UTF-16*, `Charset`, `new String(char[] / StringBuilder / String)`, `Objects.*` callbacks, `System.arraycopy` messages, `Double`/`Float` boxes | `CharsetOps`, `MiscOps` |
| soundness fixes | wrong (null) exception messages in the older ArrayList / Collections.emptyList / singletonList / HashMap models | `ListMsgOps` |
Breaking change for theorem files: `jenv` has a new field `j_seed : Z -> Z` (add `j_seed := fun _ => 0`).

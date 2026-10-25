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

| Request | State in the model session's working copy | On GitHub |
|---|---|---|
| R1 thread layer | `Core/Threads.v`, `call_static_threads`, `harness/threads/`, `classes/threadmodel`, `harness/threads_main.ml`; differential tests: 18 thread programs × 300 inputs × 6 schedules, 0 mismatches | with the next push |
| R2 ReentrantLock, Lock, Condition | model class (non-fair; `ReentrantLock(true)` is STUCK); runs under the thread layer (needs `Thread.currentThread`) | next push |
| R3 atomics | AtomicInteger/Long/Boolean/Reference model classes; a regression found while answering this (`Number.<init>` STUCK after a resolution change) is fixed | next push |
| R4 clock | nanoTime/currentTimeMillis in the thread layer: start 0, +1 ns per step, jumps to the earliest deadline when all threads wait. A clock supplied by the theorem: not yet | partly, next push |
| R5 timers, scheduled executors | Executors fixed/single/cached + FutureTask only; Timer and ScheduledExecutorService: not yet | no |
| R6 ConcurrentHashMap | clean-room model class (bins locked on their first node, tree bins, resize with forwarding, views, compute*/merge incl. "Recursive update"); single-thread tests 7 targets, 0 mismatches so far; thread-layer tests in progress | next push |
| R7 Semaphore, DelayQueue | not yet | no |
| R8 TreeSet/TreeMap | not yet (CountDownLatch: done, R1) | no |
| R9 String.format | not yet | no |

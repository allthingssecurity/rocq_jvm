# rocq-jvm: a JVM bytecode semantics in Rocq, for proofs about compiled Camel methods

Started 2026-10-23. Goal in 2-3 weeks: a large single-threaded JVM core in Rocq, a loader from real `.class` files,
and proofs about compiled Camel methods for all inputs (not bounded like JBMC, see findings/r79-jbmc-pilot.md).
Long-term scope (user, 2026-10-23: "I want all but gradually"): the whole JVM, including threads and the Java
memory model, natives, the JDK class library, reflection, class loading and `invokedynamic`. Phases 1-5 build the
single-threaded core first (weeks 1-3); phases 6-11 add the rest, each on top of a core that already proves real
Camel methods.

Trust base, kept explicit: Rocq kernel + our JVM model + the loader. The model is cross-checked against the real JVM
(differential testing: random inputs run in the extracted model and on HotSpot, results compared) at every phase.

## Phases (each ends with a checkpoint that must pass before the next starts)

| Phase | Days | Scope | Checkpoint |
|---|---|---|---|
| 1 | 1-3 | Values (int/long wraparound with exact JVMS semantics: idiv/irem/ishl masks, i2b/i2c/l2i), frames, operand stack, locals; ~60 int/long/branch/local opcodes; `tableswitch`/`lookupswitch`; small-step + fuel interpreter; extraction to OCaml for the differential test | `.class` loader (Java tool -> Rocq term) for one method; wal `TransactionLog.canUpdate` proved on the fixed bytecode and REFUTED on main's bytecode (calibration); differential test >= 100k random inputs agrees with HotSpot |
| 2 | 4-6 | Heap: objects, fields (get/putfield, get/putstatic), arrays of all primitive types + references with bounds/null/negative-size exceptions; exceptions as values, exception tables, athrow, handlers | Proofs about array/index methods (StringHelper helpers, `CaseInsensitiveMap` internals) with "no uncaught exception" + functional spec |
| 3 | 7-9 | Calls: invokestatic/invokespecial/invokevirtual/invokeinterface, method resolution and virtual dispatch over a loaded class hierarchy; constructors; `instanceof`/`checkcast` | Multi-method proofs: `CaseInsensitiveMap` put/remove/compact preserves "behaves like an ordered map" and the slot bound, for all operation sequences |
| 4 | 10-12 | JDK models: `String` (as char array + hash), `StringBuilder`, `Integer`/`Long`/`Math` statics, `System.arraycopy`, a few `java.util` classes as verified Rocq models; javac's indy string concat lowered by the loader | Proofs over Camel util code that uses Strings (path/URI helpers) |
| 5 | 13-15 | float/double (IEEE 754 via Flocq), remaining opcodes, proof automation (tactics for symbolic execution) | Opcode coverage report vs JVMS ch. 6; 3+ Camel fixes proved; write-up |
| 6 | weeks 4-5 | Threads, sequentially consistent first: interleaving semantics, `monitorenter/exit` and `synchronized`, `wait`/`notify`, `Thread.start/join`, volatile | Prove a small Camel concurrent class race-free or find the race (e.g. a lock-guarded counter, `ReentrantLock` modelled); differential runs vs HotSpot with forced schedules |
| 7 | weeks 5-7 | Java memory model: happens-before, data races, the JMM consistency rules (follow the published Rocq/Isabelle JMM formalisations; DRF-SC theorem as the first proof target) | Prove DRF-SC for the model; classify a known racy Camel field (e.g. a non-volatile flag read across threads) |
| 8 | weeks 6-8 | `java.util.concurrent` models (atomics, `ConcurrentHashMap`, executors, locks) as verified models against their specs | Proofs of Camel lifecycle code that uses them (start/stop races like the ones found by DST and the lifecycle harness) |
| 9 | weeks 7-9 | Class loading and initialisation (`<clinit>` order, resolution, linking errors), `invokedynamic` and `LambdaMetafactory`, string-concat bootstrap | Load and prove methods that use lambdas and static init |
| 10 | weeks 8-10 | Reflection (`Class`, `Method.invoke`, fields), natives as axiomatised specs with a list of every native assumed | A Camel method that uses reflection (bean binding helpers) |
| 11 | ongoing | JDK library: model classes on demand, each checked against the real JDK by differential tests, until the classes Camel core uses are covered | Coverage report of JDK classes used by camel-util / camel-support |

## Schedule compression (user, 2026-10-23: 10 weeks is too long; run it in its own session)
Three tracks in parallel instead of one phase after another, all on one shared core:
- Track A (interpreter): phases 1, 2, 3, 5, 9 in order.
- Track B (environment): bytecode loader, HotSpot differential-test harness, then JDK models (phase 4, 8, 11) against
  stub interfaces that track A fills in.
- Track C (concurrency theory): JMM and thread semantics (phases 6, 7) developed against an abstract
  action/event interface, reusing existing published Rocq/Coq formalisations wherever they exist, then joined to
  track A's interpreter.
Target: the single-threaded core proving Camel methods by end of week 1, threads + JMM joined by end of week 3,
reflection and the JDK coverage drive after that. Max 2 Rocq builds at once on this Mac (see Rules).

## Rules
- Rocq build under the same resource limits as Maven (one heavy job at a time; take camel-lean/.mvn-lock; -Xmx/ulimit caps).
- Every proof statement says exactly what is proved (which bytecode, which spec, which assumptions).
- Camel `.class` files come from `javac --release 17` of the exact source at a recorded commit.

# rocq-jvm status

Rocq 9.3.0 + rocq-stdlib 9.2.0. Build: `make` (uses `rocq makefile`, `-j1`; about 16 minutes, most of it the
kernel-computed whole-class checks in `WalScenario.v` and `CimScenario.v`). Trust base: `TRUST.md`. Opcode table: `docs/opcode-coverage.md`.
Differential-test logs: `harness/results/*.tsv`, `harness/work/*.log` (not committed). Updated 2026-10-25 (model-gaps merged: field/method resolution, initialisation order, invokedynamic bootstraps, exception messages).

Every theorem listed below: `Print Assumptions` = "Closed under the global context" (no axioms, nothing admitted).

## What the model covers (tracks A + B)

| Layer | Files | State |
|---|---|---|
| int/long arithmetic (JVMS 2.3, 6.5) | `Core/Int.v` | done; corner cases as `Example`s |
| float/double, IEEE 754 binary32/64, round-to-nearest-even, subnormals, JVMS NaN/conversion rules | `Core/Float.v` | done (written by the float agent); 0 mismatches on 250,000 inputs per op, JIT and `-Xint`; `docs/float-status.md` |
| frame: operand stack (all dup/pop/swap forms), locals (two-slot long/double), branches, switches, returns with `ireturn` narrowing | `Core/Semantics.v` | done |
| class files: constant pool, fields, methods, Code, exception tables, BootstrapMethods, all 202 opcodes decoded, modified UTF-8 | `Loader/ClassFile.v` (in Rocq) | done |
| machine: heap objects, arrays (all kinds, store checks), exceptions as objects + handler search across frames, all invoke kinds with resolution, virtual/interface dispatch, default methods, `<clinit>` (JVMS 5.5) incl. `ExceptionInInitializerError` / `NoClassDefFoundError`, checkcast/instanceof incl. arrays, monitors (single thread), String/Class constants (interned), `invokedynamic` for string concatenation and lambdas/method refs, multianewarray | `Core/Machine.v` | done |
| JDK models: String, StringBuilder, Character (Unicode tables are parameters), Integer/Long/Math, boxing with the JLS caches, Objects, System.arraycopy, Arrays.fill/copyOf, array clone, Enum, slf4j loggers, exception constructors | `Jdk/Strings.v`, `Jdk/Jdk.v` | done for what the corpora use; also Math floorDiv/floorMod/*Exact, Integer/Long bit operations, messages of exceptions created by user code (getMessage, Throwable.toString), toString of boxes in string concatenation; String.repeat/isBlank/strip*/replace/split (one-character fast path)/join/compareToIgnoreCase and ASCII toUpperCase/toLowerCase |
| java.util collections (as clean-room Java model classes, loaded by the machine) | `harness/jdkmodel/`, `classes/jdkmodel` | done for Iterator/ListIterator/Collection/List/Set/Map(+Entry) with defaults, AbstractCollection/List/Set/Map, ArrayList, HashMap (tree bins, JDK iteration order), LinkedHashMap (access order, removeEldestEntry), HashSet/LinkedHashSet, Collections empty/singleton/unmodifiable, Arrays.asList; 14 targets x 10,000 inputs, 0 mismatches; 5 canaries detected (`docs/jdk-collections-status.md`) |
| threads in the machine | `Core/Threads.v`, `harness/threads/src` (model classes) | **done (sequentially consistent semantics)**: per-thread frames and monitor counts over the shared heap; blocking monitors (`monitorenter`, ACC_SYNCHRONIZED methods with exit on normal and abrupt return); `wait`/`notify`/`notifyAll` with wait sets and reentrant counts; interrupts (JLS 17.2.3: wait, sleep, join throw InterruptedException, the status is cleared); `Thread.start/join/isAlive/currentThread/sleep/yield/interrupt/interrupted` through a clean-room `java.lang.Thread` model class; class initialisation across threads (JLS 12.4.2: a thread blocks while another initialises the class). `tstep` is the step relation over every schedule, notify choice and spurious wakeup; `trun` an executable run for a scheduler. Clean-room models over it: `AtomicInteger/Long/Boolean/Reference`, `CountDownLatch`, `ReentrantLock` with `Condition`, `ThreadLocal`, `TimeUnit`, `Executors` (fixed / single / cached pools), `ExecutorService`, `FutureTask`/`Future` (incl. ExecutionException, cancellation), `TimeoutException`. Time: `System.nanoTime`/`currentTimeMillis` read a clock that the scheduler advances (`ts_tick`); every timed operation (timed wait, sleep, join(ms), await/tryLock/get with timeouts, awaitTermination) may time out, as in the JDK |
| Java memory model | `Concurrency/Events.v`, `Order.v`, `Executions.v`, `DRF.v`, `Examples.v` | abstract event interface; executions, po/so/sw/hb/rf, well-formedness (JLS 17.4.7), hb-consistency (17.4.5), data races, SC; **DRF lemma proved** (`DRF.drf_execution_sc`), **DRF-SC for hb + acyclic(po∪so∪rf)** (`DRF.drf_sc_no_thin_air`), the JLS 17.4.8 example (`Examples.hb_model_not_drf_sc`). The thread layer is the SC semantics: by DRF-SC it has all the behaviours of race-free programs; the non-SC behaviours of racy programs are not generated (the link of `tstep` to `Executions.v` is not formalised yet) |
| reflection | `Jdk/Jdk.v` (`class_model`, `class_member_model`, `reflect_model`), `Core/Machine.v` (`MFrame`) | `Object.getClass` and `java.lang.Class`: getName, getSimpleName (InnerClasses), getTypeName, isArray, isInterface, isPrimitive, isEnum, getSuperclass, getComponentType, primitive classes (`int.class`), isInstance, isAssignableFrom, cast, desiredAssertionStatus (assertions off), toString, `Class.forName(String)`. **java.lang.reflect**: getMethod / getDeclaredMethod / getConstructor / getDeclaredConstructor / getField / getDeclaredField (NoSuchMethodException / NoSuchFieldException with the JDK's messages); `Method.invoke` (virtual dispatch, unboxing and int→long widening of arguments, boxing of the result, InvocationTargetException around the callee's exception, class initialisation first), `Constructor.newInstance`, `Field.get/set` (instance and static, non-final), getName / getModifiers / getParameterTypes / getParameterCount / getReturnType / getType / getDeclaringClass, setAccessible; access checks (Reflection.verifyMemberAccess: same class, public, nestmates for private, same package) with the JDK's IllegalAccessException message; the argument-count, receiver and type errors with the JDK's messages. The model calls back into bytecode by running a synthetic frame (`MFrame`). Not modelled (STUCK): members of JDK classes, getMethods/getDeclaredMethods (unspecified order), toString of members, annotations, generics, float/double unboxing, protected access across packages, final-field writes |
| class loaders, other natives | | not started (a run that needs them is STUCK) |

Opcodes: **199 of 202** have semantics (`jsr`, `ret`, `jsr_w` are decoded and rejected: class files of version >= 51
cannot contain them). Partial: `ldc` of MethodType/MethodHandle/dynamic constants, `invokedynamic` bootstraps other
than StringConcatFactory, LambdaMetafactory (metafactory/altMetafactory), ObjectMethods and SwitchBootstraps (and
the conversions listed under "Not done yet").
**189** of the 199 occur in the differentially tested bytecode.

Model bounds (a run that hits one is `STUCK`, i.e. no claim): arrays larger than 2^20 elements (OutOfMemoryError
depends on the heap size), JDK methods without a model, callbacks from JDK code into bytecode (e.g. `toString()` of
a user object in string concatenation), identity hash codes.

## Differential testing (extracted model vs HotSpot 21.0.12)

| Corpus | Methods | Inputs per method | Mismatches |
|---|---|---|---|
| `Ops` (all int/long opcodes, switches, loops, wide locals) | 70 | 100,000 | 0 |
| `StackOps` (hand-assembled: every form of pop/pop2/dup*/swap, nop) | 17 | 100,000 (nop: 2,000) | 0 |
| `canUpdate` main + fix | 2 | 100,000 | 0 |
| `Ops2` (plain ldc, local references, goto_w) | 4 | 2,000 | 0 (regression: `big`, a 28,000-instruction method, runs 20 inputs; the extracted loader and the linear fetch make it ~1 min per input) |
| `Heap` (objects, arrays, exceptions, dispatch, clinit, locks) | 35 | 10,000 | 0 (2 methods: inputs with array sizes above the model bound 2^20 are STUCK, i.e. no claim) |
| `Strs` (String/StringBuilder/Character/parse/concat/switch/enum) | 53 | 10,000 | 0 (2 methods: sizes above the bound STUCK) |
| `Flt` (float/double opcodes) | 31 | 10,000 | 0 |
| `Lam` (lambdas, method refs, boxing caches, multianewarray, EIIE/NCDFE, enum switch) | 15 | 10,000 | 0 (1 method: sizes above the bound STUCK) |
| `Fld` (corpus6: inherited/shadowed static and instance fields, interface fields, init order incl. superinterfaces with defaults, circular and erroneous initialisation, inherited static methods, enum with `name`/`ordinal` fields) | 11 | 2,000 | 0 |
| `Sel` (corpus7: private methods incl. nestmates and private interface methods, maximally-specific defaults, package-private overriding across packages incl. JVMS 5.4.5 (b), super calls; classes recompiled separately: ICCE / AME / NoSuchMethodError / NoSuchFieldError, resolution before the null check) | 8 | 2,000 | 0 (172 of 2,000 inputs of `changed`/`changedCaught` are `STUCK` by design: the JVMS/HotSpot divergence below) |
| `Indy` (corpus8, `--release 21`: `Foo::new` incl. initialisation and failing `<clinit>`, altMetafactory serializable/marker lambdas, record toString/equals/hashCode incl. float/double, NaN, -0.0, nulls and boxes, typeSwitch with Class/String/Integer labels and record patterns, sealed switch, enumSwitch) | 14 | 2,000 | 0 |
| `Boxes` (corpus10: instanceof / checkcast / aastore of boxes, String, StringBuilder, enums into Serializable[] / Comparable[] / Constable[] / ConstantDesc[] / CharSequence[] / Number[], mixed varargs) | 4 | 2,000 | 0 |
| `Msg` (corpus9: messages of ArithmeticException, ArrayIndexOutOfBounds, NegativeArraySize incl. multianewarray, ArrayStore, NoClassDefFoundError chains, ExceptionInInitializerError; uncaught and through getMessage()) | 11 | 2,000 | 0 (9,730 messages compared; the no-claims are the 2^20 array bound and Object.notify's message) |
| all machine corpora above + `Heap`, `Strs`, `Lam`, `Flt`, cim hash, jdkmodel rerun with messages | 187 | 300 | 0 (1,345 messages compared) |
| `Threads` (thread layer: synchronized blocks/methods, static synchronized, reentrancy, join visibility, isAlive, producer/consumer and ping-pong with wait/notify, wait restoring reentrant counts, IllegalMonitorState / negative timeout / double start, exceptions leaving synchronized methods and killing threads, names, Thread subclasses, class initialisation from two threads, sleep/yield); each input run under **6 schedulers** (round robin with quanta 1/3/17, three random) which must all agree with HotSpot | 18 | 200 | 0 |
| `Threads2` (interrupts of wait / sleep / join, interrupted() clearing, interrupt before start; AtomicInteger/Long/Boolean/Reference incl. CAS loops and update functions, CountDownLatch, ReentrantLock reentrancy and errors, Condition-based bounded buffer, ThreadLocal with initial values, lockInterruptibly) | 15 | see the regression table | 0 |
| `Refl` (corpus11: Class names, simple names, hierarchy, isInstance/isAssignableFrom, cast, forName, assertions, exception messages and toString) | 9 | 2,000 | 0 |
| `MathOps` (corpus11: Math floor/exact operations, Integer/Long bit operations) | 17 | see the regression table | 0 |
| `ExecTests` (fixed / single-thread / cached executors with futures, ExecutionException causes and messages, awaitTermination, timed CountDownLatch/tryLock/join/Future.get/Condition.await that time out and that succeed, TimeUnit conversions incl. saturation, nanoTime monotonicity) | 6 | see the regression table | 0 |
| `LamConv` (corpus13: method references and lambdas that need LambdaMetafactory's boxing, unboxing, widening incl. Integer → long, receiver casts and dropped results; NPE on unboxing null, CCE on a wrong argument type) | 8 | 300 | 0 |
| `StrMore` (corpus13: String.repeat, isBlank, strip/stripLeading/stripTrailing, ASCII toUpperCase/toLowerCase, replace(CharSequence, CharSequence) incl. empty target, split on one character with limits and trailing empty strings, String.join, compareToIgnoreCase) | 6 | 300 | 0 (cmpIC: 27 inputs reach toUpperCase of a non-ASCII string, STUCK) |
| `ReflTests` (corpus12: Method.invoke static/virtual with boxing and widening, InvocationTargetException, argument count/type/receiver errors, NoSuchMethodException, access checks with IllegalAccessException messages and nestmates, setAccessible, Constructor.newInstance incl. private, Field get/set/modifiers, NoSuchFieldException, class initialisation through reflection) | 7 | 1,000 | 0 |
| `ToStr` (corpus13: toString() called back from String.valueOf, StringBuilder.append(Object) and string concatenation; null results, exceptions, super calls, recursion) | 5 | 300 | 0 |
| `ChmOps` (ConcurrentHashMap model, single thread: random operation sequences on colliding keys incl. tree bins and resizes, compute*/merge, recursive updates, views and iterators, errors, ConcurrentMap interface) | 7 | 300 | 0 (recursive: 25 inputs resize inside a mapping function, STUCK by design) |
| `ChmThreads` (ConcurrentHashMap under the thread layer: merge counts, computeIfAbsent once per key, putIfAbsent winners, concurrent resize, replace CAS loop, iteration during writes, compute on one bin) × 6 schedules | 7 | 50 | 0 |
| `TreeOps` (TreeMap/TreeSet models: natural order and comparators, navigation, poll, compute/merge, iterators with remove, fail-fast, ClassCastException, a TreeSet subclass overriding higher) | 3 | 300 | 0 |
| `SchedTests` (Semaphore fair/non-fair incl. timed tryAcquire, reducePermits, interrupts and handoff; Timer/TimerTask order, cancel, purge, a failing task; ScheduledThreadPoolExecutor order, Callable results, cancel, fixed rate / fixed delay, shutdown policies; DelayQueue) × 6 schedules | 8 | 30 | 0 |
| `PoolTests` (ThreadPoolExecutor with the four rejection policies, hooks incl. a failing task, cached pool over SynchronousQueue with keep-alive, shutdownNow, configuration errors and resizing, ScheduledThreadPoolExecutor as a ThreadPoolExecutor, blocking queues, fair ReentrantLock order, uncaught-exception handlers) × 6 schedules | 9 | 20 | 0 |
| `TimeTests` (the earliest deadline first over sleeps and timed waits, mixed timed tryAcquire/poll/await) × 6 schedules | 3 | 20 | 0 |
| `FmtOps` (String.format / formatted: a fuzzer of valid and invalid specifiers over random arguments, exception classes and messages; common uses) | 2 | 300 | 0 (format: 4 inputs reach floating-point or date conversions, STUCK) |
| `SortOps` (Comparator combinators, stable List/ArrayList/Arrays/Collections sorting, CME and range errors, ClassCastException of mixed natural sorts; identity hash code consistency, radix strings) | 2 | 300 | 0 |
| `DequeTests` (ArrayDeque/Deque/Queue, written by the Camel hunt session) | 2 | 300 | 0 |
| `RegexOps` (java.util.regex: random patterns with groups, named groups, alternation, classes, greedy/lazy/possessive quantifiers, anchors, `\b`, back references, lookahead, inline flags; find/matches/lookingAt, group/start/end, replaceAll/First, split; typical uses) | 2 | 300 | 0 (22 no-claim: captures the JDK may keep from failed attempts) |
| `StrRegex` (`String.matches`, `replaceAll`, `replaceFirst`, `split` with and without a limit over a pool of patterns and replacements with group references; CSV / key=value parsing) | 2 | 300 | 0 |
| `StreamOps` (sequential Stream/IntStream/LongStream pipelines from random operations: lambda call order, laziness, short-circuiting, flags (sized/distinct/sorted), reuse and close errors, onClose; Collectors incl. groupingBy/partitioningBy/toMap merge errors/teeing; Optional*; StringJoiner; java.util.function defaults) | 4 | 300 | 0 |
| `ImmOps` (List.of/copyOf, Set.of/copyOf, Map.of/ofEntries/entry/copyOf: null checks with HotSpot's helpful NPE messages, duplicates, unsupported operations, sub lists, iterators, class names; set/map iteration through the salt parameter, compared sorted) | 4 | 200 | 0 |
| `MiscOps` (System.arraycopy: every check and HotSpot message; java.util.Objects: equals/hashCode/hash/toString callbacks, requireNonNull* messages, checkIndex) | 2 | 300 | 0 |
| `CowOps` (CopyOnWriteArrayList/Set incl. sub lists and snapshot iterators, ConcurrentLinkedQueue/Deque incl. weakly consistent iterators, exceptions) | 4 | 300 | 0 |
| `ListMsgOps` (ArrayList messages, ArrayList.subList nested/co-modification/bulk operations, AbstractList views of Arrays.asList and the Collections lists, clone of ArrayList/HashMap/HashSet) | 3 | 300 | 0 |
| `ExcOps` (Throwable: causes, initCause errors, addSuppressed incl. try-with-resources and disabled suppression, getLocalizedMessage/getMessage overrides, toString of JDK and user exceptions) | 2 | 300 | 0 |
| `CharsetOps` (String.getBytes / new String(byte[], ...) in UTF-8 (malformed input), ISO-8859-1, US-ASCII, UTF-16/BE/LE; Charset lookup, names, errors; String(char[]/StringBuilder/String) constructors; Double/Float boxes: equals/hashCode/compareTo/compare/bit conversions) | 4 | 300 | 0 |
| `CfTests` (CompletableFuture: chains, errors, exact dependent order (nested, combine/either, allOf/anyOf), cancel, timeouts, waiters, rejection; StampedLock stamps, queue, threads) × 6 schedules | 15 | 20 | 0 |
| `CowThreads` (copy-on-write lists/sets and concurrent linked queues/deques under three or four threads) × 6 schedules | 4 | 20 | 0 |
| `CaseInsensitiveMap.caseInsensitiveHash` main + fix | 2 | 20,000 random strings incl. surrogates | 0 |
| java.util model classes (`targets-jdkmodel.txt`: HashMap, LinkedHashMap, tree bins, copies, ctors, sizing, strings, views, sets, ArrayList, AbstractList, AbstractMap, Collections) | 13 (+1 STUCK by design: identity-hash tie-break) | 10,000 | 0 |
| CaseInsensitiveMap whole class (`CimScenario.run`: random put/remove/get/containsKey sequences of 1..200 ops checked against a reference map; result = slot-array lengths of the final map) main + fix | 2 | 2,000 runs each | 0 |
| camel-wal whole class (`WalScenario`: TransactionLog + LayerInfo + EntryContainer + LogEntry + EntryState) main + fix | 2 | 4,516 scenarios | 0 |

Model bugs found by differential testing and fixed: `String.startsWith(null, negative offset)` returns false (no
NPE); `new StringBuilder(huge)` (now a model bound); enum methods inherited from `java.lang.Enum` (model lookup on
the superclass chain). Canaries (`harness/canary.sh`, the float canaries) confirm the comparison detects wrong models.

## Proved about Camel bytecode (real `.class` files, `javac 21.0.12 --release 17 -g`, commits in `classes/*/BUILD-INFO`)

### camel-wal TransactionLog (CAMEL-26088) — main 36bebb520a63, fix e72996b974ad
| Theorem | Statement |
|---|---|
| `WalCanUpdate.main_behaviour` / `fix_behaviour` | exact input/output function of `canUpdate(IIII)Z` for all ints |
| `WalCanUpdate.fix_correct` (+ `_exact`, `_any_fuel`) | for every capacity, number of adds and added entry, the fix's `canUpdate` returns "entry still in the ring" |
| `WalCanUpdate.main_refuted` | main violates that contract (two counterexamples: off-by-one and stale layer) |
| `WalScenario.main_marks_newer_entry` | whole class on main: capacity 3, 10 adds, updating entry 2 marks entry 8 |
| `WalScenario.main_rejects_live_entry` | whole class on main: capacity 4, 9 adds, live entry 5 is not updated |
| `WalScenario.fix_bounded` | whole class on the fix: the contract holds for every capacity 1..4, every n <= 12, every k < n, debug logging off and on (computed in the kernel) |
| `WalScenario.main_bounded_fails` | the same bounded check fails on main |
| `WalUpdate.update_live` / `update_dead` | the bytecode of `update(LayerInfo, EntryState)` and everything it calls (canUpdate, getters, setEntryState, slf4j), on any heap: returns the container and sets exactly that LogEntry's state, or returns null and changes nothing |
| `WalAdd.add_step` | the bytecode of `add(LogEntry)` with the LayerInfo/EntryContainer constructors and `Object.<init>`, on any heap: the roll-over decision, two fresh objects, the array store, `currentIndex++` |
| `WalAdd.tl_init` | the constructor `TransactionLog(int)` (for capacities up to the model's array bound 2^20) |
| `WalRing.add_preserves`, `wal_update` | the ring-buffer representation invariant `wal_inv` (fields = (cur_index, cur_layer), slot `k mod cap` holds the container of every entry still in the ring, each LayerInfo holds (k mod cap, k / cap)) is preserved by `add` and by `update` |
| **`WalRing.session_ok`, `wal_from_constructor`** | **unbounded whole-class theorem on the fix:** after `new TransactionLog(cap)`, for every capacity `1 <= cap <= MAX_ARRAY` (2^20) and *every* sequence of `add` / `update` calls (while the layer counter fits in an int), each `add` returns a new container and each `update(L_k, st)` returns entry k's container iff k is still in the ring (`live cap n k`) and null otherwise. No fixed enumeration bound on sequence length; the layer-counter, heap and environment preconditions remain |

### camel-util CaseInsensitiveMap — fix branch 27aeb4f860d9 (main has the same hash code)
| Theorem | Statement |
|---|---|
| `CimHash.caseInsensitiveHash_correct` | **for every String** (any length up to Integer.MAX_VALUE, any content) and **any Unicode tables**, the real bytecode of `caseInsensitiveHash` returns `cih_spec` (a loop over UTF-16 units folding each with lower(upper(c))) — a universal proof over the heap, the loop and the String/Character models |
| `CimAscii.ascii_equals_iff`, `ascii_eq_refl`, `ascii_eq_sym`, `ascii_eq_trans`, `ascii_eq_hash`, `ascii_key_laws` | **ASCII keys of arbitrary length, for every Unicode environment, with no Unicode-table hypotheses:** equalsIgnoreCase is equality of ASCII-lowercase-normalized lists; it is an equivalence and implies equal hashes. A kernel-computed 128 × 128 character lemma is lifted to arbitrary strings by induction. |
| `CimAscii.ascii_bytecode_hash` | The real fix bytecode returns a common hash for any two equal-ignoring-case ASCII strings in the heap, with JVM string lengths at most INT_MAX. Composes the new key law with `CimHash.caseInsensitiveHash_correct`. |
| `CimAsciiMap.ascii_find_correct` | Instantiates `CimAbs.find_correct` for ASCII keys: lookup correctness under the existing table/key invariants, with no caller-supplied equality or hash laws. This is the abstract chain lookup theorem, not an additional bytecode/session theorem. |
| `CimSpec.cih_consistent_bmp` | for strings without surrogate units: `equalsIgnoreCase(a, b)` implies equal hashes (assumes the three Unicode facts `jdk_facts`, checked against JDK 21 by `harness/check_unicode_facts.py`) |
| `CimSpec.cih_inconsistent_supplementary` | with JDK 21's case pair U+10400/U+10428, `"𐐀".equalsIgnoreCase("𐐨")` is true but the hashes differ — a real defect, `docs/finding-cim-supplementary-case.md` (reproduced on HotSpot with the real classes, main and fix) |
| `CimScenario.main_churn_grows` | real bytecode of main: `put("h"); remove("H")` repeated 12/13/14/20/50 times leaves 13/13/19/28/63 slots — removed keys' slots are never reused (unbounded growth) |
| `CimScenario.fix_churn_bounded` | the fix keeps 13 slots for every n ≤ 64 |
| `CimScenario.main_runs` / `fix_runs` | 40 random runs of 100 operations (4 keys × 2 case variants incl. `x-é`/`X-É`): both versions answer every put/remove/get/containsKey/size exactly like a map; main holds up to 28 slots, the fix 13 (kernel-computed, with Track B's `AbstractMap` model class) |
Unbounded, on the real bytecode of the fix, for **any heap** (no bound on sizes or contents), each a separate theorem:
| Theorem | Statement |
|---|---|
| `CimCalls.call_cih`, `call_fi`, `call_fi1` | calls of caseInsensitiveHash / findIndex(String,int) / findIndex(String) from any frame: push `cih_spec` of the key / the result of walking the bucket's chain (`fi_walk`) |
| `CimPut.put_present` | put of a key that is in the map: replaces the value in its slot, returns the old value |
| `CimPut.put_new_fast`, `CimPut2.put_tail` | put of a new key with a free slot: key/value into slot `usedSlots`, slot pushed on its bucket's chain |
| `CimPut2.put_grow` | no free slot and more than half the slots hold keys: the three arrays grow by half (Arrays.copyOf), then insert |
| `CimCompact.call_compact`, `CimPut3.put_compact` | no free slot and at most half hold keys (**the fix**): compactRemovedSlots — its three loops proved equal to Rocq functions `c1`/`c2`/`c3` — then insert, **without growing the arrays** |
| `CimRemove.remove_spec`, `get_spec`, `containsKey_spec` | remove (unlink from the chain, clear the slot) / get / containsKey |
| `CimAbs.find_correct`, `insert_ok`, `insert_keys_ok`, `remove_ok` | the table invariant (every bucket's chain lists exactly the used slots of that bucket, keys pairwise different ignoring case): findIndex finds the slot of the key or -1; insertion and removal preserve the invariant (for keys on which equalsIgnoreCase is an equivalence consistent with the hash — e.g. strings without surrogates, see `CimSpec`) |
| `CimAbs2.c1_ok`, `c2_ok`, `c3_ok`, **`compact_ok`** | **compaction (the fix) keeps the table invariant, every entry and their order**, renumbers the used slots 0..size-1 and frees the rest; its three loops never fail on a valid table |
| **`CimMap.get_map`, `remove_map`, `put_present_map`** | **the real bytecode of get / remove / put-of-a-present-key, on any heap holding a map in the invariant (`cim_rep`), returns exactly what the abstract insertion-ordered case-insensitive map returns, and leaves a map in the invariant whose entries are the abstract result** |
| `CimMap2.put_new_free_map`, `CimMap3.put_compact_map`, `put_grow_map` | put of a *new* key at map level, on each of its three paths (free slot / compaction / growth): the entry is appended to the abstract map and the invariant is kept; non-array objects and the free heap are untouched (`hframe`) |
| **`CimSession.put_map`, `session_ok`** | **unbounded whole-class theorem on the fix:** from any state where the map represents an abstract entry list `A`, for *every* sequence of `get` / `put` / `remove` calls, each call returns what the insertion-ordered case-insensitive map returns (old value or null), the map then represents the abstract result, and the slot arrays never exceed `B >= max(initial length, 3 * threshold)` |
| **`CimSessionAscii.session_ok_ascii`** | **the session theorem with no hypotheses on the keys:** `session_ok` for ASCII keys of any length, every Unicode environment (the three key laws are `CimAscii.ascii_key_laws`) |

Assumptions of `session_ok`: no `resize()` (fewer than `threshold` entries whenever a new key is put; resize needs
`(int)(n*0.75f)` on the float model); `equalsIgnoreCase` is symmetric, transitive and consistent with `cih_spec` on
the keys used (the `good` hypotheses: true without surrogates by `CimSpec`, false for supplementary letters, see the
finding); `3 * threshold <= 2^20` (the model's array bound). `containsKey` is proved at bytecode level
(`containsKey_spec`) but not part of the session. Next: discharge the `good` hypotheses for ASCII keys, then `resize`.

### Local verification follow-up, 2026-10-24

The ASCII files above compile with Rocq 9.3.0 / stdlib 9.2.0 and their `Print Assumptions` output is closed under the global context.

All 40 baseline generated class dumps match their recorded bytecode and hashes. On local HotSpot 21.0.11,
`harness/camel/cim/probe/AsciiAudit.java` checks all 16,384 ASCII character pairs, with 180 equivalent
pairs exercising equal hashes, cross-case lookup and removal, on both recorded main and fix classes:
zero failures. Churn at 50/1000 rounds yields 63/1066 slots on main and 13/13 on the fix.
The existing Deseret counterexample reproduces on both: equalsIgnoreCase is true, hashes are
1770500 and 1770588, alternate-case lookup is null, and inserting both keys gives size 2.
These runtime checks support the model; they are not proofs. All five existing Unicode-fact
checks also pass against locally dumped JDK tables.

A fresh extracted-model/HotSpot comparison of `caseInsensitiveHash` passes for 1,000 inputs
per version (seed 20261024): 1,000 agreements each, zero mismatches, zero model STUCK/FUEL
results, and 55 matching HotSpot exceptions each. Counts: `harness/results/2026-10-24.tsv`.
Independent `rocqchk` checking of `CimAsciiMap` and all its dependencies reports no axioms,
type-in-type, unsafe recursion, or assumed positivity.

Scope clarification for WAL: `wal_from_constructor` requires `1 <= cap <= MAX_ARRAY` (2^20),
and `session_ok` starts from an invariant with `cap <= INT_MAX`. Sequence length has no fixed
enumeration bound, but the stated layer-counter bound and heap/environment preconditions remain.
These theorems do not claim that arbitrary JVM allocations are supported.

## Field and method resolution, selection, class initialisation (JVMS 5.4.3, 5.4.5, 5.4.6, 5.5)
- **Fields** (`Machine.resolve_field`, 5.4.3.2): the referenced class, its superinterfaces, then its superclass, over
  loaded classes and the generated JDK table `Core/JdkTables.v` (declared members of Object, Enum, Record, Throwable
  and the exception classes, Number, the java.lang marker/functional interfaces, java.util.function; regenerate with
  `tools/gen_jdk_tables.sh`). getstatic/putstatic initialise the class that *declares* the field (an inherited static
  field no longer initialises the referenced class, an erroneous subclass does not hide its superclass's fields).
  NoSuchFieldError / IncompatibleClassChangeError (static vs instance) are thrown, also before the null check of getfield/putfield.
- **Shadowed instance fields**: an object stores its fields most-derived first; a field shadowed by a subclass field of
  the same name is keyed `"<DeclaringClass>.<name>"`, every other field keeps its plain name (`instance_fields`).
  getfield/putfield resolve the field only when the object holds a shadowed field of that name (`field_slot`), so the
  keys and lookups of all existing proofs are unchanged. The Enum model reads `java/lang/Enum.name`/`ordinal` the same way
  (an enum may declare its own `name`/`ordinal` fields).
- **Methods**: `resolve_method` (5.4.3.3 / 5.4.3.4, incl. ICCE for class/interface mismatch, NoSuchMethodError,
  maximally-specific superinterface methods), `select_virtual` (5.4.6: a private resolved method is selected as is,
  overriding per 5.4.5 incl. package-private methods across packages and the transitive case, maximally-specific
  defaults, AbstractMethodError / ICCE / IllegalAccessError), `select_special` (invokespecial: super calls start at the
  direct superclass of the current class; `I.super.m()`). invokestatic initialises the declaring class.
  `resolve_full p c n d` is the fast path the step lemmas use: the method an object of class `c` runs when that does
  not depend on the resolved method (no private declaration of `n d` in the hierarchy other than the only one, no
  package-private overriding question, not abstract, unique non-abstract maximally-specific default); otherwise the
  machine asks the JDK model and then performs full resolution and selection.
- **Initialisation order** (5.5 steps 6, 7): all not-yet-started classes of the superclass chain are marked and their
  ConstantValue fields set before any `<clinit>` runs (circular initialisation sees the subclass "in progress"), then
  `<clinit>`s run outermost first; before a class's `<clinit>` its superinterfaces that declare a non-abstract,
  non-static method are initialised in JVMS order (a pending `<clinit>` frame at pc -1); an exception through a pending
  frame marks that class erroneous.

## invokedynamic (JDK 21 bootstrap methods)
- `LambdaMetafactory.metafactory` and `altMetafactory` (flags serializable / markers / bridges: the lambda object also
  implements the marker interfaces and java.io.Serializable; bridges are further descriptors of the same name),
  implementation kinds static / virtual / interface / special and **REF_newInvokeSpecial** (`Foo::new`: initialises
  Foo when the handle is invoked, allocates, runs the constructor, returns the object); arguments are unboxed to the
  implementation's primitive parameters (null: NullPointerException).
- `ObjectMethods.bootstrap` (records): `toString` = `getSimpleName()` (InnerClasses inner name, else the name after the
  last '/') + `[a=..., b=...]` with String.valueOf of each component (primitives, null, Strings, boxes), `hashCode` =
  fold `31 * h + hash(c)` (Integer/Long/.../Float/Double/Boolean.hashCode, Objects.hashCode), `equals` = same object,
  else `isInstance` and the components compared last to first (Float/Double.compare == 0, Objects.equals) — the
  structure of JDK 21's `ObjectMethods`.
- `SwitchBootstraps.typeSwitch` / `enumSwitch` as implemented in JDK 21.0.12 (`createMethodHandleSwitch`):
  `Objects.checkIndex(restart, n + 1)`, null -> -1, then the first label from `restart` that matches: Class
  (`isInstance`), Integer (Number/Character value), String (`Objects.equals`), enum constant name (same declaring
  enum class and the constant itself); none -> n.
- The JDK classes not loaded by the machine now know their JDK 21 superinterfaces (boxes, Number, String,
  StringBuilder, Class, Enum, the JdkTables.v classes): e.g. an Integer is Serializable / Comparable / Constable /
  ConstantDesc, so `Serializable[]` from mixed varargs accepts it (was a wrong ArrayStoreException).

## Exception messages (HotSpot 21 texts)
The machine's own exceptions carry `detailMessage` (read by the Throwable.getMessage model, printed by the harness):
`/ by zero` (idiv/irem/ldiv/lrem), `Index i out of bounds for length n` (all xaload/xastore),
the negative count for NegativeArraySizeException (multianewarray: the first negative count met by HotSpot's
depth-first allocation), `Class.getName()` of the stored value for ArrayStoreException, `current thread is not
owner` (monitorexit), `Could not initialize class X` for NoClassDefFoundError (X = the first erroneous class of
the superclass chain; the classes below it become erroneous, JVMS 5.5 step 7), null for ExceptionInInitializerError.
`DiffRunner` prints `E <class> m:<hex units>|m:null`; `compare.py` compares the message when the model prints one
and counts it (`messages_compared`).

## Proof infrastructure

### New bug witnesses (2026-10-24)

`Camel/NewBugs.v` executes unchanged production classes from Camel `bd4d2ba20d6a`:

| Theorem | New finding |
|---|---|
| `filter_remove_wrong_element`, `filter_remove_before_next` | `FilterIterator` lookahead advances the backing iterator, so delegated remove deletes the prefetched element or accepts remove before the wrapper's next. One defect, two manifestations. |
| `negative_nanosecond_is_reported_positive`, `duration_controls` | `TimeUtils.isPositive(Duration.ofNanos(-1))` returns true. Real JDK Duration getter bytecode is run from a valid normalized object; its construction and class initialization are not part of this witness. |

All four are kernel-checked concrete counterexamples/controls with closed `Print Assumptions`;
independent `rocqchk` of NewBugs and its dependencies reports no axioms or unsafe definitions.
HotSpot 21.0.11 agrees. The FilterIterator production class is tested with an ordinary finite
Iterator input in the model and independently with JDK ArrayList on HotSpot. No production method
is stubbed. Both faulty methods remain in the upstream default branch as inspected on this date.
No internal production callers were found in the local core/components search; no route-level
impact is claimed. Details: `docs/finding-filter-iterator-remove.md` and
`docs/finding-time-utils-negative-duration.md`. All 45 class dumps, including the five new ones,
match their class files. The full available project, including the registered new modules, builds successfully.

### Infrastructure
- `Core/Tactics.v`: symbolic execution of the frame interpreter (`symex`), used for int-only methods.
- `Core/Logic.v` (statement change, 2026-10-24): `mstep_getfield` / `mstep_putfield` now take `obj_get p fr fs = Some v` /
  `obj_set p fr v fs = Some fs'` instead of `assoc (fr_name fr) fs` / `set_assoc (fr_name fr) v fs` (with shadowed fields
  the plain-name lookup is wrong for a field of the superclass; for an object without shadowed fields both reduce to the
  old lookup by computation, so every call site `... | reflexivity | ...` is unchanged).
- `Core/Logic.v`: run segments (`leads`, `returns`, `returns_weaken`), fuel composition, and step lemmas
  (`mstep_local`, `mstep_local_return`, `mstep_invoke`, `do_invoke_static_model`, `do_invoke_string_model`,
  getfield/putfield/getstatic/aaload/aastore/new/anewarray/ldc-String, invokespecial/virtual/static entry,
  model calls on unloaded classes and JDK constructors, return to caller)
  that make symbolic execution of the full machine cheap (a naive `cbn` of a machine step on a symbolic state
  exhausts memory). `CimHash.v` shows the pattern: precomputed facts about the loaded program by `vm_compute`,
  model calls as lemmas proved with `cbv`, one tactic per instruction kind, loop proofs by induction.

## Model bugs found on 2026-10-23/24 (fixed in the `model-gaps` work, merged 2026-10-25)
- Instance fields are keyed by name only: a subclass field shadowing a superclass field of the same name collides
  (CaseInsensitiveMap.values vs AbstractMap.values). Not reached by any proof or test so far.
- invokevirtual of a private method selects from the receiver's runtime class (JVMS 5.4.6: the resolved private method
  is selected); package-private overriding across packages (5.4.5) not checked.
- Interfaces of the unloaded boxed types / String are incomplete (Comparable, Serializable, Constable...): an Integer
  stored into a Serializable[] throws ArrayStoreException in the machine.
The camel-wal and CaseInsensitiveMap proofs do not depend on these cases (no shadowed field is accessed, the private
calls are on receivers of the declaring class, no boxed values are stored into typed arrays).

## Not done yet / known limitations
- `jsr`/`ret` (not needed), dynamic constants (condy; e.g. `EnumDesc` labels of a pattern switch over a sealed type
  with qualified enum constants are `STUCK`).
- invokedynamic: the conversions LambdaMetafactory adds (boxing, unboxing, widening, casts, dropped results) run
  as an adapter frame; constructor references (`Foo::new`) that need conversions are `STUCK`; record `toString` of
  float/double components (Float/Double.toString) and of components that need `toString()`/`hashCode()`/`equals()`
  of another object (a call back into bytecode) are `STUCK`; so are pattern-switch label tests that would call `equals()`.
- invokeinterface where several maximally-specific default methods match: JVMS 6.5 says
  IncompatibleClassChangeError, HotSpot 21 throws AbstractMethodError (corpus7 `changed`, case 1): `STUCK` (no claim).
- Access control (IllegalAccessError for private/protected/package access, putstatic to a final field outside
  `<clinit>`) and loader constraints are not checked: javac never emits such accesses in a jointly compiled program.
- Fast paths assume a link-consistent class set (see "Field and method resolution" below and TRUST.md).
- Exception messages: the exceptions the machine creates, the reflection exceptions, and exceptions created by user
  code with the java.lang constructors carry their message; exceptions made by other JDK models (`MThrow`, e.g.
  NumberFormatException) have none (the harness compares only their class). Helpful NullPointerException messages,
  ClassCastException messages and the linkage errors' messages are not modelled. Causes (other than
  InvocationTargetException's target) and stack traces are not modelled.
- Threads: the semantics is sequentially consistent (see TRUST.md 5b): the extra behaviours the JMM allows for racy
  programs are not generated; the formal link of `Threads.tstep` to `Concurrency/Executions.v` is not written.
  Daemon threads and priorities' effect: not observable (uncaught-exception handlers are modelled).
- Class loaders (ClassLoader objects, defineClass, loading constraints) are not modelled: one program, loaded by
  one (bootstrap-like) loader. The bytecode verifier (JVMS 4.10) is not modelled: the class files are javac's.
- The JDK library beyond the models listed above (I/O beyond the exception classes, java.time construction,
  parallel streams and DoubleStream, decimal conversion of floating-point numbers (`Double.toString`,
  `parseDouble`, `%f`, `%e`), charsets other than the six standard ones, regex lookbehind, PatternSyntaxException
  messages, captures the JDK may leak between attempts, locale-sensitive case mapping of non-ASCII strings, ...)
  is `STUCK`.
- HotSpot's helpful NullPointerException messages (JEP 358) of null checks in user bytecode are not computed:
  `getMessage()` of such an exception is STUCK (the model classes throw the JDK's exact messages themselves).
- A thread does not inherit its creator's daemon status and priority in the Thread model (JDK: it does);
  thread pools normalise both, so only directly created threads in daemon threads differ.
- VirtualMachineErrors are never thrown (TRUST.md 5a).

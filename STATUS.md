# rocq-jvm status

Rocq 9.3.0 + rocq-stdlib 9.2.0. Build: `make` (uses `rocq makefile`, `-j1`; about 16 minutes, most of it the
kernel-computed whole-class checks in `WalScenario.v` and `CimScenario.v`). Trust base: `TRUST.md`. Opcode table: `docs/opcode-coverage.md`.
Differential-test logs: `harness/results/*.tsv`, `harness/work/*.log` (not committed). Updated 2026-10-24, 08:00 IST.

Every theorem listed below: `Print Assumptions` = "Closed under the global context" (no axioms, nothing admitted).

## What the model covers (tracks A + B)

| Layer | Files | State |
|---|---|---|
| int/long arithmetic (JVMS 2.3, 6.5) | `Core/Int.v` | done; corner cases as `Example`s |
| float/double, IEEE 754 binary32/64, round-to-nearest-even, subnormals, JVMS NaN/conversion rules | `Core/Float.v` | done (written by the float agent); 0 mismatches on 250,000 inputs per op, JIT and `-Xint`; `docs/float-status.md` |
| frame: operand stack (all dup/pop/swap forms), locals (two-slot long/double), branches, switches, returns with `ireturn` narrowing | `Core/Semantics.v` | done |
| class files: constant pool, fields, methods, Code, exception tables, BootstrapMethods, all 202 opcodes decoded, modified UTF-8 | `Loader/ClassFile.v` (in Rocq) | done |
| machine: heap objects, arrays (all kinds, store checks), exceptions as objects + handler search across frames, all invoke kinds with resolution, virtual/interface dispatch, default methods, `<clinit>` (JVMS 5.5) incl. `ExceptionInInitializerError` / `NoClassDefFoundError`, checkcast/instanceof incl. arrays, monitors (single thread), String/Class constants (interned), `invokedynamic` for string concatenation and lambdas/method refs, multianewarray | `Core/Machine.v` | done |
| JDK models: String, StringBuilder, Character (Unicode tables are parameters), Integer/Long/Math, boxing with the JLS caches, Objects, System.arraycopy, Arrays.fill/copyOf, array clone, Enum, slf4j loggers, exception constructors | `Jdk/Strings.v`, `Jdk/Jdk.v` | done for what the corpora use |
| java.util collections (as clean-room Java model classes, loaded by the machine) | `harness/jdkmodel/`, `classes/jdkmodel` | done for Iterator/ListIterator/Collection/List/Set/Map(+Entry) with defaults, AbstractCollection/List/Set/Map, ArrayList, HashMap (tree bins, JDK iteration order), LinkedHashMap (access order, removeEldestEntry), HashSet/LinkedHashSet, Collections empty/singleton/unmodifiable, Arrays.asList; 14 targets x 10,000 inputs, 0 mismatches; 5 canaries detected (`docs/jdk-collections-status.md`) |
| threads / JMM | `Concurrency/Events.v`, `Order.v`, `Executions.v`, `DRF.v`, `Examples.v` | abstract event interface; executions, po/so/sw/hb/rf, well-formedness (JLS 17.4.7), hb-consistency (17.4.5), data races, SC; **DRF lemma proved** (a well-formed hb-consistent race-free execution is SC, `DRF.drf_execution_sc`), **DRF-SC for hb + acyclic(po∪so∪rf)** (`DRF.drf_sc_no_thin_air`), and the JLS 17.4.8 example proving the hb model alone is *not* DRF-SC (`Examples.hb_model_not_drf_sc`). Not yet connected to `Machine.v` (design in `docs/track-c-status.md`); the 17.4.8 commit model is next |
| reflection, class loaders, natives beyond the list above | | not started |

Opcodes: **199 of 202** have semantics (`jsr`, `ret`, `jsr_w` are decoded and rejected: class files of version >= 51
cannot contain them). Partial: `ldc` of MethodType/MethodHandle/dynamic constants, `invokedynamic` other than
string concatenation and `LambdaMetafactory.metafactory` (no `Foo::new`, records' `ObjectMethods`, switch patterns).
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
| `Ops2` (plain ldc, local references, goto_w) | 4 | 2,000 | 0 |
| `Heap` (objects, arrays, exceptions, dispatch, clinit, locks) | 35 | 10,000 | 0 (2 methods: inputs with array sizes above the model bound 2^20 are STUCK, i.e. no claim) |
| `Strs` (String/StringBuilder/Character/parse/concat/switch/enum) | 53 | 10,000 | 0 (2 methods: sizes above the bound STUCK) |
| `Flt` (float/double opcodes) | 31 | 10,000 | 0 |
| `Lam` (lambdas, method refs, boxing caches, multianewarray, EIIE/NCDFE, enum switch) | 15 | 10,000 | 0 (1 method: sizes above the bound STUCK) |
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
- `Core/Logic.v`: run segments (`leads`, `returns`, `returns_weaken`), fuel composition, and step lemmas
  (`mstep_local`, `mstep_local_return`, `mstep_invoke`, `do_invoke_static_model`, `do_invoke_string_model`,
  getfield/putfield/getstatic/aaload/aastore/new/anewarray/ldc-String, invokespecial/virtual/static entry,
  model calls on unloaded classes and JDK constructors, return to caller)
  that make symbolic execution of the full machine cheap (a naive `cbn` of a machine step on a symbolic state
  exhausts memory). `CimHash.v` shows the pattern: precomputed facts about the loaded program by `vm_compute`,
  model calls as lemmas proved with `cbv`, one tactic per instruction kind, loop proofs by induction.

## Model bugs found tonight (fixed on branch `model-gaps` in /home/claude/rocq-jvm-gaps, commit b6f22ca, not merged yet)
- Instance fields are keyed by name only: a subclass field shadowing a superclass field of the same name collides
  (CaseInsensitiveMap.values vs AbstractMap.values). Not reached by any proof or test so far.
- invokevirtual of a private method selects from the receiver's runtime class (JVMS 5.4.6: the resolved private method
  is selected); package-private overriding across packages (5.4.5) not checked.
- Interfaces of the unloaded boxed types / String are incomplete (Comparable, Serializable, Constable...): an Integer
  stored into a Serializable[] throws ArrayStoreException in the machine.
The camel-wal and CaseInsensitiveMap proofs do not depend on these cases (no shadowed field is accessed, the private
calls are on receivers of the declaring class, no boxed values are stored into typed arrays).

## Not done yet / known limitations
- `jsr`/`ret` (not needed), dynamic constants, `Foo::new`, `altMetafactory`, switch-pattern and record bootstraps.
- Interface default-method selection takes the first default found (JVMS "maximally specific" not checked).
- Static fields inherited from a superclass (getstatic resolution through superclasses) are `STUCK`.
- Exception objects carry no message/cause/stack trace (only the class is observable in the model).
- Threads: Track C. Reflection, class loaders: later phases.

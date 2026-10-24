# rocq-jvm status

Rocq 9.3.0 + rocq-stdlib 9.2.0. Build: `make` (uses `rocq makefile`, `-j1`; about 16 minutes, most of it the
kernel-computed whole-class checks in `WalScenario.v` and `CimScenario.v`). Trust base: `TRUST.md`. Opcode table: `docs/opcode-coverage.md`.
Differential-test logs: `harness/results/*.tsv`, `harness/work/*.log` (not committed). Updated 2026-10-24 (night 1, second half; model gaps: field/method resolution, initialisation order, invokedynamic bootstraps, exception messages — branch model-gaps).

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
| java.util collections (as Java model classes) | `harness/jdkmodel/` | in progress (Track B agent) |
| threads / JMM | `Concurrency/Events.v`, `Order.v`, `Executions.v`, `DRF.v`, `Examples.v` | abstract event interface; executions, po/so/sw/hb/rf, well-formedness (JLS 17.4.7), hb-consistency (17.4.5), data races, SC; **DRF lemma proved** (a well-formed hb-consistent race-free execution is SC, `DRF.drf_execution_sc`), **DRF-SC for hb + acyclic(po∪so∪rf)** (`DRF.drf_sc_no_thin_air`), and the JLS 17.4.8 example proving the hb model alone is *not* DRF-SC (`Examples.hb_model_not_drf_sc`). Not yet connected to `Machine.v` (design in `docs/track-c-status.md`); the 17.4.8 commit model is next |
| reflection, class loaders, natives beyond the list above | | not started |

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
| `Ops2` (plain ldc, local references, goto_w) | 4 | 2,000 | 0 |
| `Heap` (objects, arrays, exceptions, dispatch, clinit, locks) | 35 | 10,000 (run in progress at time of writing; 300 earlier: 0) | 0 |
| `Strs` (String/StringBuilder/Character/parse/concat/switch/enum) | 53 | 10,000 (in progress; 200 earlier: 0 after 2 model fixes) | 0 |
| `Flt` (float/double opcodes) | 31 | 10,000 (in progress; 2,000 earlier: 0) | 0 |
| `Lam` (lambdas, method refs, boxing caches, multianewarray, EIIE/NCDFE, enum switch) | 15 | 10,000 (in progress; 300 earlier: 0) | 0 |
| `Fld` (corpus6: inherited/shadowed static and instance fields, interface fields, init order incl. superinterfaces with defaults, circular and erroneous initialisation, inherited static methods, enum with `name`/`ordinal` fields) | 11 | 2,000 | 0 |
| `Sel` (corpus7: private methods incl. nestmates and private interface methods, maximally-specific defaults, package-private overriding across packages incl. JVMS 5.4.5 (b), super calls; classes recompiled separately: ICCE / AME / NoSuchMethodError / NoSuchFieldError, resolution before the null check) | 8 | 2,000 | 0 (172 of 2,000 inputs of `changed`/`changedCaught` are `STUCK` by design: the JVMS/HotSpot divergence below) |
| `Indy` (corpus8, `--release 21`: `Foo::new` incl. initialisation and failing `<clinit>`, altMetafactory serializable/marker lambdas, record toString/equals/hashCode incl. float/double, NaN, -0.0, nulls and boxes, typeSwitch with Class/String/Integer labels and record patterns, sealed switch, enumSwitch) | 14 | 2,000 | 0 |
| `Boxes` (corpus10: instanceof / checkcast / aastore of boxes, String, StringBuilder, enums into Serializable[] / Comparable[] / Constable[] / ConstantDesc[] / CharSequence[] / Number[], mixed varargs) | 4 | 2,000 | 0 |
| `Msg` (corpus9: messages of ArithmeticException, ArrayIndexOutOfBounds, NegativeArraySize incl. multianewarray, ArrayStore, NoClassDefFoundError chains, ExceptionInInitializerError; uncaught and through getMessage()) | 11 | 2,000 | 0 (9,730 messages compared; the no-claims are the 2^20 array bound and Object.notify's message) |
| all machine corpora above + `Heap`, `Strs`, `Lam`, `Flt`, cim hash, jdkmodel rerun with messages | 187 | 300 | 0 (1,345 messages compared) |
| `CaseInsensitiveMap.caseInsensitiveHash` main + fix | 2 | 20,000 random strings incl. surrogates | 0 |
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
| **`WalRing.session_ok`, `wal_from_constructor`** | **unbounded whole-class theorem on the fix:** after `new TransactionLog(cap)`, for *every* capacity and *every* sequence of `add` / `update` calls (while the layer counter fits in an int), each `add` returns a new container and each `update(L_k, st)` returns entry k's container iff k is still in the ring (`live cap n k`) and null otherwise. No bound on capacity, sequence length or values |

### camel-util CaseInsensitiveMap — fix branch 27aeb4f860d9 (main has the same hash code)
| Theorem | Statement |
|---|---|
| `CimHash.caseInsensitiveHash_correct` | **for every String** (any length up to Integer.MAX_VALUE, any content) and **any Unicode tables**, the real bytecode of `caseInsensitiveHash` returns `cih_spec` (a loop over UTF-16 units folding each with lower(upper(c))) — a universal proof over the heap, the loop and the String/Character models |
| `CimSpec.cih_consistent_bmp` | for strings without surrogate units: `equalsIgnoreCase(a, b)` implies equal hashes (assumes the three Unicode facts `jdk_facts`, checked against JDK 21 by `harness/check_unicode_facts.py`) |
| `CimSpec.cih_inconsistent_supplementary` | with JDK 21's case pair U+10400/U+10428, `"𐐀".equalsIgnoreCase("𐐨")` is true but the hashes differ — a real defect, `docs/finding-cim-supplementary-case.md` (reproduced on HotSpot with the real classes, main and fix) |
| `CimScenario.main_churn_grows` | real bytecode of main: `put("h"); remove("H")` repeated 12/13/14/20/50 times leaves 13/13/19/28/63 slots — removed keys' slots are never reused (unbounded growth) |
| `CimScenario.fix_churn_bounded` | the fix keeps 13 slots for every n ≤ 64 |
| `CimScenario.main_runs` / `fix_runs` | 40 random runs of 100 operations (4 keys × 2 case variants incl. `x-é`/`X-É`): both versions answer every put/remove/get/containsKey/size exactly like a map; main holds up to 28 slots, the fix 13 (kernel-computed, with Track B's `AbstractMap` model class) |
Next: the unbounded proof (put/remove/compact refine an insertion-ordered case-insensitive map, slot count ≤ max(13, 2·size + c)) by the symbolic method used for camel-wal.

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

## Not done yet / known limitations
- `jsr`/`ret` (not needed), dynamic constants (condy; e.g. `EnumDesc` labels of a pattern switch over a sealed type
  with qualified enum constants are `STUCK`).
- invokedynamic: lambdas whose implementation needs boxing, widening or a return-value conversion/drop (e.g.
  `Supplier<Integer> s = this::intMethod`) are `STUCK` (unboxing of arguments is modelled); record `toString` of
  float/double components (Float/Double.toString) and of components that need `toString()`/`hashCode()`/`equals()`
  of another object (a call back into bytecode) are `STUCK`; so are pattern-switch label tests that would call `equals()`.
- invokeinterface where several maximally-specific default methods match: JVMS 6.5 says
  IncompatibleClassChangeError, HotSpot 21 throws AbstractMethodError (corpus7 `changed`, case 1): `STUCK` (no claim).
- Access control (IllegalAccessError for private/protected/package access, putstatic to a final field outside
  `<clinit>`) and loader constraints are not checked: javac never emits such accesses in a jointly compiled program.
- Fast paths assume a link-consistent class set (see "Field and method resolution" below and TRUST.md).
- Exception messages: only the exceptions the machine itself creates carry one (below); exceptions made by JDK models
  (`MThrow`, e.g. NumberFormatException, Object.notify's IllegalMonitorStateException) and by user code
  (`new RuntimeException("x")`) have no modelled message (getMessage() on them is `STUCK`, the harness compares
  only their class). Helpful NullPointerException messages, ClassCastException messages (they name class loaders,
  with identity hash codes under the harness's URLClassLoader) and the linkage errors' messages are not modelled.
  No causes or stack traces.
- Threads: Track C. Reflection, class loaders: later phases.

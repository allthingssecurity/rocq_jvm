# java.util collections as Java model classes (Track B)

The Rocq machine (`theories/Core/Machine.v`) runs `.class` files; JDK classes that are not loaded go to
the Rocq models of `theories/Jdk/Jdk.v` or are STUCK. For `java.util` collections we use the JBMC "core
models" approach instead: **clean-room Java implementations of the JDK collection classes, compiled into
package `java.util`**, which the machine loads in front of the code under test. HotSpot never loads
them: the differential tests run the same test methods on HotSpot against the real JDK 21 and in the
machine against the model classes, and compare every observable result.

## Licence / provenance

The model sources (`harness/jdkmodel/src/java/util/*.java`) are an **independent clean-room
implementation**, written from the Java SE 21 Javadoc (the specification of each method,
including its "implementation requirements" paragraphs) and from publicly documented algorithm
facts about the JDK `HashMap` (hash spreading, power-of-two tables, resize split, tree bins).
**No OpenJDK source code was consulted or copied.** Behaviour details beyond the Javadoc were
established by black-box differential testing against JDK 21.0.12. The files are therefore free of
the OpenJDK GPLv2+CE licence and may be distributed under the project's Apache-2.0 licence.

## Build and run

```
harness/jdkmodel/build.sh            # model -> classes/jdkmodel/java/util/*.class (javac --release 17 -g
                                     #   --patch-module java.base=harness/jdkmodel/src), BUILD-INFO with sha256;
                                     # tests -> classes/jdkmodel-tests (javac --release 17 -g, against the real JDK)
MODE=machine FUEL=2000000 harness/difftest.sh harness/targets-jdkmodel.txt 10000 1
                                     # all targets, 10,000 inputs each (~4 h machine time on one core);
                                     # each line of the targets file can also be run alone
harness/jdkmodel/build.sh canary <name>   # build a deliberately WRONG model into classes/jdkmodel-canary
                                     # and compare it with HotSpot on every target (CANARY_N inputs, default
                                     # 200; CANARY_TARGETS=<regex> selects targets); does not write
                                     # harness/results; exit 0 iff the canary is detected
```

`javac --release 17 --patch-module java.base=<src>` works with JDK 21 javac (no bootclasspath tricks
needed). The `.class` files are only meant for the Rocq machine.

## What is modelled

Interfaces (with the default methods that have an "implementation requirements" in the Javadoc):

| class | methods |
|---|---|
| `Iterator` | `hasNext`, `next`, default `remove` (UnsupportedOperationException), default `forEachRemaining` |
| `ListIterator`, `RandomAccess` | (interfaces) |
| `Collection` | all abstract methods; defaults `removeIf`, and `forEach` (re-declared here because `java.lang.Iterable` is a built-in, not loaded, interface in the machine) |
| `List` | all abstract methods; default `replaceAll` |
| `Set` | all abstract methods |
| `Map`, `Map.Entry` | all abstract methods; defaults `getOrDefault`, `forEach`, `replaceAll`, `putIfAbsent`, `remove(k,v)`, `replace(k,o,n)`, `replace(k,v)`, `computeIfAbsent`, `computeIfPresent`, `compute`, `merge` |

Classes:

| class | modelled |
|---|---|
| `AbstractCollection` | `isEmpty`, `contains`, `toArray()`, `toArray(T[])`, `add` (UOE), `remove`, `containsAll`, `addAll`, `removeAll`, `retainAll`, `clear`, `toString` |
| `AbstractList` | `modCount`; `add`, `get/set/add/remove(int)` (UOE defaults), `indexOf`, `lastIndexOf`, `clear`, `addAll(int,..)`, `iterator`, `listIterator(..)` (fail-fast `Itr`/`ListItr` over `get`), `equals`, `hashCode`, `removeRange` |
| `AbstractSet` | `equals`, `hashCode`, `removeAll` (size-dependent strategy) |
| `AbstractMap` | everything in terms of `entrySet()`: `size`, `isEmpty`, `containsKey/Value`, `get`, `put` (UOE), `remove`, `putAll`, `clear`, cached `keySet`/`values` views, `equals`, `hashCode`, `toString`; `SimpleEntry`, `SimpleImmutableEntry` |
| `ArrayList` | all constructors, `trimToSize`, `ensureCapacity` (modCount only when it grows: growth policy modelled exactly), `size`, `isEmpty`, `contains`, `indexOf`, `lastIndexOf`, `toArray()`, `toArray(T[])`, `get`, `set`, `add`, `add(int,..)`, `remove(int)`, `remove(Object)`, `equals`, `hashCode`, `clear`, `addAll`, `addAll(int,..)`, `removeRange`, `removeAll`, `retainAll`, `removeIf`, `forEach`, `replaceAll`, `iterator`, `listIterator(..)` with `forEachRemaining`, fail-fast exactly as the JDK (including which operations bump `modCount`) |
| `HashMap` | all constructors (argument checks, pre-sizing), `size`, `isEmpty`, `get`, `containsKey`, `put`, `putAll`, `remove`, `clear`, `containsValue`, `keySet`/`values`/`entrySet` views (cached; `contains`, `remove`, `clear`, `forEach`, iterators with `remove`), `getOrDefault`, `putIfAbsent`, `remove(k,v)`, `replace` x2, `computeIfAbsent`, `computeIfPresent`, `compute`, `merge`, `forEach`, `replaceAll`; **tree bins** (treeify, insertion, removal, split on resize, untreeify) so that iteration order equals the JDK's |
| `LinkedHashMap` | all constructors incl. access order, `removeEldestEntry` hook (LRU caches), `get`, `getOrDefault`, `containsValue`, `clear`, linked views and iterators, `forEach`, `replaceAll` |
| `HashSet`, `LinkedHashSet` | all constructors (incl. the JDK 19+ sizing of `HashSet(Collection)`), `iterator`, `size`, `isEmpty`, `contains`, `add`, `remove`, `clear`, `toArray` |
| `Collections` | `emptyIterator`, `emptyList`, `emptySet`, `emptyMap`, `EMPTY_LIST/SET/MAP`, `singletonList`, `singleton`, `unmodifiableCollection`, `unmodifiableList` (RandomAccess variant, no double wrapping), `unmodifiableSet`, `unmodifiableMap` (with unmodifiable entry set / entries) |
| `Arrays` | **`asList` only** (`Arrays$ArrayList`: write-through `set`, `ArrayIndexOutOfBoundsException` from `get/set`, `toArray` returns `Object[]`, iterator without `remove`) |

Exceptions are thrown with the JDK's exact classes (e.g. `IndexOutOfBoundsException` from
`ArrayList.get(-1)`, `ArrayIndexOutOfBoundsException` from `Arrays.asList(..).get(-1)`,
`IllegalArgumentException` from `new ArrayList(-1)` / `new HashMap(-1)` / a load factor <= 0 or NaN,
`NoSuchElementException`, `IllegalStateException`, `ConcurrentModificationException`,
`UnsupportedOperationException`, `NullPointerException`). Messages are not modelled (the machine does
not model exception messages).

### Arrays.asList and the Rocq models of Arrays

`java/util/Arrays` is now a **loaded** class that declares only `asList` (and its nested classes) and
has no static initialiser. For `invokestatic java/util/Arrays.fill/copyOf/...` the machine first
resolves in the loaded class, finds no such method, and falls back to the Rocq model of
`java/util/Arrays` (`do_invoke`, `InvStatic`, `None => run_model (mr_class mr)`), so the Rocq models are
**not** shadowed. This is checked by `CollOps.collections` case 9 (`Arrays.fill` + `Arrays.copyOf` +
`Arrays.asList` in one run). **No Rocq-side change is needed** for `asList`. (If a Rocq model of
`asList` is ever added, the loaded Java one wins.)

### How the model avoids making false claims

- Paths that are not modelled call `java.util.ModelStuck.unsupported(String)`, a `native` method with
  no Rocq model: the machine is STUCK there ("no model for java/util/ModelStuck.unsupported...") and
  makes no claim. Call sites: `AbstractList.subList`, `ArrayList.subList/sort/clone`,
  `HashMap.clone`, `HashSet.clone`, `Arrays.asList(..).sort`, `ArrayList` capacities near
  `Integer.MAX_VALUE`, the unmodifiable entry set's `toArray`, a collection whose size changes while
  `toArray` iterates it, tree bins with Comparable key classes other than String and the boxes.
- The model never calls `Objects.equals/hashCode` (the Rocq `Objects.equals` model is STUCK on a
  callback to a loaded `equals`); it calls `equals`/`hashCode` of the keys directly, in the same
  order and direction as the JDK (`key.equals(existingKey)`).

### Implementation notes (differences that are not observable)

- One `HashMap.Node` class carries `LinkedHashMap`'s `before`/`after` links (the JDK has a separate
  `LinkedHashMap.Entry` class); `TreeNode extends Node`. Entry *identity* is modelled as in the JDK:
  treeify/untreeify replace the entry objects (an entry obtained before stops being live), tested in
  `treeBins`.
- Private field and helper names are our own (e.g. `HashMap.cTab/cIndex/...` hold the lookup state
  of `compute*`). Code that reads JDK-private fields by reflection is not supported (reflection is
  not modelled anyway).
- JDK 19+ sizing: `HashMap(Map)`/`putAll` into an empty map pre-size to `tableSizeFor(ceil(s/lf))`,
  `putAll` into a non-empty map resizes while `s > threshold`; `HashSet(Collection)` uses capacity
  `ceil(max(n,12)/0.75)`. Checked by `Sizing.sizing`: the pre-JDK-19 formulas give mismatches (13 of
  300 inputs in a scratch experiment).

## What is not modelled (calls are STUCK, never wrong)

- Classes: `TreeMap`, `TreeSet`, `LinkedList`, `ArrayDeque`, `PriorityQueue`, `Hashtable`,
  `IdentityHashMap`, `WeakHashMap`, `EnumMap/EnumSet`, `java.util.concurrent.*`, `Iterable` itself
  (built-in), `Comparator`, `Objects` (Rocq model), `Arrays` other than `asList` (Rocq models).
- Methods: `List.of/copyOf`, `Set.of`, `Map.of/ofEntries/entry/copyOf`, `Map.Entry.comparingBy*`,
  `stream`/`parallelStream`/`spliterator`/`toArray(IntFunction)`, `subList`, `sort`,
  `Collections.*` other than those listed above, `clone`, serialization, the JDK 21
  `SequencedCollection`/`SequencedMap` methods (`getFirst`, `reversed`, `putFirst`, ...; Camel is
  compiled with `--release 17` and cannot call them). The model interfaces do not extend
  `SequencedCollection`/`SequencedMap`, so `instanceof SequencedCollection` differs from JDK 21 (not
  expressible in `--release 17` code).
- `toArray(T[])` with a too-small array of a component type other than `Object`, `String`,
  `Integer`, `Long` (needs `java.lang.reflect.Array.newInstance`: STUCK).
- **Tree bins with equal hash codes that do not compare**: when a bin with >= 64 table slots holds
  more than 8 keys (7 for `compute*`) and two of them have *equal* hash codes, are of the same class
  and that class is not `C implements Comparable<C>`, the JDK orders them by
  `System.identityHashCode`. Its iteration order then depends on the identity hashes (demonstrated
  on HotSpot: target `MapOps.tieBreak` gives different results under
  `-XX:+UnlockExperimentalVMOptions -XX:hashCode=0/2/5`), so the model calls
  `System.identityHashCode`, which has no Rocq model: STUCK. Keys of *different* classes with equal
  hash codes need `Class.getName()` (no model: STUCK). A `null` key orders first (HotSpot identity
  hash codes are positive; assumption).
- Tree bins with equal hash codes of a user class that is `Comparable`: deciding "C implements
  Comparable<C>" needs the generic signature (`Class.getGenericInterfaces`): STUCK. String and the
  boxes (`Integer`, `Long`, `Short`, `Byte`, `Character`, `Boolean`) are handled.
- Keys that do not override `hashCode` (identity hash codes are not modelled by the machine).

## Differential tests

Test classes: `harness/jdkmodel/tests/org/rocqjvm/jdkmodel/*.java` (package
`org.rocqjvm.jdkmodel`). Each target takes ints from `gen_inputs.py`, derives a sequence of operations
from them with an LCG, and folds every observation (return values, iteration order of all views,
sizes, entry identity, exception *classes* via `getClass() ==`) into the int result. Key families:
`K` (test class with chosen hash: identity, `id<<4`, `id<<6` (one bin until the table has > 64 slots),
`id<<16` (only the `h ^ h>>>16` spreading separates them), multiplicative, negative, equal-hash
groups of 7, mixed), `Integer` (small, multiples of 16/64, `id<<16`, negative), `String` (Aa/BB blocks:
equal hash codes, tree bins ordered by `compareTo`), `Long` (`a<<32|b`: equal hash codes `a^b`, tree
bins ordered by `Long.compareTo`), `null` keys and values.

COUNTS_TABLE

Canaries (deliberately wrong models, `harness/jdkmodel/build.sh canary <name>`, 100 inputs per
selected target, seed 99) are all detected:

| canary | mutation | detected by (mismatching inputs) |
|---|---|---|
| `nospread` | `HashMap.hash` without `h ^ (h >>> 16)` (a different bin index function) | hashMap 56/100, linkedHashMap 52/100, treeBins 31/100, copies 36/100, ctor 32/100 |
| `rootfront` | tree bins: root not moved to the front of the bin list | treeBins 24/100, hashMap 1/100 |
| `cia-tail` | `computeIfAbsent/compute/merge` append instead of prepend | hashMap 40/100, treeBins 56/100 (linkedHashMap 0/100: its order does not depend on bins) |
| `lhm-access` | access-ordered `LinkedHashMap.get` does not bump `modCount` | linkedHashMap 10/100 |
| `al-iobe` | `ArrayList.get(-1)` throws `ArrayIndexOutOfBoundsException` | arrayList 96/100 |

(The `nospread` numbers are from an early run with seed 7 through `difftest.sh`; those rows were removed
from `harness/results/2026-10-23.tsv` because they are not results for the real model.)

Note on `harness/results/2026-10-23.tsv`: the development row `MapOps strings ... 100 mismatches` (18:09)
is **not** a model mismatch: the test passed `Arrays.asList(1, null, "x")`, whose varargs array is a
`Serializable[]`, and the machine threw `ArrayStoreException` on storing the `Integer` (request 1
below). The test was changed to use an `Object[]`.

## Requests for the Rocq side (I did not change any Rocq file)

1. **Bug (false result): the interfaces of the boxes are missing in `Machine.interfaces_of`.**
   `java/lang/Integer`, `Long`, `Short`, `Byte` implement `Comparable`, `Constable` (and Integer/Long
   also `ConstantDesc`), and their superclass `Number` implements `Serializable`; `Character` and
   `Boolean` implement `Serializable`, `Comparable`, `Constable`. Without them, `aastore` of an Integer
   into a `Serializable[]`/`Comparable[]` throws `ArrayStoreException` in the machine (javac makes such
   arrays for generic varargs with mixed argument types, e.g. `Arrays.asList(1, "x")`,
   `List.of(1, "x")`), and `checkcast`/`instanceof Comparable` on a box gives the wrong answer.
2. **Dispatch of private methods**: javac 11+ emits `invokevirtual` for private methods; the machine
   selects by the receiver's runtime class (`resolve_full p cn0`), so a subclass declaring a method
   with the same name and descriptor would be called instead (JVMS 5.4.6: a private resolved method
   is selected directly). Similarly JVMS 5.4.5 says a method only overrides a package-private method
   from the same run-time package; the machine lets a user subclass in another package "override"
   the java.util model's package-private hooks (`HashMap.newNode/afterNodeAccess/resize/...`,
   `ArrayList.checkIndex/growTo/...`). Request: select the resolved method when it is private, and
   check accessibility (same package) for package-private overriding. Until then, user subclasses of
   `HashMap`/`LinkedHashMap`/`ArrayList` that declare methods with these names are a soundness risk.
3. (optional) `String.compareTo(Ljava/lang/Object;)I` (the bridge method, reached by
   `invokeinterface Comparable.compareTo`) has no model; the boxes accept any descriptor. The
   collections model avoids it by casting, but generic code calling `Comparable.compareTo` on Strings
   is STUCK.
4. (optional) A model of "is class C declared `implements Comparable<C>`" (from the class file's
   `Signature` attribute) would remove the STUCK for tree bins with equal-hash keys of user Comparable
   classes; `Class.getComponentType` + `Array.newInstance` would remove the STUCK of `toArray(T[])`
   for other array types.
5. TRUST.md: the model classes are specifications like `Jdk.v` and belong in the trust base, checked
   by the targets in `harness/targets-jdkmodel.txt` (counts above).

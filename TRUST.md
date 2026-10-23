# Trust base

What a reader has to trust to believe a theorem like `WalCanUpdate.fix_correct`. Everything not on this
list is checked by the Rocq kernel.

## 1. Rocq
- The Rocq 9.3.0 kernel and `rocqchk`. The Rocq standard library (rocq-stdlib 9.2.0) is used only
  through definitions and proved lemmas. The development declares **no `Axiom`s and uses no
  `Admitted`** (this holds for every file in `_RocqProject`, including the Track C files under `theories/Concurrency/`).
  Check: `Print Assumptions WalCanUpdate.fix_correct.` prints "Closed under the global context".
- `vm_compute` (the bytecode VM used for kernel conversion) is used to evaluate the class-file parser
  on the bytes and for the concrete counterexamples. It is part of the standard kernel TCB; for a
  stricter check, replace `vm_compute` by `compute` (slower, same result) or run `rocqchk`.

## 2. The JVM model (theories/Core/*.v)
The semantics is our reading of the JVMS SE 21, chapter 2 and chapter 6. It is the main thing to trust,
and the reason for the differential tests (section 4): every phase compares the extracted model with
HotSpot on random inputs, and a mismatch is treated as a model bug.
- `Int.v`: int/long arithmetic. Corner cases named in the JVMS are checked by `Example`s
  (MIN / -1, MIN % -1, division by zero, shift masks, sign/zero extension).
- `Semantics.v`: one-method small-step interpreter. Instructions without semantics are `Stuck`, and a
  stuck run never yields a result, so an unsupported instruction can make a theorem unprovable but never
  makes a false theorem provable.
- `Float.v`: IEEE 754 arithmetic as functions on bit patterns (one rounding function); correct rounding is
  tested (250,000 inputs per op, 0 mismatches), not proved against real numbers (Flocq is not used).
- `Machine.v`: the multi-frame machine (heap, arrays, exceptions, calls, class initialisation, lambdas).
- Not modelled: threads (Track C), reflection, class loaders, natives without a model. A run that needs any of
  them is `Stuck`, so theorems are only about executions inside the modelled part; the proof itself shows this.

## 3. The loader
- `tools/build-camel-classes.sh`: runs `javac --release 17 -g` (JDK 21.0.12) on the Camel sources
  exported with `git archive` at a recorded commit. Trusted: javac, git. The commit, javac version
  and SHA-256 of each class are written to `classes/<label>/BUILD-INFO`.
- `tools/classdump.py`: copies the bytes of a `.class` file, unchanged, into a Rocq string of hex
  digits (plus SHA-256 and provenance in the header). It does not interpret the file.
  `tools/check-dumps.sh` re-derives the hex and SHA-256 from the class files and compares them.
- `theories/Loader/Hex.v`, `theories/Loader/ClassFile.v`: hex decoding, class-file parsing, constant
  pool resolution and instruction decoding are **inside Rocq**: they are part of the model (section
  2), and are exercised by every differential test, because the extracted harness uses the same
  parser on the same files.

## 4. Differential testing (evidence for 2 and 3, not part of the proof)
- `harness/`: the model is extracted to OCaml (standard extraction of bool/option/list/pair and of
  `string`/`ascii` to OCaml strings/chars; `Z`, `positive`, `nat` stay unary/binary, so no OCaml
  machine arithmetic is involved) and run against HotSpot (`java` 21.0.12, `DiffRunner` via
  reflection) on the same inputs. Counts per method are in `harness/results/*.tsv` and STATUS.md.

## 5. JDK models (specifications of JDK methods, trusted, differentially tested)
`theories/Jdk/Jdk.v`, `theories/Jdk/Strings.v`. Each modelled method is a Rocq function written from the JDK 21
source of java.base and checked against HotSpot by the corpora `harness/corpus3` (Strs), `corpus2` (Heap),
`corpus5` (Lam):
- `java.lang.String`: length, isEmpty, hashCode, toString, intern, charAt, equals, equalsIgnoreCase (all three
  JDK code paths: Latin-1, mixed, UTF-16 with surrogate pairs), compareTo, indexOf/lastIndexOf (char and String,
  with JDK index clamping), contains, startsWith (both), endsWith, concat, substring (both; identity and `""`
  results as in the JDK), trim, replace(char,char), toCharArray, valueOf(int/long/char/boolean/Object).
- `java.lang.StringBuilder`: constructors, append(String/Object/CharSequence/int/long/char/boolean), toString,
  length, charAt, setLength, deleteCharAt, insert(int,String).
- `java.lang.Character`: toUpperCase/toLowerCase (char and int), isDigit/isLetter/isLetterOrDigit/isWhitespace/
  isUpperCase/isLowerCase, digit, isHigh/LowSurrogate. **Unicode data is a parameter (`uenv`)**: theorems quantify
  over all tables, plus explicitly stated facts checked against JDK 21 by `harness/check_unicode_facts.py`.
- `Integer`/`Long`: parseInt/parseLong (radix 10), toString, compare, Math.max/min/abs, boxing (`valueOf` with the
  JLS caches, xxxValue, equals, hashCode, toString, compareTo), Boolean.TRUE/FALSE.
- `java.util.Objects`: requireNonNull, equals (Strings and boxes), hashCode (Strings).
- `System.arraycopy` (all exception cases, element-wise store check), `Arrays.fill`/`copyOf`, array `clone`.
- `java.lang.Enum`: constructor, ordinal, name/toString, equals. `Object`: constructor, equals, getClass.
- slf4j: `LoggerFactory.getLogger` returns an opaque object; `Logger.isXxxEnabled()` comes from the environment
  (`jenv.j_log_enabled`, theorems state it); every void `Logger` method has no effect on the modelled state.
- Constructors of the java.lang exception classes: no observable state (messages/causes are not modelled).
Not modelled on purpose: `Object.hashCode`/`identityHashCode` (nondeterministic), I/O, threads, reflection.

## 6. Test drivers and assumptions stated in theorems
- `harness/camel/wal-*/WalScenario.java` and `harness/camel/cim/.../CimScenario.java` are our test drivers for the
  kernel-computed whole-class scenario theorems (`WalScenario.v`, `CimScenario.v`). The unbounded camel-wal theorems
  (`WalRing.v`) use no driver: they quantify over the heap and over every sequence of calls.
- `CimScenario.v` loads two java.util **model classes** of Track B (`AbstractMap`, `Map`; clean-room Java,
  `docs/jdk-collections-status.md`), which are trusted like the Rocq JDK models of section 5 and tested the same way.
  Its case mapping is a concrete table for ASCII and Latin-1 (`l1_uenv`), which agrees with JDK 21 on the characters
  the scenarios use; the 2,000-run differential test of the same driver uses the full JDK 21 tables.
- The camel-wal theorems take the JVM-level preconditions as hypotheses (`wal_env`): the classes are initialised and
  not erroneous, `TransactionLog.LOG` holds a logger, `EntryState.FAILED` a reference; `add` gets a LogEntry object.
  Class initialisation itself is covered by the scenario theorems, not by the unbounded ones.
- The Unicode facts of `CimSpec.jdk_facts` and of `cih_inconsistent_supplementary` are hypotheses of the
  theorems, not axioms; `harness/check_unicode_facts.py` checks them against the JDK 21 tables.

# rocq-jvm

A formal model of the Java Virtual Machine in [Rocq](https://rocq-prover.org) (formerly Coq): the JVMS bytecode
semantics, a class-file loader and models of the JDK library, all inside the prover. With it you can prove properties
of **any compiled Java bytecode, for all inputs**, by stating what a method should do and proving that the real
`.class` file does it.

The model is general. Nothing in `theories/Core`, `theories/Loader` or `theories/Jdk` is specific to one project.
The first case study is Apache Camel: the proofs in `theories/Camel` are about the actual `.class` files that
`javac` produces from a recorded Camel commit, not about a hand translation of the source. The Rocq kernel checks
every proof. The model is checked against HotSpot (JDK 21) by differential testing on millions of random inputs.

To prove something about your own code, compile it, dump the class files with `tools/classdump.py`, load them as in
`theories/Camel/CimProg.v`, and state the theorem. The Camel files show the pattern, from a single method
(`WalCanUpdate.v`) to a whole class over every call sequence (`WalRing.v`, `CimSession.v`).

Status: work in progress, started 2026-10-23. See [STATUS.md](STATUS.md) for the full list of what is proved and
[TRUST.md](TRUST.md) for exactly what a reader has to trust.

---

## The idea, with a Camel example

Camel's write-ahead log has a method `TransactionLog.canUpdate(...)`. It decides whether a log entry is still
in the ring buffer and so may be updated. On Camel `main` it has a bug (CAMEL-26088), and a fix branch exists.

There are three ingredients.

| | What it is | Where |
|---|---|---|
| **Model** | The rules of the JVM, written as Rocq definitions: what every bytecode instruction does to the stack, locals, heap, exceptions and calls (JVMS chapter 6). Written once, used for every method. | `theories/Core/` |
| **Spec** | What the method *should* do, as a mathematical statement. Here: "`canUpdate` returns true exactly when entry *k* is still in the ring". | in the theorem files, for example `theories/Camel/WalCanUpdate.v` |
| **Theorem** | "For **every** input, running the model on these exact bytes gives the answer the spec says." Rocq checks the proof. | e.g. `WalCanUpdate.fix_correct` |

Nothing is executed on a JVM to obtain the theorem. The `.class` bytes are loaded into Rocq: the class-file
parser itself is written in Rocq. The proof is a mathematical argument about what those bytes do under the model.
It covers all 2^32 values of each int argument and every heap, not a sample.

For `canUpdate` the result is:
- on the **fix's** bytecode, the spec is **proved** (`fix_correct`);
- on **main's** bytecode, the spec is **refuted**: Rocq checks two concrete counterexamples, an off-by-one and a
  stale layer (`main_refuted`).

**Why can the model be trusted?** The model is extracted to OCaml and run side by side with HotSpot on the same
random inputs (`harness/`). Results and exceptions must agree. A mismatch is treated as a bug in the model and
fixed before anything is proved with it.

---

## Results so far (Camel case study and the memory model)

Every theorem below reports `Print Assumptions` = *Closed under the global context*: no axioms, nothing admitted.

### camel-wal `TransactionLog` (CAMEL-26088)
- `canUpdate`: proved on the fix and refuted on main, for all ints.
- Whole class, unbounded (`WalRing.session_ok`, `wal_from_constructor`): after `new TransactionLog(cap)`, for
  **every capacity and every sequence** of `add` / `update` calls, each `add` returns a new container. Each
  `update` of entry *k* returns *k*'s container if *k* is still in the ring, and null otherwise.
- Whole class on main, concrete runs checked in the kernel: updating entry 2 marks entry 8 (capacity 3, 10 adds),
  and a live entry is rejected (capacity 4, 9 adds).

### camel-util `CaseInsensitiveMap` (the Camel message-headers map)
- Main's bytecode is shown to leak slots: repeating `put("h"); remove("H")` grows the slot arrays without bound
  (`CimScenario.main_churn_grows`). The fix keeps them bounded (`fix_churn_bounded`).
- `caseInsensitiveHash`: the real bytecode is proved equal to its spec for **every** String and any Unicode tables
  (`CimHash.caseInsensitiveHash_correct`).
- **Whole class, unbounded, on the fix (`CimSession.session_ok`):** from any heap holding a valid map, every
  sequence of `get` / `put` / `remove` calls behaves exactly like an insertion-ordered map with case-insensitive
  keys. This covers all four internal paths of `put`: key present, free slot, compaction (the fix) and growth.
  The slot arrays never exceed `max(initial length, 3 × threshold)`, however many operations run.
  - The theorem assumes `resize()` is not reached (fewer than `threshold` entries whenever a new key is put).
  - It also assumes that, on the keys used, `equalsIgnoreCase` is an equivalence consistent with the hash.
- **A real defect found while writing the spec:** for supplementary characters (e.g. U+10400 / U+10428),
  `equalsIgnoreCase` says two keys are equal but `caseInsensitiveHash` gives them different hashes. The map then
  stores both keys and `get` misses (`CimSpec.cih_inconsistent_supplementary`). The behaviour is reproduced on
  HotSpot with the real classes, on main and on the fix. Details: [docs/finding-cim-supplementary-case.md](docs/finding-cim-supplementary-case.md).

### Java memory model (Track C)
- An abstract event model of executions (JLS 17.4) with happens-before, data races and sequential consistency.
- The DRF-SC theorem: a race-free execution of a well-formed program is sequentially consistent
  (`DRF.drf_execution_sc`, `DRF.drf_sc_no_thin_air`).
- The JLS 17.4.8 example, proving that happens-before consistency alone is *not* enough
  (`Examples.hb_model_not_drf_sc`).
- This part is not yet connected to the bytecode machine.

---

## What the model covers

- **Values:** int/long with exact JVMS wraparound, division and shift corner cases. float/double as IEEE 754 on bit
  patterns, with the JVMS NaN and conversion rules. Floats are tested on 250,000 inputs per operation with
  0 mismatches; their rounding is tested, not proved.
- **Instructions:** 199 of the 202 opcodes. `jsr`/`ret`/`jsr_w` are rejected, since class files of version
  51 or later cannot contain them.
- **Class files:** a full parser written in Rocq: constant pool, fields, methods, Code, exception tables,
  BootstrapMethods, modified UTF-8.
- **Machine:**
  - heap objects and all array kinds with store checks;
  - exceptions and handler search across frames;
  - all invoke kinds with resolution and virtual/interface dispatch;
  - class initialisation (JVMS 5.5);
  - `checkcast`/`instanceof`;
  - monitors (single thread);
  - interned strings;
  - `invokedynamic` for string concatenation and lambdas.
- **JDK:** Rocq models of String, StringBuilder, Character (with Unicode tables as a parameter),
  Integer/Long/Math, boxing caches, Objects, `System.arraycopy`, Arrays, Enum and the slf4j loggers. java.util
  collections (ArrayList, HashMap with tree bins, LinkedHashMap, sets, Collections views) are clean-room Java
  model classes that the machine loads and runs.
- **Not modelled yet:** threads in the machine (the memory model above is separate), reflection, class loaders,
  and natives without a model. A run that needs any of these gets *stuck*. A stuck run never produces a result,
  so a missing feature can make a theorem unprovable but can never make a false theorem provable.

### Differential testing (extracted model vs HotSpot 21.0.12)

All corpora report **0 mismatches**, for example:

| Corpus | Inputs per method |
|---|---|
| int/long ops | 70 methods × 100,000 |
| heap | 35 methods × 10,000 |
| strings | 53 methods × 10,000 |
| floats | 31 methods × 10,000 |
| lambdas | 15 methods × 10,000 |
| java.util models | 14 targets × 10,000 |
| whole-class CaseInsensitiveMap scenarios | 2,000 runs |
| whole-class camel-wal scenarios | 4,516 runs |

The full table is in [STATUS.md](STATUS.md). Canary runs, with deliberately broken models, confirm that the
comparison catches wrong models.

---

## Repository layout

```
theories/
  Core/          the JVM model: Int, Float, Semantics (frames), Machine (heap, calls, exceptions, clinit), Logic (proof rules)
  Loader/        hex decoding and the class-file parser, in Rocq
  Jdk/           models of JDK methods (String, StringBuilder, Character, ...)
  Classes/       the real .class files as hex strings (generated by tools/classdump.py, SHA-256 in the header)
  Camel/         the theorems about Camel code (Wal*.v, Cim*.v)
  Concurrency/   Track C: events, orders, executions, DRF-SC
  Extract.v      extraction of the model to OCaml for the differential tests
classes/         the compiled Camel classes, with BUILD-INFO (commit, javac version, SHA-256)
harness/         differential testing: OCaml drivers, Java DiffRunner, corpora, input generator, comparison
tools/           build Camel classes at a commit, dump .class files to Rocq, check the dumps, coverage
docs/            opcode coverage, float status, java.util models, Track C design, findings
PLAN.md          phases and checkpoints
STATUS.md        what is proved, what is assumed, test counts
TRUST.md         the trust base
```

## Building

Requirements: Rocq 9.3.0 with rocq-stdlib. For the differential harness you also need OCaml with ocamlfind,
JDK 21 and Python 3.

```sh
make                      # builds every theorem; about 16 minutes on one core (-j1)
```

To check that a theorem uses no axioms, open a Rocq session with `-Q theories JVM` and run:

```coq
From JVM.Camel Require Import CimSession WalRing.
Print Assumptions CimSession.session_ok.     (* Closed under the global context *)
Print Assumptions WalRing.session_ok.
```

Differential tests:

```sh
harness/build.sh                                  # builds the model and extracts the OCaml drivers
harness/difftest.sh harness/targets-phase1.txt 100000
MODE=machine harness/difftest.sh harness/targets-heap.txt 10000
```

To rebuild the Camel `.class` files from source at the recorded commits, see `tools/build-camel-classes.sh` and
`tools/check-dumps.sh`.

## Branches

- `master`: everything listed above.
- `model-gaps`: model work that is complete and differentially tested but not yet merged into `master`. It adds
  JVMS-exact field resolution and initialisation order, full method selection (JVMS 5.4.3–5.4.6),
  `invokedynamic` for `Foo::new`, `altMetafactory`, records and pattern switches, and HotSpot's exception
  messages. Merging needs a full rebuild of the Camel proofs on top of it.

## Next

- Merge `model-gaps`.
- Prove the key-string assumptions of the CaseInsensitiveMap theorem for ASCII keys.
- Cover `resize()`.
- Then the Camel helpers in StringHelper, FileUtil and URISupport.
- Later: connect the memory model to the machine, then reflection and class loading.

## Credits

The idea follows Anthropic's work on proving compiled machine code in Rocq against a formal machine model,
applied here to JVM bytecode. Owner: Shashank Mohan Jain ([@allthingssecurity](https://github.com/allthingssecurity)).
The class files under `classes/` and `theories/Classes/` are compiled from [Apache Camel](https://github.com/apache/camel),
which is licensed under the Apache License 2.0.

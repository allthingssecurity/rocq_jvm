# Trust base

What a reader has to trust to believe a theorem like `WalCanUpdate.fix_correct`. Everything not on this
list is checked by the Rocq kernel.

## 1. Rocq
- The Rocq 9.3.0 kernel and `rocqchk`. The Rocq standard library (rocq-stdlib 9.2.0) is used only
  through definitions and proved lemmas. The development declares **no `Axiom`s and uses no
  `Admitted`** (Phase 1 files; Track C files list their own in `docs/track-c-status.md`).
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
- Not yet modelled (Phase 1): heap, objects, arrays, calls, float/double, exception handlers
  (a handler that would catch is `Stuck`), threads. Theorems are about methods whose execution
  stays inside the modelled subset; the proof itself shows this, since a stuck path cannot return a
  value.

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

## 5. Axiomatised natives
None yet (no calls are modelled). From Phase 4 on, each native method or JDK class used by a proof is
listed here with its Rocq specification and the differential test that checks it.

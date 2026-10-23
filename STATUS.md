# rocq-jvm status

Rocq 9.3.0 + rocq-stdlib 9.2.0. Build: `make` (uses `rocq makefile`, `-j1`). Trust base: `TRUST.md`.
Opcode table: `docs/opcode-coverage.md`. Differential-test counts: `harness/results/*.tsv`.

## Phase 1 (tracks A+B), started 2026-10-23 — in progress

### Proved (all `Print Assumptions`: "Closed under the global context": no axioms, nothing admitted)
| Theorem (theories/Camel/WalCanUpdate.v) | Statement |
|---|---|
| `main_behaviour` | for all int a b c d, main's `canUpdate(IIII)Z` returns `(a==c && b>=d) \|\| (a>c && b<d)` |
| `fix_behaviour` | for all int a b c d with a >= 0, the fix's `canUpdate` returns `(a==c && b>=d) \|\| (a==c+1 && b<=d)` |
| `fix_correct_exact`, `fix_correct` | for every capacity 1..INT_MAX, number of adds n, added entry k < n (current layer fits in an int), the fix returns exactly "entry k is still in the ring" (n - capacity <= k) — the contract `canUpdate_contract` of `WalSpec.v` |
| `fix_correct_any_fuel` | the same for any fuel >= 100 |
| `main_refuted` | main does not satisfy the contract |
| `main_rejects_live_entry` | capacity 377, 10345 adds, entry 9968: live, main returns false (`canUpdate(27,166,26,166)`: the off-by-one) |
| `main_accepts_overwritten_entry` | capacity 575, 81556 adds, entry 28088: overwritten, main returns true (`canUpdate(141,481,48,488)`: the stale layer) |

The methods are obtained in Rocq by `load_method <bytes of the .class> "canUpdate" "(IIII)Z"`
(parser + decoder in `theories/Loader/ClassFile.v`); the decoded code is identical to `javap -c`.

Bytecode under proof (`classes/*/BUILD-INFO`, `javac 21.0.12 --release 17 -g`):
- main: apache/camel `36bebb520a632d0d02a90680bba60e2a1e3941f9`, `TransactionLog.class` sha256 `3431a587…c4b`
- fix: fork branch `camel-wal-update-after-roll-over` `e72996b974ad97f55b3ba3f73497adbf27a6609d`
  (same hash as the `fork` remote of camel-lean/camel), sha256 `1de5da80…cfc02`

### Assumed
- The ring-buffer equations of `WalSpec.v` (what `add` does to `currentLayer`/`currentIndex`) are read from
  the Java source of `add`; proving `add`'s bytecode needs fields and arrays (Phase 2).
- The model and loader themselves (see TRUST.md), checked by differential testing below.

### Model
- `Core/Int.v`: int/long per JVMS (wraparound, idiv/irem/ldiv/lrem by zero and MIN/-1, shift masks, i2b/i2c/i2s/l2i, lcmp), corner cases as `Example`s.
- `Core/Semantics.v`: frames, operand stack (category-2 aware: every form of pop2/dup*/swap), locals (two-slot longs, invalidation of a split long), all int/long arithmetic, branches, `tableswitch`/`lookupswitch`, returns with JVMS 9+ `ireturn` narrowing, `aconst_null` and reference compares, VM-thrown ArithmeticException; fuel-bounded `run` with `run_mono`.
- `Loader/ClassFile.v`: whole class file (constant pool, fields, methods, attributes, Code, exception table), all 202 opcodes decoded incl. `wide`, switch padding, `goto_w`.
- Opcodes with semantics: 111 of 202; 108 of them exercised by the differential tests (not exercised:
  `aload_0`, `astore_0`, `areturn` — need reference parameters/results, Phase 2).

### Differential testing (extracted model vs HotSpot 21.0.12)
- Targets: 70 corpus methods (`harness/corpus/.../Ops.java`), 4 in `Ops2.java` (plain `ldc`, local references, `goto_w`), 17 hand-assembled `StackOps.class` methods (every form of pop/pop2/dup*/swap, nop), `canUpdate` main and fix.
- Run 1: 88 methods × 2,000 inputs = 176,000: **0 mismatches**, 0 stuck.
- Run 2: 88 methods × 100,000 inputs: in progress (all methods finished so far: 0 mismatches).
- Canary (`harness/canary.sh`): iadd-vs-isub and main-vs-fix are reported as mismatches (24,064 of 100,000 for main vs fix).

### Next in Phase 1
- finish run 2, add Ops2 and the nop case at 100k; then Phase 2 (heap, arrays, exception handlers) and `add`/`update` of TransactionLog.

## Track C (JMM): survey and abstract event model running as a separate agent; see `docs/track-c-*.md` when done.

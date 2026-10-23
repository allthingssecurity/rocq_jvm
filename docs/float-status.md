# Float / double model: status

Scope: the `float` and `double` instructions of JVMS SE 21 chapter 6 as pure
Rocq functions on IEEE 754 bit patterns (`theories/Core/Float.v`), checked
against HotSpot 21.0.12 by a differential test (`harness/float/`).

## Representation and conventions

- A `float` is its binary32 bit pattern as `Z` in `[0, 2^32)`; a `double` is
  its binary64 bit pattern as `Z` in `[0, 2^64)` (unsigned). Inputs outside
  the range are read by their low 32/64 bits.
- `int`/`long` results (f2i, f2l, d2i, d2l, the comparisons) use the signed
  `Z` convention of `JVM.Core.Int` (`in_int`, `in_long`).
- Arithmetic is done once, exactly: operands are decoded to
  `Fin s m e` = (-1)^s * m * 2^e (or `Inf s` / `NaN`), the exact result is
  an integer times a power of two (division: `mx * 2^(2*mbits+6) / my`
  plus a sticky bit), and one function `round f s m e` rounds it (to
  nearest, ties to even; gradual underflow; overflow to infinity). It is
  shared by every operation and both formats (`fmt` = `binary32` |
  `binary64`).
- Only one floating-point mode exists. Since Java SE 17 (JEP 306) every
  operation is strict (`strictfp` has no effect, and the old "FP-extended"
  value sets are gone; JVMS 2.8). The model implements only that mode. Class
  files older than version 61 that are not `ACC_STRICT` could in theory
  use extended exponent ranges on old JVMs. HotSpot 17+ ignores this and so
  does the model.
- **NaN results.** The JVMS does not fix NaN payloads. Every operation
  returns the canonical quiet NaN (`QNAN32` = 0x7fc00000, `QNAN64` =
  0x7ff8000000000000). The exception is `fneg32`/`dneg64`, which flip the
  sign bit of any input, NaNs included. **The differential test therefore
  canonicalises NaNs on the Java side** (`Float.floatToIntBits`,
  `Double.doubleToLongBits`) for every operation. The model's outputs are
  *not* canonicalised, except `fneg`/`dneg`, whose model result goes
  through `canon32`/`canon64`. In addition, `fneg_raw`/`dneg_raw` compare
  the raw model `fneg32`/`dneg64` against `floatToRawIntBits(-x)` /
  `doubleToRawLongBits(-x)`. HotSpot agrees with the model on those too: it
  flips the sign bit and keeps the payload.
- frem/drem are C `fmod` (truncating remainder, sign of the dividend,
  exact), not IEEE `remainder`. NaN if either operand is NaN, the dividend
  is infinite, or the divisor is zero. The dividend itself if the dividend
  is finite and the divisor infinite, or if the dividend is zero. For large
  exponent gaps it uses `2^d mod my` by square-and-multiply (`pow2mod`,
  proved equal to `2 ^ d mod m`).

## Public names (for Semantics.v)

All have type `Z -> Z -> Z`, `Z -> Z` or `bool -> Z -> Z -> Z` (module
`JVM.Core.Float`):

| JVM instruction | Rocq function |
|---|---|
| fadd fsub fmul fdiv frem fneg | `fadd32 fsub32 fmul32 fdiv32 frem32 fneg32` |
| dadd dsub dmul ddiv drem dneg | `dadd64 dsub64 dmul64 ddiv64 drem64 dneg64` |
| i2f i2d l2f l2d | `i2f i2d l2f l2d` (argument: signed `Z`) |
| f2d d2f | `f2d d2f` |
| f2i f2l d2i d2l | `f2i f2l d2i d2l` (result: signed `Z`, NaN to 0, toward zero, saturating) |
| fcmpl fcmpg | `fcmpl fcmpg`, or `fcmp32 (g : bool)` (`g = true` is fcmpg) |
| dcmpl dcmpg | `dcmpl dcmpg`, or `dcmp64 (g : bool)` |

Helpers: `QNAN32 QNAN64`, `is_nan32 is_nan64`, `canon32 canon64`. The
generic layer is `fmt binary32 binary64 decode fval(NaN|Inf|Fin)
is_nan is_inf is_zero is_subnormal is_normal is_finite sign_bit
biased_exp fraction round add sub mul div rem neg of_int convert to_int
cmp`. Range predicates are `in_float x := 0 <= x < 2^32` and
`in_double x := 0 <= x < 2^64`.

## Proved (no Axiom, no Admitted; `Print Assumptions` = closed)

- `fneg32_involutive`, `dneg64_involutive` (`neg_involutive`).
- `fcmpl_fcmpg_agree`, `dcmpl_dcmpg_agree`: equal unless an operand is NaN.
  `cmp_nan`: NaN gives 1 for *g, -1 for *l. `cmp_range`: result is in
  {-1, 0, 1}. `cmp_antisym`: `cmp g x y = - cmp (negb g) y x`.
  `cmp_refl` holds on non-NaN values.
- `f2i_range`, `d2i_range` (`in_int`) and `f2l_range`, `d2l_range`
  (`in_long`). `to_int_nan`: NaN gives 0.
- **Every float/double result is a valid bit pattern** (`round_range` for
  any format with `mbits >= 1`, `ebits >= 2`). From it: `fadd32_range` …
  `frem32_range`, `dadd64_range` … `drem64_range`, `i2f_range`,
  `l2f_range`, `i2d_range`, `l2d_range`, `f2d_range`, `d2f_range` hold
  unconditionally. `fneg32_range`/`dneg64_range` hold for in-range inputs.
- `add_comm`/`mul_comm` (so `fadd32_comm`, `dadd64_comm`, `fmul32_comm`,
  `dmul64_comm`), including signed zeros and NaNs.
- `pow2mod_spec`.
- 56 `Example`s checked by computation. Expected values were taken from
  HotSpot. They cover: 0.1f+0.2f (= 0.3f), 0.1+0.2 (= 0x3fd3333333333334),
  1/3, 1/0, -1/0, 0/0, 1/-0, inf-inf, inf*0, signed-zero sums and products,
  MIN_VALUE/2 = 0 (tie to even), 1.5*MIN_VALUE, MIN_NORMAL - MIN_VALUE,
  MAX*2 = inf, rounding ties (2^24+1, i2f 16777217/16777219, l2d 2^53+1),
  l2f/l2d at the long limits, f2i of NaN/±1e20/-1.5, d2l(-inf),
  f2l(inf), d2f of Double.MAX_VALUE / FLT_MAX+half-ulp (to inf) / just
  below (to FLT_MAX) / 1e-50 (to 0), f2d, fmod signs (5.5%2, -5.5%2,
  5.5%-2, -4%2 = -0, 1%inf, inf%1, 1%0, -0%1), fneg of NaN, fcmpl/fcmpg
  with NaN, +0 vs -0, -inf.

Not proved (only tested): that `round` is the *correctly rounded* value
(no real-number semantics is formalised; that would need Flocq or an
equivalent, which is not installed), that `cmp_key` orders values
correctly, and the sticky-bit argument for division (it is argued in a
comment).

## Differential test

- `harness/float/FloatExtract.v` extracts the functions to OCaml
  (`ExtrOcamlBasic`, `ExtrOcamlNativeString`; `Z`/`positive` stay Rocq
  inductives, no OCaml machine arithmetic in the model). It also defines
  two *mutant* roundings used only by the canary (ties-away;
  flush-to-zero) and proves `add_mut 0 = add` and `mul_mut 0 = mul`.
- `harness/float/model_float.ml` is the OCaml driver. It only parses and
  prints.
- `harness/float/FloatHarness.java` generates inputs (`gen`) and evaluates
  them on HotSpot (`eval`). The same `*.in` files feed both sides.
- `harness/float/compare.py` compares outputs line by line.
- `harness/float/run.sh` does everything.

Input generation is seeded (`SplittableRandom`) and biased towards special
values:
- ±0, ±inf, quiet and signalling NaNs with payloads, MIN_VALUE,
  MAX_VALUE, MIN_NORMAL, the largest subnormal.
- Powers of two with edge significands, the subnormal range.
- Values around ±2^24, 2^31, 2^53, 2^63, 2^64.
- Significands shaped as rounding ties, ±1 ulp, at arbitrary positions.
- Fully random patterns.
- For binary operations, the second operand is often related to the first:
  its negation (exact cancellation), ±few ulps, a nearby exponent (±30/±60
  and around ±24/±53, which gives alignment ties), or small constants.
- For d2f: doubles near float values with ties at float precision, the
  float subnormal range and the overflow threshold.
- For i2f/l2f/l2d: odd 25-bit and 54-bit values shifted (ties) ±1, and
  numbers with random bit lengths.

The operand mix for binary operations is about 86% normal, 8% NaN, 5%
subnormal, 0.6% inf and 0.6% zero. Results are about 2-3% subnormal,
5-14% zero, 1-10% inf and 12-14% NaN (17% inf and 11% subnormal for d2f).

### Results (2026-10-23, OpenJDK 64-Bit Server VM 21.0.12.1+1, x86-64)

| run | inputs per op | ops | mismatches |
|---|---|---|---|
| default (tiered C1/C2 JIT plus interpreter), seed 20261023 | 250,000 | 28 | **0** |
| `-Xint` (template interpreter only), seed 987654321 | 250,000 | 28 | **0** |

The 28 compared operations are `fadd fsub fmul fdiv frem fneg fneg_raw
dadd dsub dmul ddiv drem dneg dneg_raw i2f i2d l2f l2d f2d d2f f2i f2l d2i
d2l fcmpl fcmpg dcmpl dcmpg`. Every op had 250,000 inputs and 0
mismatches in both runs, for 7,000,000 comparisons per run. Full
summaries are in `harness/float/results/`.

### Canary (the comparison detects differences)

Seed 20261023, 250,000 inputs each; mismatches are expected here:

| canary | mismatches |
|---|---|
| model fadd vs JVM fsub | 244,993 |
| model dadd vs JVM dsub | 245,866 |
| model fcmpl vs JVM fcmpg | 138,929 |
| mutant round ties-away-from-zero: fadd / dadd / fmul / dmul | 6,183 / 5,916 / 2,114 / 1,882 |
| mutant flush-to-zero (no gradual underflow): fadd / dadd / fmul / dmul | 6,172 / 4,888 / 8,026 / 3,400 |

The `-Xint` run gives similar numbers. The mutants change one rule of
`round`, so their mismatches show that exact ties and subnormal results
are hit thousands of times per operation.

## Known gaps

- Only the strict (SE 17+) semantics; see above.
- NaN payload propagation is not modelled. The model is one admissible
  JVM; HotSpot's payloads are not compared, except for fneg/dneg (raw).
- The proofs show results are valid bit patterns but do not show correct
  rounding against real numbers. Correct rounding is tested only.
- Library methods that are not bytecodes (`Math.fma`, `StrictMath.*`,
  `Float.floatToFloat16`, etc.) are out of scope.
- Not yet wired into `Semantics.v`; that is the other agent's job. That
  agent also needs `ldc`/`fconst`/`dconst` to produce bit patterns.
  `fconst_1` = 0x3f800000, `fconst_2` = 0x40000000, `dconst_1` =
  0x3ff0000000000000.

## Rebuild and rerun

```sh
export OPAMROOT=/opt/opamroot; eval $(opam env --switch rocq --set-switch)
cd /home/claude/rocq-jvm
rocq compile -Q theories JVM theories/Core/Float.v      # ~2 s; needs JVM.Core.Int compiled

# full differential test (about 3.5 min on 2 cores; about 300 MB of work files in harness/float/_work)
harness/float/run.sh
# variants
N=1000 harness/float/run.sh                             # quick
SEED=987654321 JAVA_OPTS=-Xint WORK=/some/dir harness/float/run.sh
```

`run.sh` recompiles Float.v and runs the extraction in
`harness/float/_build` (which writes `float_model.ml/.mli`). It then builds
`model_float.exe` with `ocamlfind ocamlopt` and the Java side with `javac`.
Next it generates the inputs (`java -Xmx512m`, under `nice`), runs HotSpot
and the model, and compares. It exits non-zero on any mismatch. The
canary table is printed after the main table. `harness/float/_work` can be
deleted afterwards. Nothing is vendored and there are no new opam
dependencies.

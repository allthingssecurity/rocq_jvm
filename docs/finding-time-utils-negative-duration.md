# TimeUtils.isPositive classifies negative fractional durations as positive

Confirmed 2026-10-24. New relative to the local prior findings; not reported externally.

For `Duration.ofNanos(-1)`, `TimeUtils.isPositive` returns true; JDK `Duration.isPositive()` returns false.

Java Duration stores normalized seconds and a nonnegative nanosecond adjustment. Minus one nanosecond is represented as seconds = -1, nanos = 999999999. Camel computes:

```java
return dur.getSeconds() > 0 || dur.getNano() != 0;
```

The second disjunct therefore accepts a negative duration whenever its fractional adjustment is nonzero. The [Duration specification](https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/time/Duration.html) documents the normalized fields and positivity excluding zero.

## Formal evidence

`theories/Camel/NewBugs.v`:

- `negative_nanosecond_is_reported_positive`: a valid Duration heap object representing exactly -1 ns makes the actual TimeUtils bytecode return true.
- `duration_controls`: -1 second and zero return false; +1 ns and +1 second return true.

The Duration getter calls execute the real `java/time/Duration.class` extracted from OpenJDK 21.0.11's java.base.jmod. The witness starts with a valid normalized object and initialized Duration class; it does not prove Duration construction or its class initializer. TimeUtils and its static initializer execute in the model, using the existing SLF4J model. No new native model is introduced.

HotSpot reproduces the sign error for -1, -999999999 and -1000000001 ns and agrees with all four controls. The formal theorem is a concrete counterexample, not a general theorem over all Duration values.

## Scope and provenance

- Compiled unchanged from Camel commit `bd4d2ba20d6a268b66949712d00073069a8e333d`, javac 21.0.11, --release 17 -g.
- Class SHA-256: `381c104997aa3c5ce1307bcbec75920acd123f7424306106d75bd934bd52b115`.
- The faulty method remains identical in the upstream default-branch source; retrieved TimeUtils blob `5dbfa3a2890056ef55efbf6817a2ef94cf3a063c`. Other methods in that upstream file differ from the pinned source.
- No matching local prior finding, or GitHub issue/PR result for the queried TimeUtils/isPositive terms. This is not an exhaustive Jira duplicate search.
- No internal production caller found in the local core/components search. This is a public utility's classification error; no route-level or security impact is claimed.

A Java-17-compatible correction is `!dur.isNegative() && !dur.isZero()`. No production fix has been applied in this audit.

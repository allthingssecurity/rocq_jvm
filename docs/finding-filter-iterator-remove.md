# FilterIterator removes the wrong element after lookahead

Confirmed 2026-10-24. New relative to the local prior findings; not reported externally.

`FilterIterator.hasNext()` calls `checkNext()`, which consumes the next matching element from the backing iterator. `remove()` unconditionally delegates to that backing iterator. Consequently, lookahead changes which element gets removed.

On a normal JDK ArrayList containing `[a, b, c]`:

1. `filter.next()` returns `a`.
2. `filter.hasNext()` returns true, internally consuming `b`.
3. `filter.remove()` removes `b`, leaving `[a, c]`; it should remove `a`, leaving `[b, c]`.
4. `filter.next()` then returns the already-deleted `b` from its cache.

Also, `hasNext(); remove()` before any wrapper `next()` succeeds, removing `a`, instead of rejecting the call. These are two manifestations of one state-tracking defect, counted as one bug.

The [Java Iterator contract](https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Iterator.html#remove()) defines removal in terms of the last element returned by that iterator and requires an IllegalStateException when next has not been called (unless removal is unsupported).

## Formal evidence

`theories/Camel/NewBugs.v`:

- `filter_remove_wrong_element`: identical legal next/hasNext/remove operations on the finite backing iterator leave `bc` directly and `ac` through the real Camel wrapper.
- `filter_remove_before_next`: the backing iterator rejects remove-before-next (`-1` encodes the caught IllegalStateException); the wrapper accepts it and leaves two entries.

These are kernel-computed executions of real production `FilterIterator.class` plus a small ordinary Iterator test input, `FilterScenario.Backing`. No Camel method is stubbed. HotSpot separately reproduces the defect with the JDK's own ArrayList iterator, and the extracted JVM model agrees on both input-driver cases and controls. The theorem is a concrete counterexample, not a general proof of all iterators or all JVM semantics.

## Scope and provenance

- Compiled unchanged from Camel commit `bd4d2ba20d6a268b66949712d00073069a8e333d`, javac 21.0.11, --release 17 -g.
- Class SHA-256: `1c5f424ddbcd0a59e02824b3f25e7e4329a67bba886f9559f4ccc8c5ef839371`.
- Upstream default-branch source still matches this implementation; retrieved Git blob `2ae47f89992722f855adc256ada717faafa1df0b`.
- No matching local prior finding, or GitHub issue/PR search result for FilterIterator. This is not an exhaustive Jira duplicate search.
- No internal production caller found in the local core/components search. Impact is wrong-element deletion for direct users of this public utility; no route-level reproduction or security impact is claimed.

A safe repair option is to reject remove explicitly with UnsupportedOperationException (the interface permits this), or redesign removal together with lookahead. A simple direct delegation cannot preserve the contract after prefetch.

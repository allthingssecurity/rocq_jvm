/*
 * rocq-jvm model (clean-room, Apache-2.0): the element sources of sequential streams, playing the
 * part of the JDK spliterators (tryAdvance / forEachRemaining / estimateSize / characteristics).
 * Characteristics are reduced to the four that become stream flags: SIZED, ORDERED, DISTINCT and
 * SORTED (SORTED only for a natural ordering). Behaviour follows the Javadoc of the stream
 * factories (Stream.of/iterate/generate/concat, IntStream.range, Collection.stream, ...): late
 * binding of collection sources, lazy evaluation of iterate/generate, concatenation that keeps
 * the first source until it is exhausted.
 */
package java.util.stream;

import java.util.Collection;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.function.IntPredicate;
import java.util.function.IntSupplier;
import java.util.function.IntUnaryOperator;
import java.util.function.LongPredicate;
import java.util.function.LongSupplier;
import java.util.function.LongUnaryOperator;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;

abstract class Src {
    static final int SIZED = 1, ORDERED = 2, DISTINCT = 4, SORTED = 8;

    abstract boolean tryAdvance(Sink c);

    void forEachRemaining(Sink c) {
        do {
        } while (tryAdvance(c));
    }

    abstract long estimateSize();

    abstract int characteristics();

    /** Spliterator.getExactSizeIfKnown. */
    long exactSize() {
        return (characteristics() & SIZED) == 0 ? -1L : estimateSize();
    }

    // ---- arrays: Stream.of(T...), Arrays.stream, built streams (ORDERED | SIZED) ----

    static final class Arr extends Src {
        final Object[] a;
        int index;
        final int fence;

        Arr(Object[] a, int from, int to) {
            this.a = a;
            this.index = from;
            this.fence = to;
        }

        boolean tryAdvance(Sink c) {
            if (index >= 0 && index < fence) {
                Object e = a[index++];
                c.accept(e);
                return true;
            }
            return false;
        }

        void forEachRemaining(Sink c) {
            int i = index, hi = fence;
            if (a.length >= hi && i >= 0 && i < (index = hi)) {
                do {
                    c.accept(a[i]);
                } while (++i < hi);
            }
        }

        long estimateSize() {
            return (long) (fence - index);
        }

        int characteristics() {
            return SIZED | ORDERED;
        }
    }

    static final class IntArr extends Src {
        final int[] a;
        int index;
        final int fence;

        IntArr(int[] a, int from, int to) {
            this.a = a;
            this.index = from;
            this.fence = to;
        }

        boolean tryAdvance(Sink c) {
            if (index >= 0 && index < fence) {
                c.accept(a[index++]);
                return true;
            }
            return false;
        }

        void forEachRemaining(Sink c) {
            int i = index, hi = fence;
            if (a.length >= hi && i >= 0 && i < (index = hi)) {
                do {
                    c.accept(a[i]);
                } while (++i < hi);
            }
        }

        long estimateSize() {
            return (long) (fence - index);
        }

        int characteristics() {
            return SIZED | ORDERED;
        }
    }

    static final class LongArr extends Src {
        final long[] a;
        int index;
        final int fence;

        LongArr(long[] a, int from, int to) {
            this.a = a;
            this.index = from;
            this.fence = to;
        }

        boolean tryAdvance(Sink c) {
            if (index >= 0 && index < fence) {
                c.accept(a[index++]);
                return true;
            }
            return false;
        }

        void forEachRemaining(Sink c) {
            int i = index, hi = fence;
            if (a.length >= hi && i >= 0 && i < (index = hi)) {
                do {
                    c.accept(a[i]);
                } while (++i < hi);
            }
        }

        long estimateSize() {
            return (long) (fence - index);
        }

        int characteristics() {
            return SIZED | ORDERED;
        }
    }

    /** A built stream of at most one element (Stream.of(t), builders with fewer than 2 elements). */
    static final class One extends Src {
        final Object first;
        int count; // -2: the element is pending, -1: done

        One(Object first, boolean present) {
            this.first = first;
            this.count = present ? -2 : -1;
        }

        boolean tryAdvance(Sink c) {
            if (count == -2) {
                c.accept(first);
                count = -1;
                return true;
            }
            return false;
        }

        void forEachRemaining(Sink c) {
            if (count == -2) {
                c.accept(first);
                count = -1;
            }
        }

        long estimateSize() {
            return -count - 1;
        }

        int characteristics() {
            return SIZED | ORDERED;
        }
    }

    /** Stream.empty(), IntStream.empty(), ...: SIZED only (not ORDERED). */
    static final class Empty extends Src {
        boolean tryAdvance(Sink c) {
            return false;
        }

        void forEachRemaining(Sink c) {
        }

        long estimateSize() {
            return 0;
        }

        int characteristics() {
            return SIZED;
        }
    }

    // ---- iterate / generate (estimate Long.MAX_VALUE, not SIZED) ----

    static final class Iterate extends Src {
        final Object seed;
        final UnaryOperator<Object> f;
        Object prev;
        boolean started;

        Iterate(Object seed, UnaryOperator<Object> f) {
            this.seed = seed;
            this.f = f;
        }

        boolean tryAdvance(Sink c) {
            Object t;
            if (started) t = f.apply(prev);
            else {
                t = seed;
                started = true;
            }
            c.accept(prev = t);
            return true;
        }

        long estimateSize() {
            return Long.MAX_VALUE;
        }

        int characteristics() {
            return ORDERED;
        }
    }

    static final class Iterate3 extends Src {
        final Object seed;
        final Predicate<Object> hasNext;
        final UnaryOperator<Object> next;
        Object prev;
        boolean started, finished;

        Iterate3(Object seed, Predicate<Object> hasNext, UnaryOperator<Object> next) {
            this.seed = seed;
            this.hasNext = hasNext;
            this.next = next;
        }

        boolean tryAdvance(Sink c) {
            if (finished) return false;
            Object t;
            if (started) t = next.apply(prev);
            else {
                t = seed;
                started = true;
            }
            if (!hasNext.test(t)) {
                prev = null;
                finished = true;
                return false;
            }
            c.accept(prev = t);
            return true;
        }

        void forEachRemaining(Sink c) {
            if (finished) return;
            finished = true;
            Object t = started ? next.apply(prev) : seed;
            prev = null;
            while (hasNext.test(t)) {
                c.accept(t);
                t = next.apply(t);
            }
        }

        long estimateSize() {
            return Long.MAX_VALUE;
        }

        int characteristics() {
            return ORDERED;
        }
    }

    static final class IntIterate extends Src {
        final int seed;
        final IntUnaryOperator f;
        final IntPredicate hasNext; // null: infinite
        int prev;
        boolean started, finished;

        IntIterate(int seed, IntPredicate hasNext, IntUnaryOperator f) {
            this.seed = seed;
            this.f = f;
            this.hasNext = hasNext;
        }

        boolean tryAdvance(Sink c) {
            if (hasNext == null) {
                int t;
                if (started) t = f.applyAsInt(prev);
                else {
                    t = seed;
                    started = true;
                }
                c.accept(prev = t);
                return true;
            }
            if (finished) return false;
            int t;
            if (started) t = f.applyAsInt(prev);
            else {
                t = seed;
                started = true;
            }
            if (!hasNext.test(t)) {
                finished = true;
                return false;
            }
            c.accept(prev = t);
            return true;
        }

        void forEachRemaining(Sink c) {
            if (hasNext == null) {
                super.forEachRemaining(c);
                return;
            }
            if (finished) return;
            finished = true;
            int t = started ? f.applyAsInt(prev) : seed;
            while (hasNext.test(t)) {
                c.accept(t);
                t = f.applyAsInt(t);
            }
        }

        long estimateSize() {
            return Long.MAX_VALUE;
        }

        int characteristics() {
            return ORDERED;
        }
    }

    static final class LongIterate extends Src {
        final long seed;
        final LongUnaryOperator f;
        final LongPredicate hasNext; // null: infinite
        long prev;
        boolean started, finished;

        LongIterate(long seed, LongPredicate hasNext, LongUnaryOperator f) {
            this.seed = seed;
            this.f = f;
            this.hasNext = hasNext;
        }

        boolean tryAdvance(Sink c) {
            if (hasNext == null) {
                long t;
                if (started) t = f.applyAsLong(prev);
                else {
                    t = seed;
                    started = true;
                }
                c.accept(prev = t);
                return true;
            }
            if (finished) return false;
            long t;
            if (started) t = f.applyAsLong(prev);
            else {
                t = seed;
                started = true;
            }
            if (!hasNext.test(t)) {
                finished = true;
                return false;
            }
            c.accept(prev = t);
            return true;
        }

        void forEachRemaining(Sink c) {
            if (hasNext == null) {
                super.forEachRemaining(c);
                return;
            }
            if (finished) return;
            finished = true;
            long t = started ? f.applyAsLong(prev) : seed;
            while (hasNext.test(t)) {
                c.accept(t);
                t = f.applyAsLong(t);
            }
        }

        long estimateSize() {
            return Long.MAX_VALUE;
        }

        int characteristics() {
            return ORDERED;
        }
    }

    /** generate: an infinite unordered source. */
    static final class Generate extends Src {
        final Supplier<?> s;
        final IntSupplier si;
        final LongSupplier sl;

        Generate(Supplier<?> s, IntSupplier si, LongSupplier sl) {
            this.s = s;
            this.si = si;
            this.sl = sl;
        }

        boolean tryAdvance(Sink c) {
            if (s != null) c.accept(s.get());
            else if (si != null) c.accept(si.getAsInt());
            else c.accept(sl.getAsLong());
            return true;
        }

        long estimateSize() {
            return Long.MAX_VALUE;
        }

        int characteristics() {
            return 0;
        }
    }

    // ---- ranges (ORDERED | SIZED | DISTINCT | SORTED) ----

    static final class IntRange extends Src {
        int from;
        final int upTo;
        int last;

        IntRange(int from, int upTo, boolean closed) {
            this.from = from;
            this.upTo = upTo;
            this.last = closed ? 1 : 0;
        }

        boolean tryAdvance(Sink c) {
            int i = from;
            if (i < upTo) {
                from++;
                c.accept(i);
                return true;
            } else if (last > 0) {
                last = 0;
                c.accept(i);
                return true;
            }
            return false;
        }

        void forEachRemaining(Sink c) {
            int i = from;
            int hUpTo = upTo;
            int hLast = last;
            from = upTo;
            last = 0;
            while (i < hUpTo) c.accept(i++);
            if (hLast > 0) c.accept(i);
        }

        long estimateSize() {
            return ((long) upTo) - from + last;
        }

        int characteristics() {
            return SIZED | ORDERED | DISTINCT | SORTED;
        }
    }

    static final class LongRange extends Src {
        long from;
        final long upTo;
        int last;

        LongRange(long from, long upTo, boolean closed) {
            this.from = from;
            this.upTo = upTo;
            this.last = closed ? 1 : 0;
        }

        boolean tryAdvance(Sink c) {
            long i = from;
            if (i < upTo) {
                from++;
                c.accept(i);
                return true;
            } else if (last > 0) {
                last = 0;
                c.accept(i);
                return true;
            }
            return false;
        }

        void forEachRemaining(Sink c) {
            long i = from;
            long hUpTo = upTo;
            int hLast = last;
            from = upTo;
            last = 0;
            while (i < hUpTo) c.accept(i++);
            if (hLast > 0) c.accept(i);
        }

        long estimateSize() {
            return upTo - from + last;
        }

        int characteristics() {
            return SIZED | ORDERED | DISTINCT | SORTED;
        }
    }

    // ---- concat: the first source until it is exhausted, then the second ----

    static final class Concat extends Src {
        final Src a, b;
        boolean beforeSplit = true;
        final boolean unsized;

        Concat(Src a, Src b) {
            this.a = a;
            this.b = b;
            unsized = a.estimateSize() + b.estimateSize() < 0;
        }

        boolean tryAdvance(Sink c) {
            boolean hasNext;
            if (beforeSplit) {
                hasNext = a.tryAdvance(c);
                if (!hasNext) {
                    beforeSplit = false;
                    hasNext = b.tryAdvance(c);
                }
            } else hasNext = b.tryAdvance(c);
            return hasNext;
        }

        void forEachRemaining(Sink c) {
            if (beforeSplit) a.forEachRemaining(c);
            b.forEachRemaining(c);
        }

        long estimateSize() {
            if (beforeSplit) {
                long size = a.estimateSize() + b.estimateSize();
                return (size >= 0) ? size : Long.MAX_VALUE;
            }
            return b.estimateSize();
        }

        int characteristics() {
            if (beforeSplit) {
                return a.characteristics() & b.characteristics() & ~(DISTINCT | SORTED | (unsized ? SIZED : 0));
            }
            return b.characteristics();
        }
    }

    // ---- collections (Collection.stream) ----

    /**
     * A collection traversed with its iterator, bound (iterator created, size read) at the first
     * use, as the JDK's late-binding spliterators are. ITER: the JDK spliterator of this collection
     * is iterator based too, so the traversal is exact even when the collection is modified.
     * GUARD: the JDK spliterator works on the internal structure (fail-fast at the end of
     * forEachRemaining or after each tryAdvance); a modification during the traversal is detected
     * (iterator CME, size change, modCount change when known) and is STUCK.
     */
    static final class Coll extends Src {
        static final int ITER = 0, GUARD = 1;
        final Collection<?> c;
        final int chars;
        final int kind;
        final IntSupplier mod;
        Iterator<?> it;
        long est;
        int expMod;

        Coll(Collection<?> c, int chars, int kind, IntSupplier mod) {
            this.c = c;
            this.chars = chars;
            this.kind = kind;
            this.mod = mod;
        }

        private void bind() {
            if (it == null) {
                it = c.iterator();
                est = (long) c.size();
                if (mod != null) expMod = mod.getAsInt();
            }
        }

        private Object nextGuarded() {
            try {
                return it.next();
            } catch (ConcurrentModificationException e) {
                throw ModelStuckS.unsupported("collection modified during a stream traversal");
            }
        }

        private void check() {
            if ((long) c.size() != est || (mod != null && mod.getAsInt() != expMod))
                throw ModelStuckS.unsupported("collection modified during a stream traversal");
        }

        boolean tryAdvance(Sink s) {
            bind();
            if (kind == ITER) {
                if (it.hasNext()) {
                    s.accept(it.next());
                    return true;
                }
                return false;
            }
            check();
            if (!it.hasNext()) return false;
            Object e = nextGuarded();
            s.accept(e);
            check();
            return true;
        }

        @SuppressWarnings("unchecked")
        void forEachRemaining(Sink s) {
            bind();
            if (kind == ITER) {
                ((Iterator<Object>) it).forEachRemaining(s);
                return;
            }
            check();
            while (it.hasNext()) {
                Object e = nextGuarded();
                s.accept(e);
                check();
            }
        }

        long estimateSize() {
            bind();
            return est;
        }

        int characteristics() {
            return chars;
        }
    }
}

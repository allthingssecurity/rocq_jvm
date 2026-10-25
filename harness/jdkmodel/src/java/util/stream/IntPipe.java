/*
 * rocq-jvm model (clean-room, Apache-2.0): the IntStream implementation of the model (a stage of
 * a sequential pipeline whose elements travel as Integer boxes). distinct() is boxed().distinct()
 * .mapToInt(..) as the JDK documents it; DoubleStream conversions, iterator() (PrimitiveIterator),
 * spliterator(), summaryStatistics() and parallel() are STUCK.
 */
package java.util.stream;

import java.util.IntSummaryStatistics;
import java.util.OptionalDouble;
import java.util.OptionalInt;
import java.util.PrimitiveIterator;
import java.util.Spliterator;
import java.util.function.BiConsumer;
import java.util.function.IntBinaryOperator;
import java.util.function.IntConsumer;
import java.util.function.IntFunction;
import java.util.function.IntPredicate;
import java.util.function.IntToDoubleFunction;
import java.util.function.IntToLongFunction;
import java.util.function.IntUnaryOperator;
import java.util.function.ObjIntConsumer;
import java.util.function.Supplier;

final class IntPipe extends Pipe implements IntStream {
    IntPipe(Src s) {
        super(s);
    }

    IntPipe(Pipe up, Op op) {
        super(up, op);
    }

    private static <X> X req(X x) {
        if (x == null) throw new NullPointerException();
        return x;
    }

    static int v(Object o) {
        return ((Integer) o).intValue();
    }

    static Integer box(int x) {
        return Integer.valueOf(x);
    }

    // ---- BaseStream ----

    public PrimitiveIterator.OfInt iterator() {
        throw ModelStuckS.unsupported("IntStream.iterator (PrimitiveIterator)");
    }

    public Spliterator.OfInt spliterator() {
        throw ModelStuckS.unsupported("IntStream.spliterator");
    }

    public boolean isParallel() {
        return false;
    }

    public IntStream sequential() {
        return this;
    }

    public IntStream parallel() {
        throw ModelStuckS.unsupported("parallel streams");
    }

    public IntStream unordered() {
        if (!isOrdered()) return this;
        return new IntPipe(this, unorderedOp());
    }

    public IntStream onClose(Runnable closeHandler) {
        onCloseInternal(closeHandler);
        return this;
    }

    public void close() {
        closeInternal();
    }

    // ---- intermediate ops ----

    public IntStream filter(IntPredicate predicate) {
        req(predicate);
        return new IntPipe(this, filterOp(o -> predicate.test(v(o))));
    }

    public IntStream map(IntUnaryOperator mapper) {
        req(mapper);
        return new IntPipe(this, mapOp(o -> box(mapper.applyAsInt(v(o))), SORTED | DISTINCT));
    }

    public <U> Stream<U> mapToObj(IntFunction<? extends U> mapper) {
        req(mapper);
        return new RefPipe<U>(this, mapOp(o -> mapper.apply(v(o)), SORTED | DISTINCT));
    }

    public LongStream mapToLong(IntToLongFunction mapper) {
        req(mapper);
        return new LongPipe(this, mapOp(o -> Long.valueOf(mapper.applyAsLong(v(o))), SORTED | DISTINCT));
    }

    public DoubleStream mapToDouble(IntToDoubleFunction mapper) {
        throw ModelStuckS.unsupported("DoubleStream");
    }

    public IntStream flatMap(IntFunction<? extends IntStream> mapper) {
        req(mapper);
        return new IntPipe(this, flatMapOp(o -> mapper.apply(v(o)), 1));
    }

    public IntStream mapMulti(IntMapMultiConsumer mapper) {
        req(mapper);
        return new IntPipe(this, mapMultiOp((o, sink) -> mapper.accept(v(o), sink)));
    }

    public IntStream distinct() {
        return boxed().distinct().mapToInt(i -> i);
    }

    public IntStream sorted() {
        return new IntPipe(this, sortedOp(null, true));
    }

    public IntStream peek(IntConsumer action) {
        req(action);
        return new IntPipe(this, peekOp(o -> action.accept(v(o))));
    }

    public IntStream limit(long maxSize) {
        if (maxSize < 0) throw new IllegalArgumentException(Long.toString(maxSize));
        return new IntPipe(this, sliceOp(0, maxSize));
    }

    public IntStream skip(long n) {
        if (n < 0) throw new IllegalArgumentException(Long.toString(n));
        if (n == 0) return this;
        return new IntPipe(this, sliceOp(n, -1));
    }

    public IntStream takeWhile(IntPredicate predicate) {
        req(predicate);
        return new IntPipe(this, takeWhileOp(o -> predicate.test(v(o))));
    }

    public IntStream dropWhile(IntPredicate predicate) {
        req(predicate);
        return new IntPipe(this, dropWhileOp(o -> predicate.test(v(o))));
    }

    public LongStream asLongStream() {
        return new LongPipe(this, mapOp(o -> Long.valueOf((long) v(o)), 0));
    }

    public DoubleStream asDoubleStream() {
        throw ModelStuckS.unsupported("DoubleStream");
    }

    public Stream<Integer> boxed() {
        return new RefPipe<Integer>(this, mapOp(o -> o, 0));
    }

    // ---- terminal ops ----

    public void forEach(IntConsumer action) {
        req(action);
        forEachT(o -> action.accept(v(o)), false);
    }

    public void forEachOrdered(IntConsumer action) {
        req(action);
        forEachT(o -> action.accept(v(o)), true);
    }

    public int[] toArray() {
        Object[] r = toObjectArrayT();
        int[] a = new int[r.length];
        for (int i = 0; i < r.length; i++) a[i] = v(r[i]);
        return a;
    }

    public int reduce(int identity, IntBinaryOperator op) {
        req(op);
        return v(reduceT(box(identity), (a, b) -> box(op.applyAsInt(v(a), v(b)))));
    }

    public OptionalInt reduce(IntBinaryOperator op) {
        req(op);
        Object[] r = reduceOptT((a, b) -> box(op.applyAsInt(v(a), v(b))));
        return r == null ? OptionalInt.empty() : OptionalInt.of(v(r[0]));
    }

    public <R> R collect(Supplier<R> supplier, ObjIntConsumer<R> accumulator, BiConsumer<R, R> combiner) {
        req(combiner);
        req(supplier);
        req(accumulator);
        @SuppressWarnings("unchecked")
        R r = (R) collectT(supplier, (st, o) -> {
            @SuppressWarnings("unchecked")
            R state = (R) st;
            accumulator.accept(state, v(o));
        }, 0);
        return r;
    }

    public int sum() {
        return reduce(0, (a, b) -> a + b);
    }

    public OptionalInt min() {
        return reduce((a, b) -> Math.min(a, b));
    }

    public OptionalInt max() {
        return reduce((a, b) -> Math.max(a, b));
    }

    public long count() {
        return countT();
    }

    public OptionalDouble average() {
        long[] avg = collect(() -> new long[2],
                             (ll, i) -> {
                                 ll[0]++;
                                 ll[1] += i;
                             },
                             (ll, rr) -> {
                                 ll[0] += rr[0];
                                 ll[1] += rr[1];
                             });
        return avg[0] > 0 ? OptionalDouble.of((double) avg[1] / avg[0]) : OptionalDouble.empty();
    }

    public IntSummaryStatistics summaryStatistics() {
        throw ModelStuckS.unsupported("IntStream.summaryStatistics (IntSummaryStatistics)");
    }

    public boolean anyMatch(IntPredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 0);
    }

    public boolean allMatch(IntPredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 1);
    }

    public boolean noneMatch(IntPredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 2);
    }

    public OptionalInt findFirst() {
        Object[] r = findT(true);
        return r == null ? OptionalInt.empty() : OptionalInt.of(v(r[0]));
    }

    public OptionalInt findAny() {
        Object[] r = findT(false);
        return r == null ? OptionalInt.empty() : OptionalInt.of(v(r[0]));
    }

    // ---- IntStream.builder() ----

    static final class BuilderImpl implements IntStream.Builder {
        int count;
        int first;
        int[] buffer;

        public void accept(int t) {
            if (count == 0) {
                first = t;
                count++;
            } else if (count > 0) {
                if (buffer == null) {
                    buffer = new int[8];
                    buffer[0] = first;
                }
                if (count == buffer.length) buffer = copyOf(buffer, count * 2);
                buffer[count++] = t;
            } else {
                throw new IllegalStateException();
            }
        }

        public IntStream.Builder add(int t) {
            accept(t);
            return this;
        }

        public IntStream build() {
            int c = count;
            if (c >= 0) {
                count = -count - 1;
                if (c < 2) return new IntPipe(new Src.One(box(first), c == 1));
                return new IntPipe(new Src.IntArr(buffer, 0, c));
            }
            throw new IllegalStateException();
        }
    }
}

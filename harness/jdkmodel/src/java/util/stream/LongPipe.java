/*
 * rocq-jvm model (clean-room, Apache-2.0): the LongStream implementation of the model (a stage of
 * a sequential pipeline whose elements travel as Long boxes). distinct() is boxed().distinct()
 * .mapToLong(..) as the JDK documents it; DoubleStream conversions, iterator() (PrimitiveIterator),
 * spliterator(), summaryStatistics() and parallel() are STUCK.
 */
package java.util.stream;

import java.util.LongSummaryStatistics;
import java.util.OptionalDouble;
import java.util.OptionalLong;
import java.util.PrimitiveIterator;
import java.util.Spliterator;
import java.util.function.BiConsumer;
import java.util.function.LongBinaryOperator;
import java.util.function.LongConsumer;
import java.util.function.LongFunction;
import java.util.function.LongPredicate;
import java.util.function.LongToDoubleFunction;
import java.util.function.LongToIntFunction;
import java.util.function.LongUnaryOperator;
import java.util.function.ObjLongConsumer;
import java.util.function.Supplier;

final class LongPipe extends Pipe implements LongStream {
    LongPipe(Src s) {
        super(s);
    }

    LongPipe(Pipe up, Op op) {
        super(up, op);
    }

    private static <X> X req(X x) {
        if (x == null) throw new NullPointerException();
        return x;
    }

    static long v(Object o) {
        return ((Long) o).longValue();
    }

    static Long box(long x) {
        return Long.valueOf(x);
    }

    // ---- BaseStream ----

    public PrimitiveIterator.OfLong iterator() {
        throw ModelStuckS.unsupported("LongStream.iterator (PrimitiveIterator)");
    }

    public Spliterator.OfLong spliterator() {
        throw ModelStuckS.unsupported("LongStream.spliterator");
    }

    public boolean isParallel() {
        return false;
    }

    public LongStream sequential() {
        return this;
    }

    public LongStream parallel() {
        throw ModelStuckS.unsupported("parallel streams");
    }

    public LongStream unordered() {
        if (!isOrdered()) return this;
        return new LongPipe(this, unorderedOp());
    }

    public LongStream onClose(Runnable closeHandler) {
        onCloseInternal(closeHandler);
        return this;
    }

    public void close() {
        closeInternal();
    }

    // ---- intermediate ops ----

    public LongStream filter(LongPredicate predicate) {
        req(predicate);
        return new LongPipe(this, filterOp(o -> predicate.test(v(o))));
    }

    public LongStream map(LongUnaryOperator mapper) {
        req(mapper);
        return new LongPipe(this, mapOp(o -> box(mapper.applyAsLong(v(o))), SORTED | DISTINCT));
    }

    public <U> Stream<U> mapToObj(LongFunction<? extends U> mapper) {
        req(mapper);
        return new RefPipe<U>(this, mapOp(o -> mapper.apply(v(o)), SORTED | DISTINCT));
    }

    public IntStream mapToInt(LongToIntFunction mapper) {
        req(mapper);
        return new IntPipe(this, mapOp(o -> Integer.valueOf(mapper.applyAsInt(v(o))), SORTED | DISTINCT));
    }

    public DoubleStream mapToDouble(LongToDoubleFunction mapper) {
        throw ModelStuckS.unsupported("DoubleStream");
    }

    public LongStream flatMap(LongFunction<? extends LongStream> mapper) {
        req(mapper);
        return new LongPipe(this, flatMapOp(o -> mapper.apply(v(o)), 2));
    }

    public LongStream mapMulti(LongMapMultiConsumer mapper) {
        req(mapper);
        return new LongPipe(this, mapMultiOp((o, sink) -> mapper.accept(v(o), sink)));
    }

    public LongStream distinct() {
        return boxed().distinct().mapToLong(i -> i);
    }

    public LongStream sorted() {
        return new LongPipe(this, sortedOp(null, true));
    }

    public LongStream peek(LongConsumer action) {
        req(action);
        return new LongPipe(this, peekOp(o -> action.accept(v(o))));
    }

    public LongStream limit(long maxSize) {
        if (maxSize < 0) throw new IllegalArgumentException(Long.toString(maxSize));
        return new LongPipe(this, sliceOp(0, maxSize));
    }

    public LongStream skip(long n) {
        if (n < 0) throw new IllegalArgumentException(Long.toString(n));
        if (n == 0) return this;
        return new LongPipe(this, sliceOp(n, -1));
    }

    public LongStream takeWhile(LongPredicate predicate) {
        req(predicate);
        return new LongPipe(this, takeWhileOp(o -> predicate.test(v(o))));
    }

    public LongStream dropWhile(LongPredicate predicate) {
        req(predicate);
        return new LongPipe(this, dropWhileOp(o -> predicate.test(v(o))));
    }

    public DoubleStream asDoubleStream() {
        throw ModelStuckS.unsupported("DoubleStream");
    }

    public Stream<Long> boxed() {
        return new RefPipe<Long>(this, mapOp(o -> o, 0));
    }

    // ---- terminal ops ----

    public void forEach(LongConsumer action) {
        req(action);
        forEachT(o -> action.accept(v(o)), false);
    }

    public void forEachOrdered(LongConsumer action) {
        req(action);
        forEachT(o -> action.accept(v(o)), true);
    }

    public long[] toArray() {
        Object[] r = toObjectArrayT();
        long[] a = new long[r.length];
        for (int i = 0; i < r.length; i++) a[i] = v(r[i]);
        return a;
    }

    public long reduce(long identity, LongBinaryOperator op) {
        req(op);
        return v(reduceT(box(identity), (a, b) -> box(op.applyAsLong(v(a), v(b)))));
    }

    public OptionalLong reduce(LongBinaryOperator op) {
        req(op);
        Object[] r = reduceOptT((a, b) -> box(op.applyAsLong(v(a), v(b))));
        return r == null ? OptionalLong.empty() : OptionalLong.of(v(r[0]));
    }

    public <R> R collect(Supplier<R> supplier, ObjLongConsumer<R> accumulator, BiConsumer<R, R> combiner) {
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

    public long sum() {
        return reduce(0, (a, b) -> a + b);
    }

    public OptionalLong min() {
        return reduce((a, b) -> Math.min(a, b));
    }

    public OptionalLong max() {
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

    public LongSummaryStatistics summaryStatistics() {
        throw ModelStuckS.unsupported("LongStream.summaryStatistics (LongSummaryStatistics)");
    }

    public boolean anyMatch(LongPredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 0);
    }

    public boolean allMatch(LongPredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 1);
    }

    public boolean noneMatch(LongPredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 2);
    }

    public OptionalLong findFirst() {
        Object[] r = findT(true);
        return r == null ? OptionalLong.empty() : OptionalLong.of(v(r[0]));
    }

    public OptionalLong findAny() {
        Object[] r = findT(false);
        return r == null ? OptionalLong.empty() : OptionalLong.of(v(r[0]));
    }

    // ---- LongStream.builder() ----

    static final class BuilderImpl implements LongStream.Builder {
        int count;
        long first;
        long[] buffer;

        public void accept(long t) {
            if (count == 0) {
                first = t;
                count++;
            } else if (count > 0) {
                if (buffer == null) {
                    buffer = new long[8];
                    buffer[0] = first;
                }
                if (count == buffer.length) buffer = copyOf(buffer, count * 2);
                buffer[count++] = t;
            } else {
                throw new IllegalStateException();
            }
        }

        public LongStream.Builder add(long t) {
            accept(t);
            return this;
        }

        public LongStream build() {
            int c = count;
            if (c >= 0) {
                count = -count - 1;
                if (c < 2) return new LongPipe(new Src.One(box(first), c == 1));
                return new LongPipe(new Src.LongArr(buffer, 0, c));
            }
            throw new IllegalStateException();
        }
    }
}

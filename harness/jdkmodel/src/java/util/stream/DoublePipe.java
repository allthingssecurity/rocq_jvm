/*
 * rocq-jvm model (clean-room, Apache-2.0): the DoubleStream implementation of the model (a stage of
 * a sequential pipeline whose elements travel as Double boxes). distinct() is boxed().distinct()
 * .mapToDouble(..) as the JDK documents it; sorted() orders as Double.compare (-0.0 before 0.0, NaN
 * last); sum(), average() and summaryStatistics() use the JDK's compensated summation (with the
 * simple sum for same-signed infinities); min/max reduce with Math.min/max. iterator()
 * (PrimitiveIterator), spliterator() and parallel() are STUCK.
 */
package java.util.stream;

import java.util.DoubleSummaryStatistics;
import java.util.OptionalDouble;
import java.util.PrimitiveIterator;
import java.util.Spliterator;
import java.util.function.BiConsumer;
import java.util.function.DoubleBinaryOperator;
import java.util.function.DoubleConsumer;
import java.util.function.DoubleFunction;
import java.util.function.DoublePredicate;
import java.util.function.DoubleToIntFunction;
import java.util.function.DoubleToLongFunction;
import java.util.function.DoubleUnaryOperator;
import java.util.function.ObjDoubleConsumer;
import java.util.function.Supplier;

final class DoublePipe extends Pipe implements DoubleStream {
    DoublePipe(Src s) {
        super(s);
    }

    DoublePipe(Pipe up, Op op) {
        super(up, op);
    }

    private static <X> X req(X x) {
        if (x == null) throw new NullPointerException();
        return x;
    }

    static double v(Object o) {
        return ((Double) o).doubleValue();
    }

    static Double box(double x) {
        return Double.valueOf(x);
    }

    // ---- BaseStream ----

    public PrimitiveIterator.OfDouble iterator() {
        throw ModelStuckS.unsupported("DoubleStream.iterator (PrimitiveIterator)");
    }

    public Spliterator.OfDouble spliterator() {
        throw ModelStuckS.unsupported("DoubleStream.spliterator");
    }

    public boolean isParallel() {
        return false;
    }

    public DoubleStream sequential() {
        return this;
    }

    public DoubleStream parallel() {
        throw ModelStuckS.unsupported("parallel streams");
    }

    public DoubleStream unordered() {
        if (!isOrdered()) return this;
        return new DoublePipe(this, unorderedOp());
    }

    public DoubleStream onClose(Runnable closeHandler) {
        onCloseInternal(closeHandler);
        return this;
    }

    public void close() {
        closeInternal();
    }

    // ---- intermediate ops ----

    public DoubleStream filter(DoublePredicate predicate) {
        req(predicate);
        return new DoublePipe(this, filterOp(o -> predicate.test(v(o))));
    }

    public DoubleStream map(DoubleUnaryOperator mapper) {
        req(mapper);
        return new DoublePipe(this, mapOp(o -> box(mapper.applyAsDouble(v(o))), SORTED | DISTINCT));
    }

    public <U> Stream<U> mapToObj(DoubleFunction<? extends U> mapper) {
        req(mapper);
        return new RefPipe<U>(this, mapOp(o -> mapper.apply(v(o)), SORTED | DISTINCT));
    }

    public IntStream mapToInt(DoubleToIntFunction mapper) {
        req(mapper);
        return new IntPipe(this, mapOp(o -> Integer.valueOf(mapper.applyAsInt(v(o))), SORTED | DISTINCT));
    }

    public LongStream mapToLong(DoubleToLongFunction mapper) {
        req(mapper);
        return new LongPipe(this, mapOp(o -> Long.valueOf(mapper.applyAsLong(v(o))), SORTED | DISTINCT));
    }

    public DoubleStream flatMap(DoubleFunction<? extends DoubleStream> mapper) {
        req(mapper);
        return new DoublePipe(this, flatMapOp(o -> mapper.apply(v(o)), 3));
    }

    public DoubleStream mapMulti(DoubleMapMultiConsumer mapper) {
        req(mapper);
        return new DoublePipe(this, mapMultiOp((o, sink) -> mapper.accept(v(o), sink)));
    }

    public DoubleStream distinct() {
        return boxed().distinct().mapToDouble(d -> d);
    }

    public DoubleStream sorted() {
        return new DoublePipe(this, sortedOp(null, true));
    }

    public DoubleStream peek(DoubleConsumer action) {
        req(action);
        return new DoublePipe(this, peekOp(o -> action.accept(v(o))));
    }

    public DoubleStream limit(long maxSize) {
        if (maxSize < 0) throw new IllegalArgumentException(Long.toString(maxSize));
        return new DoublePipe(this, sliceOp(0, maxSize));
    }

    public DoubleStream skip(long n) {
        if (n < 0) throw new IllegalArgumentException(Long.toString(n));
        if (n == 0) return this;
        return new DoublePipe(this, sliceOp(n, -1));
    }

    public DoubleStream takeWhile(DoublePredicate predicate) {
        req(predicate);
        return new DoublePipe(this, takeWhileOp(o -> predicate.test(v(o))));
    }

    public DoubleStream dropWhile(DoublePredicate predicate) {
        req(predicate);
        return new DoublePipe(this, dropWhileOp(o -> predicate.test(v(o))));
    }

    public Stream<Double> boxed() {
        return new RefPipe<Double>(this, mapOp(o -> o, 0));
    }

    // ---- terminal ops ----

    public void forEach(DoubleConsumer action) {
        req(action);
        forEachT(o -> action.accept(v(o)), false);
    }

    public void forEachOrdered(DoubleConsumer action) {
        req(action);
        forEachT(o -> action.accept(v(o)), true);
    }

    public double[] toArray() {
        Object[] r = toObjectArrayT();
        double[] a = new double[r.length];
        for (int i = 0; i < r.length; i++) a[i] = v(r[i]);
        return a;
    }

    public double reduce(double identity, DoubleBinaryOperator op) {
        req(op);
        return v(reduceT(box(identity), (a, b) -> box(op.applyAsDouble(v(a), v(b)))));
    }

    public OptionalDouble reduce(DoubleBinaryOperator op) {
        req(op);
        Object[] r = reduceOptT((a, b) -> box(op.applyAsDouble(v(a), v(b))));
        return r == null ? OptionalDouble.empty() : OptionalDouble.of(v(r[0]));
    }

    public <R> R collect(Supplier<R> supplier, ObjDoubleConsumer<R> accumulator, BiConsumer<R, R> combiner) {
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

    /** Collectors.sumWithCompensation: s[0] high-order sum, s[1] negated low-order bits. */
    static void sumWithCompensation(double[] s, double value) {
        double t = value - s[1];
        double sum = s[0];
        double v = sum + t;
        s[1] = (v - sum) - t;
        s[0] = v;
    }

    /** Collectors.computeFinalSum: the simple sum (last slot) when the compensated one is NaN. */
    static double computeFinalSum(double[] s) {
        double t = s[0] - s[1];
        double simple = s[s.length - 1];
        return (Double.isNaN(t) && Double.isInfinite(simple)) ? simple : t;
    }

    public double sum() {
        double[] summation = collect(() -> new double[3],
                                     (ll, d) -> {
                                         sumWithCompensation(ll, d);
                                         ll[2] += d;
                                     },
                                     (ll, rr) -> {
                                         sumWithCompensation(ll, rr[0]);
                                         sumWithCompensation(ll, -rr[1]);
                                         ll[2] += rr[2];
                                     });
        return computeFinalSum(summation);
    }

    public OptionalDouble min() {
        return reduce(Math::min);
    }

    public OptionalDouble max() {
        return reduce(Math::max);
    }

    public long count() {
        return countT();
    }

    public OptionalDouble average() {
        double[] avg = collect(() -> new double[4],
                               (ll, d) -> {
                                   ll[2]++;
                                   sumWithCompensation(ll, d);
                                   ll[3] += d;
                               },
                               (ll, rr) -> {
                                   sumWithCompensation(ll, rr[0]);
                                   sumWithCompensation(ll, -rr[1]);
                                   ll[2] += rr[2];
                                   ll[3] += rr[3];
                               });
        return avg[2] > 0 ? OptionalDouble.of(computeFinalSum(avg) / avg[2]) : OptionalDouble.empty();
    }

    public DoubleSummaryStatistics summaryStatistics() {
        return collect(DoubleSummaryStatistics::new, DoubleSummaryStatistics::accept, DoubleSummaryStatistics::combine);
    }

    public boolean anyMatch(DoublePredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 0);
    }

    public boolean allMatch(DoublePredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 1);
    }

    public boolean noneMatch(DoublePredicate predicate) {
        req(predicate);
        return matchT(o -> predicate.test(v(o)), 2);
    }

    public OptionalDouble findFirst() {
        Object[] r = findT(true);
        return r == null ? OptionalDouble.empty() : OptionalDouble.of(v(r[0]));
    }

    public OptionalDouble findAny() {
        Object[] r = findT(false);
        return r == null ? OptionalDouble.empty() : OptionalDouble.of(v(r[0]));
    }

    // ---- DoubleStream.builder() ----

    static final class BuilderImpl implements DoubleStream.Builder {
        int count;
        double first;
        double[] buffer;

        public void accept(double t) {
            if (count == 0) {
                first = t;
                count++;
            } else if (count > 0) {
                if (buffer == null) {
                    buffer = new double[8];
                    buffer[0] = first;
                }
                if (count == buffer.length) buffer = copyOf(buffer, count * 2);
                buffer[count++] = t;
            } else {
                throw new IllegalStateException();
            }
        }

        public DoubleStream.Builder add(double t) {
            accept(t);
            return this;
        }

        public DoubleStream build() {
            int c = count;
            if (c >= 0) {
                count = -count - 1;
                if (c < 2) return new DoublePipe(new Src.One(box(first), c == 1));
                return new DoublePipe(new Src.DoubleArr(buffer, 0, c));
            }
            throw new IllegalStateException();
        }
    }
}

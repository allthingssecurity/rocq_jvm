/*
 * rocq-jvm model of java.util.stream.DoubleStream (clean-room, Apache-2.0), from the Javadoc. The
 * factories build sequential pipelines of the model (DoublePipe): of/empty/builder are SIZED sources
 * (empty() is not ORDERED), iterate is lazy and ORDERED, generate is unordered. sum(), average()
 * and summaryStatistics() use the JDK's compensated summation. iterator() (PrimitiveIterator),
 * spliterator() and parallel() are STUCK.
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
import java.util.function.DoubleSupplier;
import java.util.function.DoubleToIntFunction;
import java.util.function.DoubleToLongFunction;
import java.util.function.DoubleUnaryOperator;
import java.util.function.ObjDoubleConsumer;
import java.util.function.Supplier;

public interface DoubleStream extends BaseStream<Double, DoubleStream> {
    DoubleStream filter(DoublePredicate predicate);

    DoubleStream map(DoubleUnaryOperator mapper);

    <U> Stream<U> mapToObj(DoubleFunction<? extends U> mapper);

    IntStream mapToInt(DoubleToIntFunction mapper);

    LongStream mapToLong(DoubleToLongFunction mapper);

    DoubleStream flatMap(DoubleFunction<? extends DoubleStream> mapper);

    default DoubleStream mapMulti(DoubleMapMultiConsumer mapper) {
        throw ModelStuckS.unsupported("DoubleStream.mapMulti default method");
    }

    DoubleStream distinct();

    DoubleStream sorted();

    DoubleStream peek(DoubleConsumer action);

    DoubleStream limit(long maxSize);

    DoubleStream skip(long n);

    default DoubleStream takeWhile(DoublePredicate predicate) {
        throw ModelStuckS.unsupported("DoubleStream.takeWhile default method");
    }

    default DoubleStream dropWhile(DoublePredicate predicate) {
        throw ModelStuckS.unsupported("DoubleStream.dropWhile default method");
    }

    void forEach(DoubleConsumer action);

    void forEachOrdered(DoubleConsumer action);

    double[] toArray();

    double reduce(double identity, DoubleBinaryOperator op);

    OptionalDouble reduce(DoubleBinaryOperator op);

    <R> R collect(Supplier<R> supplier, ObjDoubleConsumer<R> accumulator, BiConsumer<R, R> combiner);

    double sum();

    OptionalDouble min();

    OptionalDouble max();

    long count();

    OptionalDouble average();

    DoubleSummaryStatistics summaryStatistics();

    boolean anyMatch(DoublePredicate predicate);

    boolean allMatch(DoublePredicate predicate);

    boolean noneMatch(DoublePredicate predicate);

    OptionalDouble findFirst();

    OptionalDouble findAny();

    Stream<Double> boxed();

    @Override
    DoubleStream sequential();

    @Override
    DoubleStream parallel();

    @Override
    PrimitiveIterator.OfDouble iterator();

    @Override
    Spliterator.OfDouble spliterator();

    // ---- static factories ----

    public static Builder builder() {
        return new DoublePipe.BuilderImpl();
    }

    public static DoubleStream empty() {
        return new DoublePipe(new Src.Empty());
    }

    public static DoubleStream of(double t) {
        return new DoublePipe(new Src.One(Double.valueOf(t), true));
    }

    public static DoubleStream of(double... values) {
        ModelStuckS.nn(values);
        return ModelStreams.ofDoubleArray(values, 0, values.length);
    }

    public static DoubleStream iterate(final double seed, final DoubleUnaryOperator f) {
        if (f == null) throw new NullPointerException();
        return new DoublePipe(new Src.DoubleIterate(seed, null, f));
    }

    public static DoubleStream iterate(double seed, DoublePredicate hasNext, DoubleUnaryOperator next) {
        if (next == null) throw new NullPointerException();
        if (hasNext == null) throw new NullPointerException();
        return new DoublePipe(new Src.DoubleIterate(seed, hasNext, next));
    }

    public static DoubleStream generate(DoubleSupplier s) {
        if (s == null) throw new NullPointerException();
        return new DoublePipe(new Src.Generate(null, null, null, s));
    }

    public static DoubleStream concat(DoubleStream a, DoubleStream b) {
        if (a == null) throw new NullPointerException();
        if (b == null) throw new NullPointerException();
        Src sa = Pipe.srcOf(a);
        Src sb = Pipe.srcOf(b);
        DoubleStream stream = new DoublePipe(new Src.Concat(sa, sb));
        return stream.onClose(Pipe.composedClose(a, b));
    }

    public interface Builder extends DoubleConsumer {
        @Override
        void accept(double t);

        default Builder add(double t) {
            accept(t);
            return this;
        }

        DoubleStream build();
    }

    @FunctionalInterface
    interface DoubleMapMultiConsumer {
        void accept(double value, DoubleConsumer dc);
    }
}

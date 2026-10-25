/*
 * rocq-jvm model of java.util.stream.IntStream (clean-room, Apache-2.0), from the Javadoc. The
 * factories build sequential pipelines of the model (IntPipe): of/empty/builder/range are SIZED
 * sources (range is also ORDERED, DISTINCT and SORTED; empty() is not ORDERED), iterate is lazy and
 * ORDERED, generate is unordered. DoubleStream conversions, iterator() (PrimitiveIterator),
 * spliterator() and summaryStatistics() are STUCK in the model pipeline.
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
import java.util.function.IntSupplier;
import java.util.function.IntToDoubleFunction;
import java.util.function.IntToLongFunction;
import java.util.function.IntUnaryOperator;
import java.util.function.ObjIntConsumer;
import java.util.function.Supplier;

public interface IntStream extends BaseStream<Integer, IntStream> {
    IntStream filter(IntPredicate predicate);

    IntStream map(IntUnaryOperator mapper);

    <U> Stream<U> mapToObj(IntFunction<? extends U> mapper);

    LongStream mapToLong(IntToLongFunction mapper);

    DoubleStream mapToDouble(IntToDoubleFunction mapper);

    IntStream flatMap(IntFunction<? extends IntStream> mapper);

    default IntStream mapMulti(IntMapMultiConsumer mapper) {
        throw ModelStuckS.unsupported("IntStream.mapMulti default method");
    }

    IntStream distinct();

    IntStream sorted();

    IntStream peek(IntConsumer action);

    IntStream limit(long maxSize);

    IntStream skip(long n);

    default IntStream takeWhile(IntPredicate predicate) {
        throw ModelStuckS.unsupported("IntStream.takeWhile default method");
    }

    default IntStream dropWhile(IntPredicate predicate) {
        throw ModelStuckS.unsupported("IntStream.dropWhile default method");
    }

    void forEach(IntConsumer action);

    void forEachOrdered(IntConsumer action);

    int[] toArray();

    int reduce(int identity, IntBinaryOperator op);

    OptionalInt reduce(IntBinaryOperator op);

    <R> R collect(Supplier<R> supplier, ObjIntConsumer<R> accumulator, BiConsumer<R, R> combiner);

    int sum();

    OptionalInt min();

    OptionalInt max();

    long count();

    OptionalDouble average();

    IntSummaryStatistics summaryStatistics();

    boolean anyMatch(IntPredicate predicate);

    boolean allMatch(IntPredicate predicate);

    boolean noneMatch(IntPredicate predicate);

    OptionalInt findFirst();

    OptionalInt findAny();

    LongStream asLongStream();

    DoubleStream asDoubleStream();

    Stream<Integer> boxed();

    @Override
    IntStream sequential();

    @Override
    IntStream parallel();

    @Override
    PrimitiveIterator.OfInt iterator();

    @Override
    Spliterator.OfInt spliterator();

    // ---- static factories ----

    public static Builder builder() {
        return new IntPipe.BuilderImpl();
    }

    public static IntStream empty() {
        return new IntPipe(new Src.Empty());
    }

    public static IntStream of(int t) {
        return new IntPipe(new Src.One(Integer.valueOf(t), true));
    }

    public static IntStream of(int... values) {
        ModelStuckS.nn(values);
        return ModelStreams.ofIntArray(values, 0, values.length);
    }

    public static IntStream iterate(final int seed, final IntUnaryOperator f) {
        if (f == null) throw new NullPointerException();
        return new IntPipe(new Src.IntIterate(seed, null, f));
    }

    public static IntStream iterate(int seed, IntPredicate hasNext, IntUnaryOperator next) {
        if (next == null) throw new NullPointerException();
        if (hasNext == null) throw new NullPointerException();
        return new IntPipe(new Src.IntIterate(seed, hasNext, next));
    }

    public static IntStream generate(IntSupplier s) {
        if (s == null) throw new NullPointerException();
        return new IntPipe(new Src.Generate(null, s, null));
    }

    public static IntStream range(int startInclusive, int endExclusive) {
        if (startInclusive >= endExclusive) return empty();
        return new IntPipe(new Src.IntRange(startInclusive, endExclusive, false));
    }

    public static IntStream rangeClosed(int startInclusive, int endInclusive) {
        if (startInclusive > endInclusive) return empty();
        return new IntPipe(new Src.IntRange(startInclusive, endInclusive, true));
    }

    public static IntStream concat(IntStream a, IntStream b) {
        if (a == null) throw new NullPointerException();
        if (b == null) throw new NullPointerException();
        Src sa = Pipe.srcOf(a);
        Src sb = Pipe.srcOf(b);
        IntStream stream = new IntPipe(new Src.Concat(sa, sb));
        return stream.onClose(Pipe.composedClose(a, b));
    }

    public interface Builder extends IntConsumer {
        @Override
        void accept(int t);

        default Builder add(int t) {
            accept(t);
            return this;
        }

        IntStream build();
    }

    @FunctionalInterface
    interface IntMapMultiConsumer {
        void accept(int value, IntConsumer ic);
    }
}

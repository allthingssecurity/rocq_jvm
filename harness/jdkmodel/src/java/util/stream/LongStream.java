/*
 * rocq-jvm model of java.util.stream.LongStream (clean-room, Apache-2.0), from the Javadoc. The
 * factories build sequential pipelines of the model (LongPipe): of/empty/builder/range are SIZED
 * sources (range is also ORDERED, DISTINCT and SORTED; empty() is not ORDERED), iterate is lazy and
 * ORDERED, generate is unordered. DoubleStream conversions, iterator() (PrimitiveIterator),
 * spliterator() and summaryStatistics() are STUCK in the model pipeline.
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
import java.util.function.LongSupplier;
import java.util.function.LongToDoubleFunction;
import java.util.function.LongToIntFunction;
import java.util.function.LongUnaryOperator;
import java.util.function.ObjLongConsumer;
import java.util.function.Supplier;

public interface LongStream extends BaseStream<Long, LongStream> {
    LongStream filter(LongPredicate predicate);

    LongStream map(LongUnaryOperator mapper);

    <U> Stream<U> mapToObj(LongFunction<? extends U> mapper);

    IntStream mapToInt(LongToIntFunction mapper);

    DoubleStream mapToDouble(LongToDoubleFunction mapper);

    LongStream flatMap(LongFunction<? extends LongStream> mapper);

    default LongStream mapMulti(LongMapMultiConsumer mapper) {
        throw ModelStuckS.unsupported("LongStream.mapMulti default method");
    }

    LongStream distinct();

    LongStream sorted();

    LongStream peek(LongConsumer action);

    LongStream limit(long maxSize);

    LongStream skip(long n);

    default LongStream takeWhile(LongPredicate predicate) {
        throw ModelStuckS.unsupported("LongStream.takeWhile default method");
    }

    default LongStream dropWhile(LongPredicate predicate) {
        throw ModelStuckS.unsupported("LongStream.dropWhile default method");
    }

    void forEach(LongConsumer action);

    void forEachOrdered(LongConsumer action);

    long[] toArray();

    long reduce(long identity, LongBinaryOperator op);

    OptionalLong reduce(LongBinaryOperator op);

    <R> R collect(Supplier<R> supplier, ObjLongConsumer<R> accumulator, BiConsumer<R, R> combiner);

    long sum();

    OptionalLong min();

    OptionalLong max();

    long count();

    OptionalDouble average();

    LongSummaryStatistics summaryStatistics();

    boolean anyMatch(LongPredicate predicate);

    boolean allMatch(LongPredicate predicate);

    boolean noneMatch(LongPredicate predicate);

    OptionalLong findFirst();

    OptionalLong findAny();

    DoubleStream asDoubleStream();

    Stream<Long> boxed();

    @Override
    LongStream sequential();

    @Override
    LongStream parallel();

    @Override
    PrimitiveIterator.OfLong iterator();

    @Override
    Spliterator.OfLong spliterator();

    // ---- static factories ----

    public static Builder builder() {
        return new LongPipe.BuilderImpl();
    }

    public static LongStream empty() {
        return new LongPipe(new Src.Empty());
    }

    public static LongStream of(long t) {
        return new LongPipe(new Src.One(Long.valueOf(t), true));
    }

    public static LongStream of(long... values) {
        ModelStuckS.nn(values);
        return ModelStreams.ofLongArray(values, 0, values.length);
    }

    public static LongStream iterate(final long seed, final LongUnaryOperator f) {
        if (f == null) throw new NullPointerException();
        return new LongPipe(new Src.LongIterate(seed, null, f));
    }

    public static LongStream iterate(long seed, LongPredicate hasNext, LongUnaryOperator next) {
        if (next == null) throw new NullPointerException();
        if (hasNext == null) throw new NullPointerException();
        return new LongPipe(new Src.LongIterate(seed, hasNext, next));
    }

    public static LongStream generate(LongSupplier s) {
        if (s == null) throw new NullPointerException();
        return new LongPipe(new Src.Generate(null, null, s));
    }

    public static LongStream range(long startInclusive, long endExclusive) {
        if (startInclusive >= endExclusive) return empty();
        if (endExclusive - startInclusive < 0) throw ModelStuckS.unsupported("LongStream.range of more than Long.MAX_VALUE elements");
        return new LongPipe(new Src.LongRange(startInclusive, endExclusive, false));
    }

    public static LongStream rangeClosed(long startInclusive, long endInclusive) {
        if (startInclusive > endInclusive) return empty();
        if (endInclusive - startInclusive + 1 <= 0) throw ModelStuckS.unsupported("LongStream.rangeClosed of more than Long.MAX_VALUE elements");
        return new LongPipe(new Src.LongRange(startInclusive, endInclusive, true));
    }

    public static LongStream concat(LongStream a, LongStream b) {
        if (a == null) throw new NullPointerException();
        if (b == null) throw new NullPointerException();
        Src sa = Pipe.srcOf(a);
        Src sb = Pipe.srcOf(b);
        LongStream stream = new LongPipe(new Src.Concat(sa, sb));
        return stream.onClose(Pipe.composedClose(a, b));
    }

    public interface Builder extends LongConsumer {
        @Override
        void accept(long t);

        default Builder add(long t) {
            accept(t);
            return this;
        }

        LongStream build();
    }

    @FunctionalInterface
    interface LongMapMultiConsumer {
        void accept(long value, LongConsumer ic);
    }
}

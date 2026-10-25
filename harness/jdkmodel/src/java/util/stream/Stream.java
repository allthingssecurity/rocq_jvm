/*
 * rocq-jvm model of java.util.stream.Stream (clean-room, Apache-2.0), from the Javadoc. The
 * factories build sequential pipelines of the model (RefPipe): of/ofNullable/empty/builder are
 * ORDERED and SIZED sources (empty() is not ORDERED), iterate is ORDERED and lazy (the function is
 * applied only when the next element is needed), generate is unordered, concat keeps the
 * characteristics both sides share and closes both streams when it is closed.
 * The default methods are given for streams that are not model pipelines; the model pipeline
 * overrides all of them.
 */
package java.util.stream;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.IntConsumer;
import java.util.function.IntFunction;
import java.util.function.LongConsumer;
import java.util.function.DoubleConsumer;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.function.ToDoubleFunction;
import java.util.function.ToIntFunction;
import java.util.function.ToLongFunction;
import java.util.function.UnaryOperator;

public interface Stream<T> extends BaseStream<T, Stream<T>> {
    Stream<T> filter(Predicate<? super T> predicate);

    <R> Stream<R> map(Function<? super T, ? extends R> mapper);

    IntStream mapToInt(ToIntFunction<? super T> mapper);

    LongStream mapToLong(ToLongFunction<? super T> mapper);

    DoubleStream mapToDouble(ToDoubleFunction<? super T> mapper);

    <R> Stream<R> flatMap(Function<? super T, ? extends Stream<? extends R>> mapper);

    IntStream flatMapToInt(Function<? super T, ? extends IntStream> mapper);

    LongStream flatMapToLong(Function<? super T, ? extends LongStream> mapper);

    DoubleStream flatMapToDouble(Function<? super T, ? extends DoubleStream> mapper);

    default <R> Stream<R> mapMulti(BiConsumer<? super T, ? super Consumer<R>> mapper) {
        throw ModelStuckS.unsupported("Stream.mapMulti default method");
    }

    default IntStream mapMultiToInt(BiConsumer<? super T, ? super IntConsumer> mapper) {
        throw ModelStuckS.unsupported("Stream.mapMultiToInt default method");
    }

    default LongStream mapMultiToLong(BiConsumer<? super T, ? super LongConsumer> mapper) {
        throw ModelStuckS.unsupported("Stream.mapMultiToLong default method");
    }

    default DoubleStream mapMultiToDouble(BiConsumer<? super T, ? super DoubleConsumer> mapper) {
        throw ModelStuckS.unsupported("Stream.mapMultiToDouble (DoubleStream)");
    }

    Stream<T> distinct();

    Stream<T> sorted();

    Stream<T> sorted(Comparator<? super T> comparator);

    Stream<T> peek(Consumer<? super T> action);

    Stream<T> limit(long maxSize);

    Stream<T> skip(long n);

    default Stream<T> takeWhile(Predicate<? super T> predicate) {
        throw ModelStuckS.unsupported("Stream.takeWhile default method");
    }

    default Stream<T> dropWhile(Predicate<? super T> predicate) {
        throw ModelStuckS.unsupported("Stream.dropWhile default method");
    }

    void forEach(Consumer<? super T> action);

    void forEachOrdered(Consumer<? super T> action);

    Object[] toArray();

    <A> A[] toArray(IntFunction<A[]> generator);

    T reduce(T identity, BinaryOperator<T> accumulator);

    Optional<T> reduce(BinaryOperator<T> accumulator);

    <U> U reduce(U identity, BiFunction<U, ? super T, U> accumulator, BinaryOperator<U> combiner);

    <R> R collect(Supplier<R> supplier, BiConsumer<R, ? super T> accumulator, BiConsumer<R, R> combiner);

    <R, A> R collect(Collector<? super T, A, R> collector);

    @SuppressWarnings("unchecked")
    default List<T> toList() {
        return (List<T>) Collections.unmodifiableList(new ArrayList<>(Arrays.asList(this.toArray())));
    }

    Optional<T> min(Comparator<? super T> comparator);

    Optional<T> max(Comparator<? super T> comparator);

    long count();

    boolean anyMatch(Predicate<? super T> predicate);

    boolean allMatch(Predicate<? super T> predicate);

    boolean noneMatch(Predicate<? super T> predicate);

    Optional<T> findFirst();

    Optional<T> findAny();

    // ---- static factories ----

    public static <T> Builder<T> builder() {
        return new RefPipe.BuilderImpl<>();
    }

    public static <T> Stream<T> empty() {
        return new RefPipe<>(new Src.Empty());
    }

    public static <T> Stream<T> of(T t) {
        return new RefPipe<>(new Src.One(t, true));
    }

    public static <T> Stream<T> ofNullable(T t) {
        return t == null ? Stream.empty() : new RefPipe<>(new Src.One(t, true));
    }

    @SafeVarargs
    @SuppressWarnings("varargs")
    public static <T> Stream<T> of(T... values) {
        ModelStuckS.nn(values);
        return ModelStreams.ofArray(values, 0, values.length);
    }

    @SuppressWarnings("unchecked")
    public static <T> Stream<T> iterate(final T seed, final UnaryOperator<T> f) {
        if (f == null) throw new NullPointerException();
        return new RefPipe<>(new Src.Iterate(seed, (UnaryOperator<Object>) f));
    }

    @SuppressWarnings("unchecked")
    public static <T> Stream<T> iterate(T seed, Predicate<? super T> hasNext, UnaryOperator<T> next) {
        if (next == null) throw new NullPointerException();
        if (hasNext == null) throw new NullPointerException();
        return new RefPipe<>(new Src.Iterate3(seed, (Predicate<Object>) hasNext, (UnaryOperator<Object>) next));
    }

    public static <T> Stream<T> generate(Supplier<? extends T> s) {
        if (s == null) throw new NullPointerException();
        return new RefPipe<>(new Src.Generate(s, null, null));
    }

    public static <T> Stream<T> concat(Stream<? extends T> a, Stream<? extends T> b) {
        if (a == null) throw new NullPointerException();
        if (b == null) throw new NullPointerException();
        Src sa = Pipe.srcOf(a);
        Src sb = Pipe.srcOf(b);
        Stream<T> stream = new RefPipe<>(new Src.Concat(sa, sb));
        return stream.onClose(Pipe.composedClose(a, b));
    }

    public interface Builder<T> extends Consumer<T> {
        @Override
        void accept(T t);

        default Builder<T> add(T t) {
            accept(t);
            return this;
        }

        Stream<T> build();
    }
}

/*
 * rocq-jvm model (clean-room, Apache-2.0): the Stream implementation of the model (a stage of a
 * sequential pipeline of references). Argument checks happen before the stage is linked (except
 * sorted(null) and onClose(null), which the JDK checks after linking), as in the JDK.
 */
package java.util.stream;

import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.Spliterator;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Consumer;
import java.util.function.DoubleConsumer;
import java.util.function.Function;
import java.util.function.IntConsumer;
import java.util.function.IntFunction;
import java.util.function.LongConsumer;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.function.ToDoubleFunction;
import java.util.function.ToIntFunction;
import java.util.function.ToLongFunction;

@SuppressWarnings({"unchecked", "rawtypes"})
final class RefPipe<T> extends Pipe implements Stream<T> {
    RefPipe(Src s) {
        super(s);
    }

    RefPipe(Pipe up, Op op) {
        super(up, op);
    }

    private static <X> X req(X x) {
        if (x == null) throw new NullPointerException();
        return x;
    }

    // ---- BaseStream ----

    public Iterator<T> iterator() {
        return (Iterator<T>) iteratorInternal();
    }

    public Spliterator<T> spliterator() {
        throw ModelStuckS.unsupported("Stream.spliterator");
    }

    public boolean isParallel() {
        return false;
    }

    public Stream<T> sequential() {
        return this;
    }

    public Stream<T> parallel() {
        throw ModelStuckS.unsupported("parallel streams");
    }

    public Stream<T> unordered() {
        if (!isOrdered()) return this;
        return new RefPipe<>(this, unorderedOp());
    }

    public Stream<T> onClose(Runnable closeHandler) {
        onCloseInternal(closeHandler);
        return this;
    }

    public void close() {
        closeInternal();
    }

    // ---- stateless intermediate ops ----

    public Stream<T> filter(Predicate<? super T> predicate) {
        req(predicate);
        return new RefPipe<>(this, filterOp((Predicate<Object>) predicate));
    }

    public <R> Stream<R> map(Function<? super T, ? extends R> mapper) {
        req(mapper);
        return new RefPipe<>(this, mapOp((Function<Object, Object>) mapper, SORTED | DISTINCT));
    }

    public IntStream mapToInt(ToIntFunction<? super T> mapper) {
        req(mapper);
        ToIntFunction<Object> f = (ToIntFunction<Object>) mapper;
        return new IntPipe(this, mapOp(t -> Integer.valueOf(f.applyAsInt(t)), SORTED | DISTINCT));
    }

    public LongStream mapToLong(ToLongFunction<? super T> mapper) {
        req(mapper);
        ToLongFunction<Object> f = (ToLongFunction<Object>) mapper;
        return new LongPipe(this, mapOp(t -> Long.valueOf(f.applyAsLong(t)), SORTED | DISTINCT));
    }

    public DoubleStream mapToDouble(ToDoubleFunction<? super T> mapper) {
        req(mapper);
        return new DoublePipe(this, mapOp(o -> Double.valueOf(((ToDoubleFunction<Object>) (ToDoubleFunction) mapper).applyAsDouble(o)), SORTED | DISTINCT));
    }

    public <R> Stream<R> flatMap(Function<? super T, ? extends Stream<? extends R>> mapper) {
        req(mapper);
        return new RefPipe<>(this, flatMapOp((Function<Object, Object>) (Function) mapper, 0));
    }

    public IntStream flatMapToInt(Function<? super T, ? extends IntStream> mapper) {
        req(mapper);
        return new IntPipe(this, flatMapOp((Function<Object, Object>) (Function) mapper, 1));
    }

    public LongStream flatMapToLong(Function<? super T, ? extends LongStream> mapper) {
        req(mapper);
        return new LongPipe(this, flatMapOp((Function<Object, Object>) (Function) mapper, 2));
    }

    public DoubleStream flatMapToDouble(Function<? super T, ? extends DoubleStream> mapper) {
        req(mapper);
        return new DoublePipe(this, flatMapOp((Function<Object, Object>) (Function) mapper, 3));
    }

    public <R> Stream<R> mapMulti(BiConsumer<? super T, ? super Consumer<R>> mapper) {
        req(mapper);
        BiConsumer<Object, Object> m = (BiConsumer<Object, Object>) (BiConsumer) mapper;
        return new RefPipe<>(this, mapMultiOp((t, sink) -> m.accept(t, sink)));
    }

    public IntStream mapMultiToInt(BiConsumer<? super T, ? super IntConsumer> mapper) {
        req(mapper);
        BiConsumer<Object, Object> m = (BiConsumer<Object, Object>) (BiConsumer) mapper;
        return new IntPipe(this, mapMultiOp((t, sink) -> m.accept(t, sink)));
    }

    public LongStream mapMultiToLong(BiConsumer<? super T, ? super LongConsumer> mapper) {
        req(mapper);
        BiConsumer<Object, Object> m = (BiConsumer<Object, Object>) (BiConsumer) mapper;
        return new LongPipe(this, mapMultiOp((t, sink) -> m.accept(t, sink)));
    }

    public DoubleStream mapMultiToDouble(BiConsumer<? super T, ? super DoubleConsumer> mapper) {
        req(mapper);
        BiConsumer<Object, Object> m = (BiConsumer<Object, Object>) (BiConsumer) mapper;
        return new DoublePipe(this, mapMultiOp((t, sink) -> m.accept(t, sink)));
    }

    public Stream<T> peek(Consumer<? super T> action) {
        req(action);
        return new RefPipe<>(this, peekOp((Consumer<Object>) action));
    }

    // ---- stateful intermediate ops ----

    public Stream<T> distinct() {
        return new RefPipe<>(this, distinctOp());
    }

    public Stream<T> sorted() {
        return new RefPipe<>(this, sortedOp(null, false));
    }

    public Stream<T> sorted(Comparator<? super T> comparator) {
        RefPipe<T> p = new RefPipe<>(this, sortedOp((Comparator<Object>) comparator, false));
        req(comparator);
        return p;
    }

    public Stream<T> limit(long maxSize) {
        if (maxSize < 0) throw new IllegalArgumentException(Long.toString(maxSize));
        return new RefPipe<>(this, sliceOp(0, maxSize));
    }

    public Stream<T> skip(long n) {
        if (n < 0) throw new IllegalArgumentException(Long.toString(n));
        if (n == 0) return this;
        return new RefPipe<>(this, sliceOp(n, -1));
    }

    public Stream<T> takeWhile(Predicate<? super T> predicate) {
        req(predicate);
        return new RefPipe<>(this, takeWhileOp((Predicate<Object>) predicate));
    }

    public Stream<T> dropWhile(Predicate<? super T> predicate) {
        req(predicate);
        return new RefPipe<>(this, dropWhileOp((Predicate<Object>) predicate));
    }

    // ---- terminal ops ----

    public void forEach(Consumer<? super T> action) {
        req(action);
        forEachT((Consumer<Object>) action, false);
    }

    public void forEachOrdered(Consumer<? super T> action) {
        req(action);
        forEachT((Consumer<Object>) action, true);
    }

    public Object[] toArray() {
        return toArray(Object[]::new);
    }

    public <A> A[] toArray(IntFunction<A[]> generator) {
        ModelStuckS.nn(generator);
        Src s = terminal(0, 0);
        long size = exactOutputSize(s);
        if (size >= 0 && size < MAX_ARRAY_SIZE) {
            // a fixed-size array, made before the traversal
            Object[] array = generator.apply((int) size);
            ModelStuckS.nn(array);
            class Fixed extends Sink {
                int curSize;

                void begin(long sz) {
                    if (sz != array.length)
                        throw new IllegalStateException("Begin size " + sz + " is not equal to fixed size " + array.length);
                    curSize = 0;
                }

                public void accept(Object t) {
                    if (curSize < array.length) {
                        array[curSize++] = t;
                    } else {
                        throw new IllegalStateException("Accept exceeded fixed size of " + array.length);
                    }
                }

                void end() {
                    if (curSize < array.length)
                        throw new IllegalStateException("End size " + curSize + " is less than fixed size " + array.length);
                }
            }
            Fixed f = wrapAndCopyInto(new Fixed(), s);
            if (f.curSize < array.length)
                throw new IllegalStateException("Current size " + f.curSize + " is less than fixed size " + array.length);
            return (A[]) array;
        }
        Buf b = wrapAndCopyInto(new Buf(), s);
        if (b.n >= MAX_ARRAY_SIZE) throw new IllegalArgumentException("Stream size exceeds max array size");
        Object[] result = generator.apply(b.n);
        ModelStuckS.nn(result);
        if (b.n > result.length) throw new IndexOutOfBoundsException("does not fit");
        for (int i = 0; i < b.n; i++) {
            try {
                result[i] = b.a[i];
            } catch (ArrayStoreException e) {
                throw ModelStuckS.unsupported("toArray: System.arraycopy ArrayStoreException message");
            }
        }
        return (A[]) result;
    }

    public List<T> toList() {
        return (List<T>) StreamList.nullsAllowed(toArray());
    }

    public T reduce(T identity, BinaryOperator<T> accumulator) {
        req(accumulator);
        return (T) reduceT(identity, (BiFunction<Object, Object, Object>) (BiFunction) accumulator);
    }

    public Optional<T> reduce(BinaryOperator<T> accumulator) {
        req(accumulator);
        Object[] r = reduceOptT((BinaryOperator<Object>) (BinaryOperator) accumulator);
        return r == null ? Optional.empty() : Optional.of((T) r[0]);
    }

    public <U> U reduce(U identity, BiFunction<U, ? super T, U> accumulator, BinaryOperator<U> combiner) {
        req(accumulator);
        req(combiner);
        return (U) reduceT(identity, (BiFunction<Object, Object, Object>) (BiFunction) accumulator);
    }

    public <R> R collect(Supplier<R> supplier, BiConsumer<R, ? super T> accumulator, BiConsumer<R, R> combiner) {
        req(supplier);
        req(accumulator);
        req(combiner);
        return (R) collectT(supplier, (BiConsumer<Object, Object>) (BiConsumer) accumulator, 0);
    }

    public <R, A> R collect(Collector<? super T, A, R> collector) {
        req(collector);
        Supplier<A> supplier = collector.supplier();
        BiConsumer<A, ? super T> accumulator = collector.accumulator();
        BinaryOperator<A> combiner = collector.combiner();
        if (linked) throw new IllegalStateException(MSG_LINKED);
        linked = true;
        int clear = collector.characteristics().contains(Collector.Characteristics.UNORDERED) ? ORDERED : 0;
        Src s = sourceSrc(0, clear);
        A container = (A) collectS(s, supplier, (BiConsumer<Object, Object>) (BiConsumer) accumulator);
        return collector.characteristics().contains(Collector.Characteristics.IDENTITY_FINISH)
            ? (R) container
            : collector.finisher().apply(container);
    }

    public Optional<T> min(Comparator<? super T> comparator) {
        return reduce(java.util.function.BinaryOperator.minBy(comparator));
    }

    public Optional<T> max(Comparator<? super T> comparator) {
        return reduce(java.util.function.BinaryOperator.maxBy(comparator));
    }

    public long count() {
        return countT();
    }

    public boolean anyMatch(Predicate<? super T> predicate) {
        req(predicate);
        return matchT((Predicate<Object>) predicate, 0);
    }

    public boolean allMatch(Predicate<? super T> predicate) {
        req(predicate);
        return matchT((Predicate<Object>) predicate, 1);
    }

    public boolean noneMatch(Predicate<? super T> predicate) {
        req(predicate);
        return matchT((Predicate<Object>) predicate, 2);
    }

    public Optional<T> findFirst() {
        Object[] r = findT(true);
        return r == null ? Optional.empty() : Optional.of((T) r[0]);
    }

    public Optional<T> findAny() {
        Object[] r = findT(false);
        return r == null ? Optional.empty() : Optional.of((T) r[0]);
    }

    // ---- Stream.builder() ----

    static final class BuilderImpl<T> implements Stream.Builder<T> {
        // count >= 0: building (number of elements); < 0: built
        int count;
        Object first;
        Object[] buffer;

        public void accept(T t) {
            if (count == 0) {
                first = t;
                count++;
            } else if (count > 0) {
                if (buffer == null) {
                    buffer = new Object[8];
                    buffer[0] = first;
                }
                if (count == buffer.length) buffer = copyOf(buffer, count * 2);
                buffer[count++] = t;
            } else {
                throw new IllegalStateException();
            }
        }

        public Stream.Builder<T> add(T t) {
            accept(t);
            return this;
        }

        public Stream<T> build() {
            int c = count;
            if (c >= 0) {
                count = -count - 1;
                if (c < 2) return new RefPipe<>(new Src.One(first, c == 1));
                return new RefPipe<>(new Src.Arr(buffer, 0, c));
            }
            throw new IllegalStateException();
        }
    }
}

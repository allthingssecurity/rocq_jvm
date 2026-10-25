/*
 * rocq-jvm model of java.util.stream.Collectors (clean-room, Apache-2.0), from the Javadoc:
 * toList/toSet/toCollection collect into ArrayList/HashSet/the supplied collection; toMap uses a
 * HashMap (putIfAbsent, IllegalStateException "Duplicate key k (attempted merging values u and
 * v)", NullPointerException for null values) or Map.merge with a merge function; groupingBy uses
 * computeIfAbsent on the map (NullPointerException "element cannot be mapped to a null key") and
 * applies the downstream finisher with replaceAll; partitioningBy yields a two-entry map
 * {false=.., true=..}; joining uses StringBuilder / StringJoiner; reducing/minBy/maxBy give
 * Optional.ofNullable of the result. The order in which a downstream collector's functions are
 * obtained follows the JDK (observable only by collectors with side effects).
 * STUCK: the concurrent collectors (groupingByConcurrent, toConcurrentMap), toUnmodifiableSet and
 * toUnmodifiableMap (Set.of/Map.ofEntries iteration order is randomized per JVM), the
 * summarizing* collectors (summary statistics classes), summingDouble/averagingDouble; a null
 * function that the JDK dereferences without a check (helpful NullPointerException).
 */
package java.util.stream;

import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.DoubleSummaryStatistics;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IntSummaryStatistics;
import java.util.Iterator;
import java.util.List;
import java.util.LongSummaryStatistics;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Set;
import java.util.StringJoiner;
import java.util.concurrent.ConcurrentMap;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.function.ToDoubleFunction;
import java.util.function.ToIntFunction;
import java.util.function.ToLongFunction;

@SuppressWarnings({"unchecked", "rawtypes"})
public final class Collectors {
    static final Set<Collector.Characteristics> CH_ID = new CharSet(CharSet.ID);
    static final Set<Collector.Characteristics> CH_UNORDERED_ID = new CharSet(CharSet.UNORDERED | CharSet.ID);
    static final Set<Collector.Characteristics> CH_NOID = Collections.emptySet();
    static final Set<Collector.Characteristics> CH_UNORDERED_NOID = new CharSet(CharSet.UNORDERED);

    private Collectors() {
    }

    private static void nn(Object f) {
        ModelStuckS.nn(f);
    }

    static final class CollectorImpl<T, A, R> implements Collector<T, A, R> {
        private final Supplier<A> supplier;
        private final BiConsumer<A, T> accumulator;
        private final BinaryOperator<A> combiner;
        private final Function<A, R> finisher;
        private final Set<Characteristics> characteristics;

        CollectorImpl(Supplier<A> supplier, BiConsumer<A, T> accumulator, BinaryOperator<A> combiner,
                      Function<A, R> finisher, Set<Characteristics> characteristics) {
            this.supplier = supplier;
            this.accumulator = accumulator;
            this.combiner = combiner;
            this.finisher = finisher != null ? finisher : i -> (R) i;
            this.characteristics = characteristics;
        }

        CollectorImpl(Supplier<A> supplier, BiConsumer<A, T> accumulator, BinaryOperator<A> combiner,
                      Set<Characteristics> characteristics) {
            this(supplier, accumulator, combiner, null, characteristics);
        }

        public Supplier<A> supplier() {
            return supplier;
        }

        public BiConsumer<A, T> accumulator() {
            return accumulator;
        }

        public BinaryOperator<A> combiner() {
            return combiner;
        }

        public Function<A, R> finisher() {
            return finisher;
        }

        public Set<Characteristics> characteristics() {
            return characteristics;
        }
    }

    private static IllegalStateException duplicateKeyException(Object k, Object u, Object v) {
        return new IllegalStateException("Duplicate key " + k + " (attempted merging values " + u + " and " + v + ")");
    }

    // ---------------------------------------------------------------- collections

    public static <T, C extends Collection<T>> Collector<T, ?, C> toCollection(Supplier<C> collectionFactory) {
        nn(collectionFactory);
        return new CollectorImpl<T, C, C>(collectionFactory, (c, t) -> c.add(t),
                                          (r1, r2) -> { r1.addAll(r2); return r1; }, CH_ID);
    }

    public static <T> Collector<T, ?, List<T>> toList() {
        return new CollectorImpl<T, List<T>, List<T>>(() -> new ArrayList<>(), (l, t) -> l.add(t),
                                                      (left, right) -> { left.addAll(right); return left; }, CH_ID);
    }

    public static <T> Collector<T, ?, List<T>> toUnmodifiableList() {
        return new CollectorImpl<T, List<T>, List<T>>(() -> new ArrayList<>(), (l, t) -> l.add(t),
            (left, right) -> { left.addAll(right); return left; },
            list -> {
                if (list.getClass() == ArrayList.class) return (List<T>) StreamList.trusted(list.toArray());
                throw new IllegalArgumentException();
            },
            CH_NOID);
    }

    public static <T> Collector<T, ?, Set<T>> toSet() {
        return new CollectorImpl<T, Set<T>, Set<T>>(() -> new HashSet<>(), (s, t) -> s.add(t),
            (left, right) -> {
                if (left.size() < right.size()) {
                    right.addAll(left);
                    return right;
                } else {
                    left.addAll(right);
                    return left;
                }
            }, CH_UNORDERED_ID);
    }

    public static <T> Collector<T, ?, Set<T>> toUnmodifiableSet() {
        throw ModelStuckS.unsupported("Collectors.toUnmodifiableSet (Set.of iteration order)");
    }

    // ---------------------------------------------------------------- joining

    private static void appendCharSequence(StringBuilder sb, CharSequence cs) {
        if (cs == null || cs instanceof String) sb.append((String) cs);
        else if (cs instanceof StringBuilder) sb.append(cs.toString());
        else throw ModelStuckS.unsupported("joining(): StringBuilder.append of a CharSequence that is not a String");
    }

    public static Collector<CharSequence, ?, String> joining() {
        return new CollectorImpl<CharSequence, StringBuilder, String>(
            () -> new StringBuilder(), (sb, cs) -> appendCharSequence(sb, cs),
            (r1, r2) -> { r1.append(r2.toString()); return r1; },
            sb -> sb.toString(), CH_NOID);
    }

    public static Collector<CharSequence, ?, String> joining(CharSequence delimiter) {
        return joining(delimiter, "", "");
    }

    public static Collector<CharSequence, ?, String> joining(CharSequence delimiter, CharSequence prefix, CharSequence suffix) {
        return new CollectorImpl<CharSequence, StringJoiner, String>(
            () -> new StringJoiner(delimiter, prefix, suffix), (sj, cs) -> sj.add(cs),
            (a, b) -> a.merge(b), sj -> sj.toString(), CH_NOID);
    }

    // ---------------------------------------------------------------- adapters

    private static <K, V, M extends Map<K, V>> BinaryOperator<M> mapMerger(BinaryOperator<V> mergeFunction) {
        return (m1, m2) -> {
            for (Map.Entry<K, V> e : m2.entrySet()) m1.merge(e.getKey(), e.getValue(), mergeFunction);
            return m1;
        };
    }

    public static <T, U, A, R> Collector<T, ?, R> mapping(Function<? super T, ? extends U> mapper,
                                                         Collector<? super U, A, R> downstream) {
        nn(downstream);
        nn(mapper);
        BiConsumer<A, ? super U> downstreamAccumulator = downstream.accumulator();
        return new CollectorImpl<T, A, R>(downstream.supplier(),
                                          (r, t) -> ((BiConsumer) downstreamAccumulator).accept(r, mapper.apply(t)),
                                          downstream.combiner(), downstream.finisher(), downstream.characteristics());
    }

    public static <T, U, A, R> Collector<T, ?, R> flatMapping(Function<? super T, ? extends Stream<? extends U>> mapper,
                                                             Collector<? super U, A, R> downstream) {
        nn(downstream);
        nn(mapper);
        BiConsumer<A, ? super U> downstreamAccumulator = downstream.accumulator();
        return new CollectorImpl<T, A, R>(downstream.supplier(),
            (r, t) -> {
                try (Stream<? extends U> result = mapper.apply(t)) {
                    if (result != null) result.sequential().forEach(u -> ((BiConsumer) downstreamAccumulator).accept(r, u));
                }
            },
            downstream.combiner(), downstream.finisher(), downstream.characteristics());
    }

    public static <T, A, R> Collector<T, ?, R> filtering(Predicate<? super T> predicate, Collector<? super T, A, R> downstream) {
        nn(downstream);
        nn(predicate);
        BiConsumer<A, ? super T> downstreamAccumulator = downstream.accumulator();
        return new CollectorImpl<T, A, R>(downstream.supplier(),
            (r, t) -> {
                if (predicate.test(t)) ((BiConsumer) downstreamAccumulator).accept(r, t);
            },
            downstream.combiner(), downstream.finisher(), downstream.characteristics());
    }

    public static <T, A, R, RR> Collector<T, A, RR> collectingAndThen(Collector<T, A, R> downstream, Function<R, RR> finisher) {
        nn(downstream);
        Set<Collector.Characteristics> characteristics = downstream.characteristics();
        if (characteristics.contains(Collector.Characteristics.IDENTITY_FINISH)) {
            if (characteristics.size() == 1) characteristics = CH_NOID;
            else characteristics = new CharSet(CharSet.bitsOf(characteristics) & ~CharSet.ID);
        }
        Supplier<A> s = downstream.supplier();
        BiConsumer<A, T> a = downstream.accumulator();
        BinaryOperator<A> c = downstream.combiner();
        Function<A, R> f = downstream.finisher();
        nn(f);
        return new CollectorImpl<>(s, a, c, f.andThen(finisher), characteristics);
    }

    // ---------------------------------------------------------------- reductions

    public static <T> Collector<T, ?, Long> counting() {
        return summingLong(e -> 1L);
    }

    public static <T> Collector<T, ?, Optional<T>> minBy(Comparator<? super T> comparator) {
        return reducing(BinaryOperator.minBy(comparator));
    }

    public static <T> Collector<T, ?, Optional<T>> maxBy(Comparator<? super T> comparator) {
        return reducing(BinaryOperator.maxBy(comparator));
    }

    public static <T> Collector<T, ?, Integer> summingInt(ToIntFunction<? super T> mapper) {
        nn(mapper);
        return new CollectorImpl<T, int[], Integer>(() -> new int[1],
                                                    (a, t) -> { a[0] += mapper.applyAsInt(t); },
                                                    (a, b) -> { a[0] += b[0]; return a; },
                                                    a -> a[0], CH_NOID);
    }

    public static <T> Collector<T, ?, Long> summingLong(ToLongFunction<? super T> mapper) {
        nn(mapper);
        return new CollectorImpl<T, long[], Long>(() -> new long[1],
                                                  (a, t) -> { a[0] += mapper.applyAsLong(t); },
                                                  (a, b) -> { a[0] += b[0]; return a; },
                                                  a -> a[0], CH_NOID);
    }

    public static <T> Collector<T, ?, Double> summingDouble(ToDoubleFunction<? super T> mapper) {
        throw ModelStuckS.unsupported("Collectors.summingDouble");
    }

    public static <T> Collector<T, ?, Double> averagingInt(ToIntFunction<? super T> mapper) {
        nn(mapper);
        return new CollectorImpl<T, long[], Double>(() -> new long[2],
                                                    (a, t) -> { a[0] += mapper.applyAsInt(t); a[1]++; },
                                                    (a, b) -> { a[0] += b[0]; a[1] += b[1]; return a; },
                                                    a -> (a[1] == 0) ? 0.0d : (double) a[0] / a[1], CH_NOID);
    }

    public static <T> Collector<T, ?, Double> averagingLong(ToLongFunction<? super T> mapper) {
        nn(mapper);
        return new CollectorImpl<T, long[], Double>(() -> new long[2],
                                                    (a, t) -> { a[0] += mapper.applyAsLong(t); a[1]++; },
                                                    (a, b) -> { a[0] += b[0]; a[1] += b[1]; return a; },
                                                    a -> (a[1] == 0) ? 0.0d : (double) a[0] / a[1], CH_NOID);
    }

    public static <T> Collector<T, ?, Double> averagingDouble(ToDoubleFunction<? super T> mapper) {
        throw ModelStuckS.unsupported("Collectors.averagingDouble");
    }

    public static <T> Collector<T, ?, T> reducing(T identity, BinaryOperator<T> op) {
        nn(op);
        return new CollectorImpl<T, Object[], T>(() -> new Object[] { identity },
                                                 (a, t) -> { a[0] = op.apply((T) a[0], t); },
                                                 (a, b) -> { a[0] = op.apply((T) a[0], (T) b[0]); return a; },
                                                 a -> (T) a[0], CH_NOID);
    }

    private static final class OptionalBox<T> implements Consumer<T> {
        final BinaryOperator<T> op;
        T value = null;
        boolean present = false;

        OptionalBox(BinaryOperator<T> op) {
            this.op = op;
        }

        public void accept(T t) {
            if (present) {
                value = op.apply(value, t);
            } else {
                value = t;
                present = true;
            }
        }
    }

    public static <T> Collector<T, ?, Optional<T>> reducing(BinaryOperator<T> op) {
        nn(op);
        return new CollectorImpl<T, OptionalBox<T>, Optional<T>>(() -> new OptionalBox<>(op), (a, t) -> a.accept(t),
            (a, b) -> { if (b.present) a.accept(b.value); return a; },
            a -> Optional.ofNullable(a.value), CH_NOID);
    }

    public static <T, U> Collector<T, ?, U> reducing(U identity, Function<? super T, ? extends U> mapper, BinaryOperator<U> op) {
        nn(mapper);
        nn(op);
        return new CollectorImpl<T, Object[], U>(() -> new Object[] { identity },
                                                 (a, t) -> { a[0] = op.apply((U) a[0], mapper.apply(t)); },
                                                 (a, b) -> { a[0] = op.apply((U) a[0], (U) b[0]); return a; },
                                                 a -> (U) a[0], CH_NOID);
    }

    // ---------------------------------------------------------------- grouping

    public static <T, K> Collector<T, ?, Map<K, List<T>>> groupingBy(Function<? super T, ? extends K> classifier) {
        return groupingBy(classifier, toList());
    }

    public static <T, K, A, D> Collector<T, ?, Map<K, D>> groupingBy(Function<? super T, ? extends K> classifier,
                                                                    Collector<? super T, A, D> downstream) {
        return groupingBy(classifier, () -> new HashMap<>(), downstream);
    }

    public static <T, K, D, A, M extends Map<K, D>> Collector<T, ?, M> groupingBy(Function<? super T, ? extends K> classifier,
                                                                                 Supplier<M> mapFactory,
                                                                                 Collector<? super T, A, D> downstream) {
        nn(downstream);
        nn(classifier);
        nn(mapFactory);
        Supplier<A> downstreamSupplier = downstream.supplier();
        BiConsumer<A, ? super T> downstreamAccumulator = downstream.accumulator();
        BiConsumer<Map<K, A>, T> accumulator = (m, t) -> {
            K key = classifier.apply(t);
            if (key == null) throw new NullPointerException("element cannot be mapped to a null key");
            A container = m.computeIfAbsent(key, k -> downstreamSupplier.get());
            ((BiConsumer) downstreamAccumulator).accept(container, t);
        };
        BinaryOperator<Map<K, A>> merger = Collectors.<K, A, Map<K, A>>mapMerger(downstream.combiner());
        Supplier<Map<K, A>> mangledFactory = (Supplier<Map<K, A>>) mapFactory;
        if (downstream.characteristics().contains(Collector.Characteristics.IDENTITY_FINISH)) {
            return new CollectorImpl<>(mangledFactory, accumulator, merger, CH_ID);
        } else {
            Function<A, A> downstreamFinisher = (Function<A, A>) downstream.finisher();
            Function<Map<K, A>, M> finisher = intermediate -> {
                intermediate.replaceAll((k, v) -> downstreamFinisher.apply(v));
                return (M) intermediate;
            };
            return new CollectorImpl<>(mangledFactory, accumulator, merger, finisher, CH_NOID);
        }
    }

    public static <T, K> Collector<T, ?, ConcurrentMap<K, List<T>>> groupingByConcurrent(Function<? super T, ? extends K> classifier) {
        throw ModelStuckS.unsupported("Collectors.groupingByConcurrent");
    }

    public static <T, K, A, D> Collector<T, ?, ConcurrentMap<K, D>> groupingByConcurrent(Function<? super T, ? extends K> classifier,
                                                                                        Collector<? super T, A, D> downstream) {
        throw ModelStuckS.unsupported("Collectors.groupingByConcurrent");
    }

    public static <T, K, A, D, M extends ConcurrentMap<K, D>> Collector<T, ?, M> groupingByConcurrent(
            Function<? super T, ? extends K> classifier, Supplier<M> mapFactory, Collector<? super T, A, D> downstream) {
        throw ModelStuckS.unsupported("Collectors.groupingByConcurrent");
    }

    public static <T> Collector<T, ?, Map<Boolean, List<T>>> partitioningBy(Predicate<? super T> predicate) {
        return partitioningBy(predicate, toList());
    }

    public static <T, D, A> Collector<T, ?, Map<Boolean, D>> partitioningBy(Predicate<? super T> predicate,
                                                                           Collector<? super T, A, D> downstream) {
        nn(downstream);
        nn(predicate);
        BiConsumer<A, ? super T> downstreamAccumulator = downstream.accumulator();
        BiConsumer<Partition<A>, T> accumulator = (result, t) ->
            ((BiConsumer) downstreamAccumulator).accept(predicate.test(t) ? result.forTrue : result.forFalse, t);
        BinaryOperator<A> op = downstream.combiner();
        BinaryOperator<Partition<A>> merger = (left, right) ->
            new Partition<>(op.apply(left.forTrue, right.forTrue), op.apply(left.forFalse, right.forFalse));
        Supplier<Partition<A>> supplier = () -> new Partition<>(downstream.supplier().get(), downstream.supplier().get());
        if (downstream.characteristics().contains(Collector.Characteristics.IDENTITY_FINISH)) {
            return new CollectorImpl<>(supplier, accumulator, merger, CH_ID);
        } else {
            Function<Partition<A>, Map<Boolean, D>> finisher = par ->
                new Partition<>(downstream.finisher().apply(par.forTrue), downstream.finisher().apply(par.forFalse));
            return new CollectorImpl<>(supplier, accumulator, merger, finisher, CH_NOID);
        }
    }

    // ---------------------------------------------------------------- maps

    public static <T, K, U> Collector<T, ?, Map<K, U>> toMap(Function<? super T, ? extends K> keyMapper,
                                                            Function<? super T, ? extends U> valueMapper) {
        nn(keyMapper);
        nn(valueMapper);
        BiConsumer<Map<K, U>, T> accumulator = (map, element) -> {
            K k = keyMapper.apply(element);
            U v = valueMapper.apply(element);
            if (v == null) throw new NullPointerException();
            U u = map.putIfAbsent(k, v);
            if (u != null) throw duplicateKeyException(k, u, v);
        };
        BinaryOperator<Map<K, U>> merger = (m1, m2) -> {
            for (Map.Entry<K, U> e : m2.entrySet()) {
                K k = e.getKey();
                U v = e.getValue();
                if (v == null) throw new NullPointerException();
                U u = m1.putIfAbsent(k, v);
                if (u != null) throw duplicateKeyException(k, u, v);
            }
            return m1;
        };
        return new CollectorImpl<>(() -> new HashMap<>(), accumulator, merger, CH_ID);
    }

    public static <T, K, U> Collector<T, ?, Map<K, U>> toUnmodifiableMap(Function<? super T, ? extends K> keyMapper,
                                                                        Function<? super T, ? extends U> valueMapper) {
        throw ModelStuckS.unsupported("Collectors.toUnmodifiableMap (Map.ofEntries iteration order)");
    }

    public static <T, K, U> Collector<T, ?, Map<K, U>> toMap(Function<? super T, ? extends K> keyMapper,
                                                            Function<? super T, ? extends U> valueMapper,
                                                            BinaryOperator<U> mergeFunction) {
        return toMap(keyMapper, valueMapper, mergeFunction, () -> new HashMap<>());
    }

    public static <T, K, U> Collector<T, ?, Map<K, U>> toUnmodifiableMap(Function<? super T, ? extends K> keyMapper,
                                                                        Function<? super T, ? extends U> valueMapper,
                                                                        BinaryOperator<U> mergeFunction) {
        throw ModelStuckS.unsupported("Collectors.toUnmodifiableMap (Map.ofEntries iteration order)");
    }

    public static <T, K, U, M extends Map<K, U>> Collector<T, ?, M> toMap(Function<? super T, ? extends K> keyMapper,
                                                                         Function<? super T, ? extends U> valueMapper,
                                                                         BinaryOperator<U> mergeFunction,
                                                                         Supplier<M> mapFactory) {
        nn(keyMapper);
        nn(valueMapper);
        nn(mapFactory);
        BiConsumer<M, T> accumulator = (map, element) ->
            map.merge(keyMapper.apply(element), valueMapper.apply(element), mergeFunction);
        return new CollectorImpl<>(mapFactory, accumulator, mapMerger(mergeFunction), CH_ID);
    }

    public static <T, K, U> Collector<T, ?, ConcurrentMap<K, U>> toConcurrentMap(Function<? super T, ? extends K> keyMapper,
                                                                                Function<? super T, ? extends U> valueMapper) {
        throw ModelStuckS.unsupported("Collectors.toConcurrentMap");
    }

    public static <T, K, U> Collector<T, ?, ConcurrentMap<K, U>> toConcurrentMap(Function<? super T, ? extends K> keyMapper,
                                                                                Function<? super T, ? extends U> valueMapper,
                                                                                BinaryOperator<U> mergeFunction) {
        throw ModelStuckS.unsupported("Collectors.toConcurrentMap");
    }

    public static <T, K, U, M extends ConcurrentMap<K, U>> Collector<T, ?, M> toConcurrentMap(
            Function<? super T, ? extends K> keyMapper, Function<? super T, ? extends U> valueMapper,
            BinaryOperator<U> mergeFunction, Supplier<M> mapFactory) {
        throw ModelStuckS.unsupported("Collectors.toConcurrentMap");
    }

    // ---------------------------------------------------------------- statistics

    public static <T> Collector<T, ?, IntSummaryStatistics> summarizingInt(ToIntFunction<? super T> mapper) {
        throw ModelStuckS.unsupported("Collectors.summarizingInt");
    }

    public static <T> Collector<T, ?, LongSummaryStatistics> summarizingLong(ToLongFunction<? super T> mapper) {
        throw ModelStuckS.unsupported("Collectors.summarizingLong");
    }

    public static <T> Collector<T, ?, DoubleSummaryStatistics> summarizingDouble(ToDoubleFunction<? super T> mapper) {
        throw ModelStuckS.unsupported("Collectors.summarizingDouble");
    }

    // ---------------------------------------------------------------- teeing

    public static <T, R1, R2, R> Collector<T, ?, R> teeing(Collector<? super T, ?, R1> downstream1,
                                                          Collector<? super T, ?, R2> downstream2,
                                                          BiFunction<? super R1, ? super R2, R> merger) {
        if (downstream1 == null) throw new NullPointerException("downstream1");
        if (downstream2 == null) throw new NullPointerException("downstream2");
        if (merger == null) throw new NullPointerException("merger");
        Supplier c1Supplier = req(downstream1.supplier(), "downstream1 supplier");
        Supplier c2Supplier = req(downstream2.supplier(), "downstream2 supplier");
        BiConsumer c1Accumulator = req(downstream1.accumulator(), "downstream1 accumulator");
        BiConsumer c2Accumulator = req(downstream2.accumulator(), "downstream2 accumulator");
        BinaryOperator c1Combiner = req(downstream1.combiner(), "downstream1 combiner");
        BinaryOperator c2Combiner = req(downstream2.combiner(), "downstream2 combiner");
        Function c1Finisher = req(downstream1.finisher(), "downstream1 finisher");
        Function c2Finisher = req(downstream2.finisher(), "downstream2 finisher");
        Set<Collector.Characteristics> characteristics;
        Set<Collector.Characteristics> c1Characteristics = downstream1.characteristics();
        Set<Collector.Characteristics> c2Characteristics = downstream2.characteristics();
        if (CH_ID.containsAll(c1Characteristics) || CH_ID.containsAll(c2Characteristics)) {
            characteristics = CH_NOID;
        } else {
            int bits = CharSet.bitsOf(c1Characteristics) & CharSet.bitsOf(c2Characteristics) & ~CharSet.ID;
            characteristics = new CharSet(bits);
        }
        final class PairBox {
            Object left = c1Supplier.get();
            Object right = c2Supplier.get();

            void add(T t) {
                c1Accumulator.accept(left, t);
                c2Accumulator.accept(right, t);
            }

            PairBox combine(PairBox other) {
                left = c1Combiner.apply(left, other.left);
                right = c2Combiner.apply(right, other.right);
                return this;
            }

            R get() {
                Object r1 = c1Finisher.apply(left);
                Object r2 = c2Finisher.apply(right);
                return (R) ((BiFunction) merger).apply(r1, r2);
            }
        }
        return new CollectorImpl<T, PairBox, R>(() -> new PairBox(), (b, t) -> b.add(t), (a, b) -> a.combine(b),
                                                b -> b.get(), characteristics);
    }

    private static <X> X req(X x, String msg) {
        if (x == null) throw new NullPointerException(msg);
        return x;
    }

    // ---------------------------------------------------------------- partition map

    private static final class Partition<T> extends AbstractMap<Boolean, T> implements Map<Boolean, T> {
        final T forTrue;
        final T forFalse;

        Partition(T forTrue, T forFalse) {
            this.forTrue = forTrue;
            this.forFalse = forFalse;
        }

        public int size() {
            return 2;
        }

        public boolean isEmpty() {
            return false;
        }

        public T get(Object key) {
            if (key instanceof Boolean) return ((Boolean) key).booleanValue() ? forTrue : forFalse;
            return null;
        }

        public boolean containsKey(Object key) {
            return key instanceof Boolean;
        }

        public boolean containsValue(Object value) {
            return eq(value, forTrue) || eq(value, forFalse);
        }

        private static boolean eq(Object a, Object b) {
            return (a == b) || (a != null && a.equals(b));
        }

        public Set<Map.Entry<Boolean, T>> entrySet() {
            return new AbstractSet<Map.Entry<Boolean, T>>() {
                public Iterator<Map.Entry<Boolean, T>> iterator() {
                    Map.Entry<Boolean, T> falseEntry = new SimpleImmutableEntry<>(false, forFalse);
                    Map.Entry<Boolean, T> trueEntry = new SimpleImmutableEntry<>(true, forTrue);
                    return new Iterator<Map.Entry<Boolean, T>>() {
                        int cursor;

                        public boolean hasNext() {
                            return cursor != 2;
                        }

                        public Map.Entry<Boolean, T> next() {
                            int i = cursor;
                            if (i >= 2) throw new NoSuchElementException();
                            cursor = i + 1;
                            return i == 0 ? falseEntry : trueEntry;
                        }

                        public void remove() {
                            throw new UnsupportedOperationException();
                        }
                    };
                }

                public int size() {
                    return 2;
                }
            };
        }
    }
}

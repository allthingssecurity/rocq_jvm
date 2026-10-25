/*
 * rocq-jvm model of java.util.Comparator (clean-room, Apache-2.0): the default and static
 * methods as the Javadoc describes them (lexicographic thenComparing, key extractors, natural and
 * reverse order, null-friendly comparators). comparingDouble/thenComparingDouble are STUCK.
 */
package java.util;

import java.util.function.Function;
import java.util.function.ToIntFunction;
import java.util.function.ToLongFunction;
import java.util.function.ToDoubleFunction;

@FunctionalInterface
public interface Comparator<T> {
    int compare(T o1, T o2);

    boolean equals(Object obj);

    default Comparator<T> reversed() {
        return Collections.reverseOrder(this);
    }

    default Comparator<T> thenComparing(Comparator<? super T> other) {
        if (other == null) throw new NullPointerException();
        return (Comparator<T> & java.io.Serializable) (c1, c2) -> {
            int res = compare(c1, c2);
            return (res != 0) ? res : other.compare(c1, c2);
        };
    }

    default <U> Comparator<T> thenComparing(Function<? super T, ? extends U> keyExtractor, Comparator<? super U> keyComparator) {
        return thenComparing(comparing(keyExtractor, keyComparator));
    }

    default <U extends Comparable<? super U>> Comparator<T> thenComparing(Function<? super T, ? extends U> keyExtractor) {
        return thenComparing(comparing(keyExtractor));
    }

    default Comparator<T> thenComparingInt(ToIntFunction<? super T> keyExtractor) {
        return thenComparing(comparingInt(keyExtractor));
    }

    default Comparator<T> thenComparingLong(ToLongFunction<? super T> keyExtractor) {
        return thenComparing(comparingLong(keyExtractor));
    }

    default Comparator<T> thenComparingDouble(ToDoubleFunction<? super T> keyExtractor) {
        throw ModelStuck.unsupported("Comparator.thenComparingDouble");
    }

    public static <T extends Comparable<? super T>> Comparator<T> reverseOrder() {
        return Collections.reverseOrder();
    }

    @SuppressWarnings("unchecked")
    public static <T extends Comparable<? super T>> Comparator<T> naturalOrder() {
        return (Comparator<T>) Collections.NaturalOrder.INSTANCE;
    }

    public static <T> Comparator<T> nullsFirst(Comparator<? super T> comparator) {
        return new Collections.NullComparator<>(true, comparator);
    }

    public static <T> Comparator<T> nullsLast(Comparator<? super T> comparator) {
        return new Collections.NullComparator<>(false, comparator);
    }

    public static <T, U> Comparator<T> comparing(Function<? super T, ? extends U> keyExtractor, Comparator<? super U> keyComparator) {
        if (keyExtractor == null || keyComparator == null) throw new NullPointerException();
        return (Comparator<T> & java.io.Serializable)
            (c1, c2) -> keyComparator.compare(keyExtractor.apply(c1), keyExtractor.apply(c2));
    }

    public static <T, U extends Comparable<? super U>> Comparator<T> comparing(Function<? super T, ? extends U> keyExtractor) {
        if (keyExtractor == null) throw new NullPointerException();
        return (Comparator<T> & java.io.Serializable)
            (c1, c2) -> keyExtractor.apply(c1).compareTo(keyExtractor.apply(c2));
    }

    public static <T> Comparator<T> comparingInt(ToIntFunction<? super T> keyExtractor) {
        if (keyExtractor == null) throw new NullPointerException();
        return (Comparator<T> & java.io.Serializable) (c1, c2) -> {
            int x = keyExtractor.applyAsInt(c1), y = keyExtractor.applyAsInt(c2);
            return (x < y) ? -1 : ((x == y) ? 0 : 1);
        };
    }

    public static <T> Comparator<T> comparingLong(ToLongFunction<? super T> keyExtractor) {
        if (keyExtractor == null) throw new NullPointerException();
        return (Comparator<T> & java.io.Serializable) (c1, c2) -> {
            long x = keyExtractor.applyAsLong(c1), y = keyExtractor.applyAsLong(c2);
            return (x < y) ? -1 : ((x == y) ? 0 : 1);
        };
    }

    public static <T> Comparator<T> comparingDouble(ToDoubleFunction<? super T> keyExtractor) {
        throw ModelStuck.unsupported("Comparator.comparingDouble");
    }
}

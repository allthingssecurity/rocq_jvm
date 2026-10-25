/*
 * rocq-jvm model of java.util.function.BinaryOperator (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

import java.util.Comparator;

@FunctionalInterface
public interface BinaryOperator<T> extends BiFunction<T, T, T> {
    /** Javadoc: returns the lesser of two elements (the first one when they compare equal). */
    public static <T> BinaryOperator<T> minBy(Comparator<? super T> comparator) {
        if (comparator == null) throw new NullPointerException();
        return (a, b) -> comparator.compare(a, b) <= 0 ? a : b;
    }

    /** Javadoc: returns the greater of two elements (the first one when they compare equal). */
    public static <T> BinaryOperator<T> maxBy(Comparator<? super T> comparator) {
        if (comparator == null) throw new NullPointerException();
        return (a, b) -> comparator.compare(a, b) >= 0 ? a : b;
    }
}

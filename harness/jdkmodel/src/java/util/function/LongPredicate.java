/*
 * rocq-jvm model of java.util.function.LongPredicate (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface LongPredicate {
    boolean test(long value);

    default LongPredicate and(LongPredicate other) {
        if (other == null) throw new NullPointerException();
        return (value) -> test(value) && other.test(value);
    }

    default LongPredicate negate() {
        return (value) -> !test(value);
    }

    default LongPredicate or(LongPredicate other) {
        if (other == null) throw new NullPointerException();
        return (value) -> test(value) || other.test(value);
    }
}

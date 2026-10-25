/*
 * rocq-jvm model of java.util.function.IntPredicate (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface IntPredicate {
    boolean test(int value);

    default IntPredicate and(IntPredicate other) {
        if (other == null) throw new NullPointerException();
        return (value) -> test(value) && other.test(value);
    }

    default IntPredicate negate() {
        return (value) -> !test(value);
    }

    default IntPredicate or(IntPredicate other) {
        if (other == null) throw new NullPointerException();
        return (value) -> test(value) || other.test(value);
    }
}

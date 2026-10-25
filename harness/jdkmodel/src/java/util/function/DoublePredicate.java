/*
 * rocq-jvm model of java.util.function.DoublePredicate (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface DoublePredicate {
    boolean test(double value);

    default DoublePredicate and(DoublePredicate other) {
        if (other == null) throw new NullPointerException();
        return (value) -> test(value) && other.test(value);
    }

    default DoublePredicate negate() {
        return (value) -> !test(value);
    }

    default DoublePredicate or(DoublePredicate other) {
        if (other == null) throw new NullPointerException();
        return (value) -> test(value) || other.test(value);
    }
}

/*
 * rocq-jvm model of java.util.function.DoubleUnaryOperator (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface DoubleUnaryOperator {
    double applyAsDouble(double operand);

    default DoubleUnaryOperator compose(DoubleUnaryOperator before) {
        if (before == null) throw new NullPointerException();
        return (double v) -> applyAsDouble(before.applyAsDouble(v));
    }

    default DoubleUnaryOperator andThen(DoubleUnaryOperator after) {
        if (after == null) throw new NullPointerException();
        return (double t) -> after.applyAsDouble(applyAsDouble(t));
    }

    static DoubleUnaryOperator identity() {
        return t -> t;
    }
}

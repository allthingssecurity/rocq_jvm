/*
 * rocq-jvm model of java.util.function.IntUnaryOperator (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface IntUnaryOperator {
    int applyAsInt(int operand);

    default IntUnaryOperator compose(IntUnaryOperator before) {
        if (before == null) throw new NullPointerException();
        return (int v) -> applyAsInt(before.applyAsInt(v));
    }

    default IntUnaryOperator andThen(IntUnaryOperator after) {
        if (after == null) throw new NullPointerException();
        return (int t) -> after.applyAsInt(applyAsInt(t));
    }

    static IntUnaryOperator identity() {
        return t -> t;
    }
}

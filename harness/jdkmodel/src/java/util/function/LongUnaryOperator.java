/*
 * rocq-jvm model of java.util.function.LongUnaryOperator (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface LongUnaryOperator {
    long applyAsLong(long operand);

    default LongUnaryOperator compose(LongUnaryOperator before) {
        if (before == null) throw new NullPointerException();
        return (long v) -> applyAsLong(before.applyAsLong(v));
    }

    default LongUnaryOperator andThen(LongUnaryOperator after) {
        if (after == null) throw new NullPointerException();
        return (long t) -> after.applyAsLong(applyAsLong(t));
    }

    static LongUnaryOperator identity() {
        return t -> t;
    }
}

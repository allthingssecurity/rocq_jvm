/*
 * rocq-jvm model of java.util.function.DoubleConsumer (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface DoubleConsumer {
    void accept(double value);

    default DoubleConsumer andThen(DoubleConsumer after) {
        if (after == null) throw new NullPointerException();
        return (double t) -> { accept(t); after.accept(t); };
    }
}

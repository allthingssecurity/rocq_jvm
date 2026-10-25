/*
 * rocq-jvm model of java.util.function.IntConsumer (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface IntConsumer {
    void accept(int value);

    default IntConsumer andThen(IntConsumer after) {
        if (after == null) throw new NullPointerException();
        return (int t) -> { accept(t); after.accept(t); };
    }
}

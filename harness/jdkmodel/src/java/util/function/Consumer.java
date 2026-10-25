/*
 * rocq-jvm model of java.util.function.Consumer (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface Consumer<T> {
    void accept(T t);

    default Consumer<T> andThen(Consumer<? super T> after) {
        if (after == null) throw new NullPointerException();
        return (T t) -> { accept(t); after.accept(t); };
    }
}

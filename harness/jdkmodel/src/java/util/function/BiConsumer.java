/*
 * rocq-jvm model of java.util.function.BiConsumer (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface BiConsumer<T, U> {
    void accept(T t, U u);

    default BiConsumer<T, U> andThen(BiConsumer<? super T, ? super U> after) {
        if (after == null) throw new NullPointerException();
        return (l, r) -> {
            accept(l, r);
            after.accept(l, r);
        };
    }
}

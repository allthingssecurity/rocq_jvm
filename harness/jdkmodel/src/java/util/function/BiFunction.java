/*
 * rocq-jvm model of java.util.function.BiFunction (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface BiFunction<T, U, R> {
    R apply(T t, U u);

    default <V> BiFunction<T, U, V> andThen(Function<? super R, ? extends V> after) {
        if (after == null) throw new NullPointerException();
        return (T t, U u) -> after.apply(apply(t, u));
    }
}

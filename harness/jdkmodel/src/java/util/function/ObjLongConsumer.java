/*
 * rocq-jvm model of java.util.function.ObjLongConsumer (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface ObjLongConsumer<T> {
    void accept(T t, long value);
}

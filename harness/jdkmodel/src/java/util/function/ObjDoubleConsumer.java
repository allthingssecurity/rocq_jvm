/*
 * rocq-jvm model of java.util.function.ObjDoubleConsumer (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface ObjDoubleConsumer<T> {
    void accept(T t, double value);
}

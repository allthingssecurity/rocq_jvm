/*
 * rocq-jvm model of java.util.function.Predicate (clean-room, Apache-2.0): written from the Javadoc
 * (composed functions evaluate in the documented order; null arguments of the combinators throw
 * NullPointerException when the combinator is called).
 */
package java.util.function;

@FunctionalInterface
public interface Predicate<T> {
    boolean test(T t);

    default Predicate<T> and(Predicate<? super T> other) {
        if (other == null) throw new NullPointerException();
        return (t) -> test(t) && other.test(t);
    }

    default Predicate<T> negate() {
        return (t) -> !test(t);
    }

    default Predicate<T> or(Predicate<? super T> other) {
        if (other == null) throw new NullPointerException();
        return (t) -> test(t) || other.test(t);
    }

    /** Javadoc: tests Objects.equals(targetRef, object); a null target tests for null. */
    static <T> Predicate<T> isEqual(Object targetRef) {
        return (null == targetRef)
                ? object -> object == null
                : object -> targetRef.equals(object);
    }

    /** Javadoc: the negation of the target (target.negate()). */
    @SuppressWarnings("unchecked")
    static <T> Predicate<T> not(Predicate<? super T> target) {
        if (target == null) throw new NullPointerException();
        return (Predicate<T>) target.negate();
    }
}

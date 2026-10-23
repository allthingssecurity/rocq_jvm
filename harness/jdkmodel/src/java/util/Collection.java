/*
 * rocq-jvm model of java.util.Collection (clean-room, Apache-2.0).
 * Only the default methods that the Javadoc specifies by an "implementation requirements"
 * paragraph are given; stream()/spliterator()/parallelStream()/toArray(IntFunction) are not
 * modelled (calls to them are STUCK in the machine).
 */
package java.util;

import java.util.function.Consumer;
import java.util.function.Predicate;

public interface Collection<E> extends Iterable<E> {
    int size();
    boolean isEmpty();
    boolean contains(Object o);
    Iterator<E> iterator();
    Object[] toArray();
    <T> T[] toArray(T[] a);
    boolean add(E e);
    boolean remove(Object o);
    boolean containsAll(Collection<?> c);
    boolean addAll(Collection<? extends E> c);
    boolean removeAll(Collection<?> c);
    boolean retainAll(Collection<?> c);
    void clear();
    boolean equals(Object o);
    int hashCode();

    /** Javadoc (Collection.removeIf): iterates with iterator() and removes matching elements
     *  with Iterator.remove. */
    default boolean removeIf(Predicate<? super E> filter) {
        if (filter == null) throw new NullPointerException();
        boolean removed = false;
        Iterator<E> it = iterator();
        while (it.hasNext()) {
            if (filter.test(it.next())) {
                it.remove();
                removed = true;
            }
        }
        return removed;
    }

    /** Iterable.forEach, re-declared here because java.lang.Iterable is not a loaded class in
     *  the machine (Javadoc of Iterable.forEach: for (T t : this) action.accept(t)). */
    default void forEach(Consumer<? super E> action) {
        if (action == null) throw new NullPointerException();
        Iterator<E> it = iterator();
        while (it.hasNext()) action.accept(it.next());
    }
}

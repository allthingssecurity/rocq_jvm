/*
 * rocq-jvm model of java.util.Collection (clean-room, Apache-2.0).
 * Only the default methods that the Javadoc specifies by an "implementation requirements"
 * paragraph are given; spliterator()/toArray(IntFunction) are not modelled (calls to them are
 * STUCK in the machine), parallelStream() is STUCK.
 * stream() builds a model pipeline (java.util.stream) over the collection's iterator, with the
 * characteristics of the JDK spliterator of each model collection class (SIZED / ORDERED /
 * DISTINCT / SORTED); a collection class not listed below is STUCK.
 */
package java.util;

import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.stream.ModelStreams;
import java.util.stream.Stream;

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

    /**
     * Javadoc: a sequential Stream with this collection as its source (the JDK default is
     * StreamSupport.stream(spliterator(), false); the unmodifiable and synchronized wrappers
     * return the wrapped collection's stream()). The source is bound at the first traversal.
     */
    @SuppressWarnings("unchecked")
    default Stream<E> stream() {
        String n = getClass().getName();
        if (n.equals("java.util.Collections$UnmodifiableCollection") || n.equals("java.util.Collections$UnmodifiableSet")
            || n.equals("java.util.Collections$UnmodifiableList") || n.equals("java.util.Collections$UnmodifiableRandomAccessList")) {
            return (Stream<E>) ((Collections.UnmodifiableCollection<E>) this).c.stream();
        }
        if (n.equals("java.util.Collections$SynchronizedCollection") || n.equals("java.util.Collections$SynchronizedSet")
            || n.equals("java.util.Collections$SynchronizedList")) {
            return ((Collections.SynchronizedCollection<E>) this).c.stream();
        }
        if (n.equals("java.util.Collections$UnmodifiableMap$UnmodifiableEntrySet")) {
            // the wrapped set's characteristics; the entries are wrapped by this set's iterator
            int info = streamInfo(((Collections.UnmodifiableCollection<E>) this).c);
            if (info < 0) throw ModelStuck.unsupported("Collection.stream of " + n);
            return ModelStreams.ofCollection(this, info & 15, info >> 4, null);
        }
        int info = streamInfo(this);
        if (info < 0) throw ModelStuck.unsupported("Collection.stream of " + n);
        java.util.function.IntSupplier mod = null;
        if (n.equals("java.util.ArrayList")) {
            AbstractList<?> l = (AbstractList<?>) this;
            mod = () -> l.modCount;
        } else if (n.equals("java.util.HashSet")) {
            HashMap<?, ?> m = ((HashSet<?>) this).map;
            mod = () -> m.modCount;
        }
        return ModelStreams.ofCollection(this, info & 15, info >> 4, mod);
    }

    /**
     * The characteristics (low 4 bits) and traversal kind (<< 4) of the JDK spliterator of a model
     * collection class, or -1 when the class is not known.
     */
    private static int streamInfo(Collection<?> c) {
        final int S = ModelStreams.SIZED, O = ModelStreams.ORDERED, D = ModelStreams.DISTINCT, SO = ModelStreams.SORTED;
        final int ITER = ModelStreams.ITER << 4, GUARD = ModelStreams.GUARD << 4;
        String n = c.getClass().getName();
        switch (n) {
            case "java.util.ArrayList": return S | O | GUARD;
            case "java.util.Arrays$ArrayList": return S | O | ITER;
            case "java.util.ArrayDeque": return S | O | GUARD;
            case "java.util.HashSet": return S | D | GUARD;
            case "java.util.LinkedHashSet": return S | O | D | ITER;
            case "java.util.HashMap$KeySet": return S | D | GUARD;
            case "java.util.HashMap$Values": return S | GUARD;
            case "java.util.HashMap$EntrySet": return S | D | GUARD;
            case "java.util.LinkedHashMap$LinkedKeySet": return S | O | D | ITER;
            case "java.util.LinkedHashMap$LinkedValues": return S | O | ITER;
            case "java.util.LinkedHashMap$LinkedEntrySet": return S | O | D | ITER;
            case "java.util.TreeSet":
            case "java.util.TreeMap$KeySet":
                return S | O | D | (((SortedSet<?>) c).comparator() == null ? SO : 0) | GUARD;
            case "java.util.TreeMap$Values": return S | O | GUARD;
            case "java.util.TreeMap$EntrySet": return S | O | D | GUARD;
            case "java.util.AbstractMap$KeyView": return S | D | ITER;
            case "java.util.AbstractMap$ValueView": return S | ITER;
            case "java.util.Collections$EmptyList":
            case "java.util.Collections$EmptySet":
                return S | ITER;
            case "java.util.Collections$SingletonList":
            case "java.util.Collections$SingletonSet":
                return S | O | D | ITER;
            case "java.util.stream.StreamList": return S | O | ITER;
            default: return -1;
        }
    }

    default Stream<E> parallelStream() {
        throw ModelStuck.unsupported("Collection.parallelStream");
    }
}

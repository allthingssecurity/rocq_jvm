/* rocq-jvm model of java.util.Set (clean-room, Apache-2.0). Set.of/copyOf: ImmutableCollections. */
package java.util;

public interface Set<E> extends Collection<E> {
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
    boolean retainAll(Collection<?> c);
    boolean removeAll(Collection<?> c);
    void clear();
    boolean equals(Object o);
    int hashCode();

    @SuppressWarnings("unchecked")
    static <E> Set<E> of() {
        return (Set<E>) ImmutableCollections.EMPTY_SET;
    }
    static <E> Set<E> of(E e1) {
        return new ImmutableCollections.Set12<>(e1);
    }
    static <E> Set<E> of(E e1, E e2) {
        return new ImmutableCollections.Set12<>(e1, e2);
    }
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E e1, E e2, E e3) {
        return new ImmutableCollections.SetN<>(e1, e2, e3);
    }
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E e1, E e2, E e3, E e4) {
        return new ImmutableCollections.SetN<>(e1, e2, e3, e4);
    }
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E e1, E e2, E e3, E e4, E e5) {
        return new ImmutableCollections.SetN<>(e1, e2, e3, e4, e5);
    }
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E e1, E e2, E e3, E e4, E e5, E e6) {
        return new ImmutableCollections.SetN<>(e1, e2, e3, e4, e5, e6);
    }
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E e1, E e2, E e3, E e4, E e5, E e6, E e7) {
        return new ImmutableCollections.SetN<>(e1, e2, e3, e4, e5, e6, e7);
    }
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E e1, E e2, E e3, E e4, E e5, E e6, E e7, E e8) {
        return new ImmutableCollections.SetN<>(e1, e2, e3, e4, e5, e6, e7, e8);
    }
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E e1, E e2, E e3, E e4, E e5, E e6, E e7, E e8, E e9) {
        return new ImmutableCollections.SetN<>(e1, e2, e3, e4, e5, e6, e7, e8, e9);
    }
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E e1, E e2, E e3, E e4, E e5, E e6, E e7, E e8, E e9, E e10) {
        return new ImmutableCollections.SetN<>(e1, e2, e3, e4, e5, e6, e7, e8, e9, e10);
    }
    @SafeVarargs
    @SuppressWarnings("unchecked")
    static <E> Set<E> of(E... elements) {
        if (elements == null) throw ImmutableCollections.lengthOfNull("elements");
        switch (elements.length) {
            case 0: return (Set<E>) ImmutableCollections.EMPTY_SET;
            case 1: return new ImmutableCollections.Set12<>(elements[0]);
            case 2: return new ImmutableCollections.Set12<>(elements[0], elements[1]);
            default: return new ImmutableCollections.SetN<>(elements);
        }
    }

    @SuppressWarnings("unchecked")
    static <E> Set<E> copyOf(Collection<? extends E> coll) {
        if (coll instanceof ImmutableCollections.AbstractImmutableSet) {
            return (Set<E>) coll;
        } else if (coll == null) {
            throw ImmutableCollections.invokeOnNull("java.util.Collection.isEmpty()", "coll");
        } else if (coll.isEmpty()) {
            return Set.of();
        } else {
            return (Set<E>) Set.of(new HashSet<>(coll).toArray());
        }
    }
}

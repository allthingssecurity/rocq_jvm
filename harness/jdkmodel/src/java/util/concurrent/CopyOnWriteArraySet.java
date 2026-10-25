/*
 * rocq-jvm model of java.util.concurrent.CopyOnWriteArraySet (clean-room, Apache-2.0): a set
 * backed by a CopyOnWriteArrayList (add = addIfAbsent), with the JDK 21 set comparison used by
 * equals and containsAll. spliterator and serialization are STUCK.
 */
package java.util.concurrent;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Iterator;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;

public class CopyOnWriteArraySet<E> extends AbstractSet<E> implements java.io.Serializable {
    private static final long serialVersionUID = 5457747651344034263L;

    private final CopyOnWriteArrayList<E> al;

    public CopyOnWriteArraySet() {
        al = new CopyOnWriteArrayList<E>();
    }

    @SuppressWarnings("unchecked")
    public CopyOnWriteArraySet(Collection<? extends E> c) {
        if (c.getClass() == CopyOnWriteArraySet.class) {
            CopyOnWriteArraySet<E> cc = (CopyOnWriteArraySet<E>) c;
            al = new CopyOnWriteArrayList<E>(cc.al);
        } else {
            al = new CopyOnWriteArrayList<E>();
            al.addAllAbsent(c);
        }
    }

    public int size() {
        return al.size();
    }

    public boolean isEmpty() {
        return al.isEmpty();
    }

    public boolean contains(Object o) {
        return al.contains(o);
    }

    public Object[] toArray() {
        return al.toArray();
    }

    public <T> T[] toArray(T[] a) {
        return al.toArray(a);
    }

    public void clear() {
        al.clear();
    }

    public boolean remove(Object o) {
        return al.remove(o);
    }

    public boolean add(E e) {
        return al.addIfAbsent(e);
    }

    public boolean containsAll(Collection<?> c) {
        return (c instanceof Set) ? compareSets(al.getArray(), (Set<?>) c) >= 0 : al.containsAll(c);
    }

    /** -1: set has an element not in snapshot; 0: equal; 1: snapshot has more. */
    private static int compareSets(Object[] snapshot, Set<?> set) {
        final int len = snapshot.length;
        final boolean[] matched = new boolean[len];
        int j = 0;
        for (Object x : set) {
            boolean found = false;
            for (int i = j; i < len; i++) {
                if (!matched[i] && Objects.equals(x, snapshot[i])) {
                    matched[i] = true;
                    if (i == j) {
                        do {
                            j++;
                        } while (j < len && matched[j]);
                    }
                    found = true;
                    break;
                }
            }
            if (!found) return -1;
        }
        return (j == len) ? 0 : 1;
    }

    public boolean addAll(Collection<? extends E> c) {
        return al.addAllAbsent(c) > 0;
    }

    public boolean removeAll(Collection<?> c) {
        return al.removeAll(c);
    }

    public boolean retainAll(Collection<?> c) {
        return al.retainAll(c);
    }

    public Iterator<E> iterator() {
        return al.iterator();
    }

    public boolean equals(Object o) {
        return (o == this) || ((o instanceof Set) && compareSets(al.getArray(), (Set<?>) o) == 0);
    }

    public boolean removeIf(Predicate<? super E> filter) {
        return al.removeIf(filter);
    }

    public void forEach(Consumer<? super E> action) {
        al.forEach(action);
    }

    public java.util.Spliterator<E> spliterator() {
        throw ModelStuck.unsupported("CopyOnWriteArraySet.spliterator");
    }
}

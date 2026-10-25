/*
 * rocq-jvm model (clean-room, Apache-2.0): the unmodifiable lists returned by Stream.toList()
 * (nulls allowed) and Collectors.toUnmodifiableList() (no nulls), with the observable behaviour of
 * the JDK's immutable lists as documented and established by differential testing: every mutator
 * throws UnsupportedOperationException (even when it would not change the list); a null-hostile
 * list throws NullPointerException from contains/indexOf/lastIndexOf(null); the one- and
 * two-element null-hostile list reports a bad index as IndexOutOfBoundsException
 * ("Index: i Size: n"), the array-backed ones as ArrayIndexOutOfBoundsException; empty lists of
 * each kind are shared instances. subList and toArray into a too-small array are STUCK.
 */
package java.util.stream;

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;
import java.util.RandomAccess;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

final class StreamList<E> extends AbstractCollection<E> implements List<E>, RandomAccess {
    static final int LISTN = 0, LISTN_NULLS = 1, LIST12 = 2;
    static final StreamList<Object> EMPTY_LIST = new StreamList<>(new Object[0], LISTN);
    static final StreamList<Object> EMPTY_LIST_NULLS = new StreamList<>(new Object[0], LISTN_NULLS);

    private final Object[] es;
    private final int mode;

    private StreamList(Object[] es, int mode) {
        this.es = es;
        this.mode = mode;
    }

    /** Stream.toList(): the array is owned by the list. */
    static List<Object> nullsAllowed(Object[] input) {
        if (input.length == 0) return EMPTY_LIST_NULLS;
        return new StreamList<>(input, LISTN_NULLS);
    }

    /** Collectors.toUnmodifiableList(): nulls are rejected. */
    static List<Object> trusted(Object[] input) {
        for (Object o : input) {
            if (o == null) throw new NullPointerException();
        }
        if (input.length == 0) return EMPTY_LIST;
        if (input.length <= 2) return new StreamList<>(input, LIST12);
        return new StreamList<>(input, LISTN);
    }

    private static UnsupportedOperationException uoe() {
        return new UnsupportedOperationException();
    }

    private IndexOutOfBoundsException outOfBounds(int index) {
        return new IndexOutOfBoundsException("Index: " + index + " Size: " + size());
    }

    private static boolean eq(Object a, Object b) {
        return (a == b) || (a != null && a.equals(b));
    }

    public int size() {
        return es.length;
    }

    public boolean isEmpty() {
        return mode == LIST12 ? false : es.length == 0;
    }

    @SuppressWarnings("unchecked")
    public E get(int index) {
        if (mode == LIST12) {
            if (index == 0) return (E) es[0];
            else if (index == 1 && es.length == 2) return (E) es[1];
            throw outOfBounds(index);
        }
        return (E) es[index];
    }

    public int indexOf(Object o) {
        if (mode == LIST12) {
            if (o == null) throw new NullPointerException();
            if (o.equals(es[0])) return 0;
            else if (es.length == 2 && o.equals(es[1])) return 1;
            return -1;
        }
        if (mode == LISTN && o == null) throw new NullPointerException();
        for (int i = 0; i < es.length; i++) {
            if (eq(o, es[i])) return i;
        }
        return -1;
    }

    public int lastIndexOf(Object o) {
        if (mode == LIST12) {
            if (o == null) throw new NullPointerException();
            if (es.length == 2 && o.equals(es[1])) return 1;
            else if (o.equals(es[0])) return 0;
            return -1;
        }
        if (mode == LISTN && o == null) throw new NullPointerException();
        for (int i = es.length - 1; i >= 0; i--) {
            if (eq(o, es[i])) return i;
        }
        return -1;
    }

    public boolean contains(Object o) {
        return indexOf(o) >= 0;
    }

    public Object[] toArray() {
        Object[] r = new Object[es.length];
        for (int i = 0; i < es.length; i++) r[i] = es[i];
        return r;
    }

    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
        int size = es.length;
        if (a.length < size) throw ModelStuckS.unsupported("List.toArray(T[]) into a smaller array (reflection)");
        if (mode == LIST12) {
            a[0] = (T) es[0];
            if (size == 2) a[1] = (T) es[1];
        } else {
            for (int i = 0; i < size; i++) {
                try {
                    a[i] = (T) es[i];
                } catch (ArrayStoreException e) {
                    throw ModelStuckS.unsupported("toArray: System.arraycopy ArrayStoreException message");
                }
            }
        }
        if (a.length > size) a[size] = null;
        return a;
    }

    public Iterator<E> iterator() {
        return new Itr(0, false);
    }

    public ListIterator<E> listIterator() {
        return listIterator(0);
    }

    public ListIterator<E> listIterator(int index) {
        int size = size();
        if (index < 0 || index > size) throw outOfBounds(index);
        return new Itr(index, true);
    }

    private final class Itr implements ListIterator<E> {
        private int cursor;
        private final boolean isListIterator;

        Itr(int cursor, boolean isListIterator) {
            this.cursor = cursor;
            this.isListIterator = isListIterator;
        }

        public boolean hasNext() {
            return cursor != es.length;
        }

        public E next() {
            int i = cursor;
            if (i < 0 || i >= es.length) throw new NoSuchElementException();
            E next = get(i);
            cursor = i + 1;
            return next;
        }

        public void remove() {
            throw uoe();
        }

        public boolean hasPrevious() {
            if (!isListIterator) throw uoe();
            return cursor != 0;
        }

        public E previous() {
            if (!isListIterator) throw uoe();
            int i = cursor - 1;
            if (i < 0 || i >= es.length) throw new NoSuchElementException();
            E previous = get(i);
            cursor = i;
            return previous;
        }

        public int nextIndex() {
            if (!isListIterator) throw uoe();
            return cursor;
        }

        public int previousIndex() {
            if (!isListIterator) throw uoe();
            return cursor - 1;
        }

        public void set(E e) {
            throw uoe();
        }

        public void add(E e) {
            throw uoe();
        }
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof List)) return false;
        Iterator<?> oit = ((List<?>) o).iterator();
        for (int i = 0, s = size(); i < s; i++) {
            if (!oit.hasNext() || !eq(get(i), oit.next())) return false;
        }
        return !oit.hasNext();
    }

    public int hashCode() {
        int hash = 1;
        for (int i = 0, s = size(); i < s; i++) {
            Object e = get(i);
            hash = 31 * hash + (e == null ? 0 : e.hashCode());
        }
        return hash;
    }

    public List<E> subList(int fromIndex, int toIndex) {
        throw ModelStuckS.unsupported("immutable List.subList");
    }

    // ---- mutators ----

    public boolean add(E e) {
        throw uoe();
    }

    public boolean addAll(Collection<? extends E> c) {
        throw uoe();
    }

    public void clear() {
        throw uoe();
    }

    public boolean remove(Object o) {
        throw uoe();
    }

    public boolean removeAll(Collection<?> c) {
        throw uoe();
    }

    public boolean removeIf(Predicate<? super E> filter) {
        throw uoe();
    }

    public boolean retainAll(Collection<?> c) {
        throw uoe();
    }

    public void add(int index, E element) {
        throw uoe();
    }

    public boolean addAll(int index, Collection<? extends E> c) {
        throw uoe();
    }

    public E remove(int index) {
        throw uoe();
    }

    public void replaceAll(UnaryOperator<E> operator) {
        throw uoe();
    }

    public E set(int index, E element) {
        throw uoe();
    }

    public void sort(Comparator<? super E> c) {
        throw uoe();
    }
}

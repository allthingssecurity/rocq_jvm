/*
 * rocq-jvm model of java.util.concurrent.CopyOnWriteArrayList (clean-room, Apache-2.0).
 * Writers hold the list's lock and replace the array; readers and iterators use the array they
 * read (snapshots), as in JDK 21; exceptions and messages follow the JDK. Under the model's
 * sequentially consistent thread layer the volatile array reads/writes are atomic and ordered.
 * Not modelled (STUCK): spliterator, reversed(), clone, serialization, and the bulk operations
 * of sub lists (removeAll/retainAll/removeIf on a subList).
 */
package java.util.concurrent;

import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.RandomAccess;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

public class CopyOnWriteArrayList<E> implements List<E>, RandomAccess, Cloneable, java.io.Serializable {
    private static final long serialVersionUID = 8673264195747942595L;

    final transient Object lock = new Object();

    private transient volatile Object[] array;

    final Object[] getArray() {
        return array;
    }

    final void setArray(Object[] a) {
        array = a;
    }

    static Object[] copy(Object[] a, int newLength) {
        Object[] r = new Object[newLength];
        System.arraycopy(a, 0, r, 0, Math.min(a.length, newLength));
        return r;
    }

    public CopyOnWriteArrayList() {
        setArray(new Object[0]);
    }

    public CopyOnWriteArrayList(Collection<? extends E> c) {
        Object[] es;
        if (c.getClass() == CopyOnWriteArrayList.class) {
            es = ((CopyOnWriteArrayList<?>) c).getArray();
        } else {
            es = c.toArray();
            if (c.getClass() != java.util.ArrayList.class) es = copy(es, es.length);
        }
        setArray(es);
    }

    public CopyOnWriteArrayList(E[] toCopyIn) {
        setArray(copy(toCopyIn, toCopyIn.length));
    }

    public int size() {
        return getArray().length;
    }

    public boolean isEmpty() {
        return size() == 0;
    }

    static int indexOfRange(Object o, Object[] es, int from, int to) {
        if (o == null) {
            for (int i = from; i < to; i++) if (es[i] == null) return i;
        } else {
            for (int i = from; i < to; i++) if (o.equals(es[i])) return i;
        }
        return -1;
    }

    static int lastIndexOfRange(Object o, Object[] es, int from, int to) {
        if (o == null) {
            for (int i = to - 1; i >= from; i--) if (es[i] == null) return i;
        } else {
            for (int i = to - 1; i >= from; i--) if (o.equals(es[i])) return i;
        }
        return -1;
    }

    public boolean contains(Object o) {
        return indexOf(o) >= 0;
    }

    public int indexOf(Object o) {
        Object[] es = getArray();
        return indexOfRange(o, es, 0, es.length);
    }

    public int indexOf(E e, int index) {
        Object[] es = getArray();
        return indexOfRange(e, es, index, es.length);
    }

    public int lastIndexOf(Object o) {
        Object[] es = getArray();
        return lastIndexOfRange(o, es, 0, es.length);
    }

    public int lastIndexOf(E e, int index) {
        Object[] es = getArray();
        return lastIndexOfRange(e, es, 0, index + 1);
    }

    public Object clone() {
        throw ModelStuck.unsupported("CopyOnWriteArrayList.clone");
    }

    public Object[] toArray() {
        Object[] es = getArray();
        return copy(es, es.length);
    }

    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
        Object[] es = getArray();
        int len = es.length;
        if (a.length < len) {
            T[] r = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), len);
            System.arraycopy(es, 0, r, 0, len);
            return r;
        }
        System.arraycopy(es, 0, a, 0, len);
        if (a.length > len) a[len] = null;
        return a;
    }

    @SuppressWarnings("unchecked")
    static <E> E elementAt(Object[] a, int index) {
        return (E) a[index];
    }

    static String outOfBounds(int index, int size) {
        return "Index: " + index + ", Size: " + size;
    }

    public E get(int index) {
        return elementAt(getArray(), index);
    }

    public E getFirst() {
        Object[] es = getArray();
        if (es.length == 0) throw new NoSuchElementException();
        return elementAt(es, 0);
    }

    public E getLast() {
        Object[] es = getArray();
        if (es.length == 0) throw new NoSuchElementException();
        return elementAt(es, es.length - 1);
    }

    public E set(int index, E element) {
        synchronized (lock) {
            Object[] es = getArray();
            E oldValue = elementAt(es, index);
            if (oldValue != element) {
                es = copy(es, es.length);
                es[index] = element;
            }
            setArray(es);
            return oldValue;
        }
    }

    public boolean add(E e) {
        synchronized (lock) {
            Object[] es = getArray();
            int len = es.length;
            es = copy(es, len + 1);
            es[len] = e;
            setArray(es);
            return true;
        }
    }

    public void add(int index, E element) {
        synchronized (lock) {
            Object[] es = getArray();
            int len = es.length;
            if (index > len || index < 0) throw new IndexOutOfBoundsException(outOfBounds(index, len));
            Object[] n = new Object[len + 1];
            System.arraycopy(es, 0, n, 0, index);
            System.arraycopy(es, index, n, index + 1, len - index);
            n[index] = element;
            setArray(n);
        }
    }

    public void addFirst(E e) {
        add(0, e);
    }

    public void addLast(E e) {
        synchronized (lock) {
            add(getArray().length, e);
        }
    }

    public E remove(int index) {
        synchronized (lock) {
            Object[] es = getArray();
            int len = es.length;
            E oldValue = elementAt(es, index);
            Object[] n = new Object[len - 1];
            System.arraycopy(es, 0, n, 0, index);
            System.arraycopy(es, index + 1, n, index, len - index - 1);
            setArray(n);
            return oldValue;
        }
    }

    public E removeFirst() {
        synchronized (lock) {
            if (getArray().length == 0) throw new NoSuchElementException();
            return remove(0);
        }
    }

    public E removeLast() {
        synchronized (lock) {
            int size = getArray().length;
            if (size == 0) throw new NoSuchElementException();
            return remove(size - 1);
        }
    }

    public boolean remove(Object o) {
        Object[] snapshot = getArray();
        int index = indexOfRange(o, snapshot, 0, snapshot.length);
        return index >= 0 && remove(o, snapshot, index);
    }

    /** Remove o, found at [index] of [snapshot]; the array may have changed since. */
    private boolean remove(Object o, Object[] snapshot, int index) {
        synchronized (lock) {
            Object[] current = getArray();
            int len = current.length;
            if (snapshot != current) {
                boolean found = false;
                int prefix = Math.min(index, len);
                for (int i = 0; i < prefix; i++) {
                    if (current[i] != snapshot[i] && Objects.equals(o, current[i])) {
                        index = i;
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    if (index >= len) return false;
                    if (current[index] != o) {
                        index = indexOfRange(o, current, index, len);
                        if (index < 0) return false;
                    }
                }
            }
            Object[] n = new Object[len - 1];
            System.arraycopy(current, 0, n, 0, index);
            System.arraycopy(current, index + 1, n, index, len - index - 1);
            setArray(n);
            return true;
        }
    }

    void removeRange(int fromIndex, int toIndex) {
        synchronized (lock) {
            Object[] es = getArray();
            int len = es.length;
            if (fromIndex < 0 || toIndex > len || toIndex < fromIndex) throw new IndexOutOfBoundsException();
            int newlen = len - (toIndex - fromIndex);
            Object[] n = new Object[newlen];
            System.arraycopy(es, 0, n, 0, fromIndex);
            System.arraycopy(es, toIndex, n, fromIndex, len - toIndex);
            setArray(n);
        }
    }

    public boolean addIfAbsent(E e) {
        Object[] snapshot = getArray();
        return indexOfRange(e, snapshot, 0, snapshot.length) < 0 && addIfAbsent(e, snapshot);
    }

    private boolean addIfAbsent(E e, Object[] snapshot) {
        synchronized (lock) {
            Object[] current = getArray();
            int len = current.length;
            if (snapshot != current) {
                int common = Math.min(snapshot.length, len);
                for (int i = 0; i < common; i++) {
                    if (current[i] != snapshot[i] && Objects.equals(e, current[i])) return false;
                }
                if (indexOfRange(e, current, common, len) >= 0) return false;
            }
            Object[] n = copy(current, len + 1);
            n[len] = e;
            setArray(n);
            return true;
        }
    }

    public boolean containsAll(Collection<?> c) {
        Object[] es = getArray();
        int len = es.length;
        for (Object e : c) {
            if (indexOfRange(e, es, 0, len) < 0) return false;
        }
        return true;
    }

    public boolean removeAll(Collection<?> c) {
        Objects.requireNonNull(c);
        return bulkRemove(e -> c.contains(e));
    }

    public boolean retainAll(Collection<?> c) {
        Objects.requireNonNull(c);
        return bulkRemove(e -> !c.contains(e));
    }

    public int addAllAbsent(Collection<? extends E> c) {
        Object[] cs = c.toArray();
        if (c.getClass() != java.util.ArrayList.class) cs = copy(cs, cs.length);
        if (cs.length == 0) return 0;
        synchronized (lock) {
            Object[] es = getArray();
            int len = es.length;
            int added = 0;
            for (int i = 0; i < cs.length; ++i) {
                Object e = cs[i];
                if (indexOfRange(e, es, 0, len) < 0 && indexOfRange(e, cs, 0, added) < 0) cs[added++] = e;
            }
            if (added > 0) {
                Object[] n = copy(es, len + added);
                System.arraycopy(cs, 0, n, len, added);
                setArray(n);
            }
            return added;
        }
    }

    public void clear() {
        synchronized (lock) {
            setArray(new Object[0]);
        }
    }

    public boolean addAll(Collection<? extends E> c) {
        Object[] cs = (c.getClass() == CopyOnWriteArrayList.class)
            ? ((CopyOnWriteArrayList<?>) c).getArray() : c.toArray();
        if (cs.length == 0) return false;
        synchronized (lock) {
            Object[] es = getArray();
            int len = es.length;
            Object[] n;
            if (len == 0 && (c.getClass() == CopyOnWriteArrayList.class || c.getClass() == java.util.ArrayList.class)) {
                n = cs;
            } else {
                n = copy(es, len + cs.length);
                System.arraycopy(cs, 0, n, len, cs.length);
            }
            setArray(n);
            return true;
        }
    }

    public boolean addAll(int index, Collection<? extends E> c) {
        Object[] cs = c.toArray();
        synchronized (lock) {
            Object[] es = getArray();
            int len = es.length;
            if (index > len || index < 0) throw new IndexOutOfBoundsException(outOfBounds(index, len));
            if (cs.length == 0) return false;
            Object[] n = new Object[len + cs.length];
            System.arraycopy(es, 0, n, 0, index);
            System.arraycopy(es, index, n, index + cs.length, len - index);
            System.arraycopy(cs, 0, n, index, cs.length);
            setArray(n);
            return true;
        }
    }

    public void forEach(Consumer<? super E> action) {
        Objects.requireNonNull(action);
        for (Object x : getArray()) {
            @SuppressWarnings("unchecked") E e = (E) x;
            action.accept(e);
        }
    }

    public boolean removeIf(Predicate<? super E> filter) {
        Objects.requireNonNull(filter);
        return bulkRemove(filter);
    }

    private boolean bulkRemove(Predicate<? super E> filter) {
        synchronized (lock) {
            return bulkRemove(filter, 0, getArray().length);
        }
    }

    boolean bulkRemove(Predicate<? super E> filter, int i, int end) {
        final Object[] es = getArray();
        for (; i < end && !filter.test(elementAt(es, i)); i++) {
        }
        if (i < end) {
            final int beg = i;
            boolean[] dead = new boolean[end - beg];
            int deleted = 1;
            dead[0] = true;
            for (i = beg + 1; i < end; i++) {
                if (filter.test(elementAt(es, i))) {
                    dead[i - beg] = true;
                    deleted++;
                }
            }
            if (es != getArray()) throw new ConcurrentModificationException();
            final Object[] n = copy(es, es.length - deleted);
            int w = beg;
            for (i = beg; i < end; i++) {
                if (!dead[i - beg]) n[w++] = es[i];
            }
            System.arraycopy(es, i, n, w, es.length - i);
            setArray(n);
            return true;
        } else {
            if (es != getArray()) throw new ConcurrentModificationException();
            return false;
        }
    }

    public void replaceAll(UnaryOperator<E> operator) {
        synchronized (lock) {
            replaceAllRange(operator, 0, getArray().length);
        }
    }

    void replaceAllRange(UnaryOperator<E> operator, int i, int end) {
        Objects.requireNonNull(operator);
        Object[] cur = getArray();
        final Object[] es = copy(cur, cur.length);
        for (; i < end; i++) es[i] = operator.apply(elementAt(es, i));
        setArray(es);
    }

    public void sort(Comparator<? super E> c) {
        synchronized (lock) {
            sortRange(c, 0, getArray().length);
        }
    }

    @SuppressWarnings("unchecked")
    void sortRange(Comparator<? super E> c, int i, int end) {
        Object[] cur = getArray();
        final Object[] es = copy(cur, cur.length);
        Arrays.sort(es, i, end, (Comparator<Object>) c);
        setArray(es);
    }

    public String toString() {
        return Arrays.toString(getArray());
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof List)) return false;
        Iterator<?> it = ((List<?>) o).iterator();
        for (Object element : getArray()) {
            if (!it.hasNext() || !Objects.equals(element, it.next())) return false;
        }
        return !it.hasNext();
    }

    static int hashCodeOfRange(Object[] es, int from, int to) {
        int hashCode = 1;
        for (int i = from; i < to; i++) {
            Object x = es[i];
            hashCode = 31 * hashCode + (x == null ? 0 : x.hashCode());
        }
        return hashCode;
    }

    public int hashCode() {
        Object[] es = getArray();
        return hashCodeOfRange(es, 0, es.length);
    }

    public Iterator<E> iterator() {
        return new COWIterator<E>(getArray(), 0);
    }

    public ListIterator<E> listIterator() {
        return new COWIterator<E>(getArray(), 0);
    }

    public ListIterator<E> listIterator(int index) {
        Object[] es = getArray();
        int len = es.length;
        if (index < 0 || index > len) throw new IndexOutOfBoundsException(outOfBounds(index, len));
        return new COWIterator<E>(es, index);
    }

    public java.util.Spliterator<E> spliterator() {
        throw ModelStuck.unsupported("CopyOnWriteArrayList.spliterator");
    }

    public List<E> reversed() {
        throw ModelStuck.unsupported("CopyOnWriteArrayList.reversed");
    }

    static final class COWIterator<E> implements ListIterator<E> {
        private final Object[] snapshot;
        private int cursor;

        COWIterator(Object[] es, int initialCursor) {
            cursor = initialCursor;
            snapshot = es;
        }

        public boolean hasNext() {
            return cursor < snapshot.length;
        }

        public boolean hasPrevious() {
            return cursor > 0;
        }

        @SuppressWarnings("unchecked")
        public E next() {
            if (!hasNext()) throw new NoSuchElementException();
            return (E) snapshot[cursor++];
        }

        @SuppressWarnings("unchecked")
        public E previous() {
            if (!hasPrevious()) throw new NoSuchElementException();
            return (E) snapshot[--cursor];
        }

        public int nextIndex() {
            return cursor;
        }

        public int previousIndex() {
            return cursor - 1;
        }

        public void remove() {
            throw new UnsupportedOperationException();
        }

        public void set(E e) {
            throw new UnsupportedOperationException();
        }

        public void add(E e) {
            throw new UnsupportedOperationException();
        }

        public void forEachRemaining(Consumer<? super E> action) {
            Objects.requireNonNull(action);
            final int size = snapshot.length;
            int i = cursor;
            cursor = size;
            for (; i < size; i++) action.accept(elementAt(snapshot, i));
        }
    }

    public List<E> subList(int fromIndex, int toIndex) {
        synchronized (lock) {
            Object[] es = getArray();
            int len = es.length;
            int size = toIndex - fromIndex;
            if (fromIndex < 0 || toIndex > len || size < 0) throw new IndexOutOfBoundsException();
            return new COWSubList(es, fromIndex, size);
        }
    }

    private class COWSubList implements List<E>, RandomAccess {
        private final int offset;
        private int size;
        private Object[] expectedArray;

        COWSubList(Object[] es, int offset, int size) {
            expectedArray = es;
            this.offset = offset;
            this.size = size;
        }

        private void checkForComodification() {
            if (getArray() != expectedArray) throw new ConcurrentModificationException();
        }

        private Object[] getArrayChecked() {
            Object[] a = getArray();
            if (a != expectedArray) throw new ConcurrentModificationException();
            return a;
        }

        private void rangeCheck(int index) {
            if (index < 0 || index >= size) throw new IndexOutOfBoundsException(outOfBounds(index, size));
        }

        private void rangeCheckForAdd(int index) {
            if (index < 0 || index > size) throw new IndexOutOfBoundsException(outOfBounds(index, size));
        }

        public Object[] toArray() {
            final Object[] es;
            final int off;
            final int sz;
            synchronized (lock) {
                es = getArrayChecked();
                off = this.offset;
                sz = this.size;
            }
            Object[] r = new Object[sz];
            System.arraycopy(es, off, r, 0, sz);
            return r;
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            final Object[] es;
            final int off;
            final int sz;
            synchronized (lock) {
                es = getArrayChecked();
                off = this.offset;
                sz = this.size;
            }
            if (a.length < sz) {
                T[] r = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), sz);
                System.arraycopy(es, off, r, 0, sz);
                return r;
            }
            System.arraycopy(es, off, a, 0, sz);
            if (a.length > sz) a[sz] = null;
            return a;
        }

        public int indexOf(Object o) {
            final Object[] es;
            final int off;
            final int sz;
            synchronized (lock) {
                es = getArrayChecked();
                off = this.offset;
                sz = this.size;
            }
            int i = indexOfRange(o, es, off, off + sz);
            return (i == -1) ? -1 : i - off;
        }

        public int lastIndexOf(Object o) {
            final Object[] es;
            final int off;
            final int sz;
            synchronized (lock) {
                es = getArrayChecked();
                off = this.offset;
                sz = this.size;
            }
            int i = lastIndexOfRange(o, es, off, off + sz);
            return (i == -1) ? -1 : i - off;
        }

        public boolean contains(Object o) {
            return indexOf(o) >= 0;
        }

        public boolean containsAll(Collection<?> c) {
            final Object[] es;
            final int off;
            final int sz;
            synchronized (lock) {
                es = getArrayChecked();
                off = this.offset;
                sz = this.size;
            }
            for (Object o : c) {
                if (indexOfRange(o, es, off, off + sz) < 0) return false;
            }
            return true;
        }

        public boolean isEmpty() {
            return size() == 0;
        }

        public String toString() {
            return Arrays.toString(toArray());
        }

        public int hashCode() {
            final Object[] es;
            final int off;
            final int sz;
            synchronized (lock) {
                es = getArrayChecked();
                off = this.offset;
                sz = this.size;
            }
            return hashCodeOfRange(es, off, off + sz);
        }

        public boolean equals(Object o) {
            if (o == this) return true;
            if (!(o instanceof List)) return false;
            Iterator<?> it = ((List<?>) o).iterator();
            final Object[] es;
            final int off;
            final int sz;
            synchronized (lock) {
                es = getArrayChecked();
                off = this.offset;
                sz = this.size;
            }
            for (int i = off, end = off + sz; i < end; i++) {
                if (!it.hasNext() || !Objects.equals(es[i], it.next())) return false;
            }
            return !it.hasNext();
        }

        public E set(int index, E element) {
            synchronized (lock) {
                rangeCheck(index);
                checkForComodification();
                E x = CopyOnWriteArrayList.this.set(offset + index, element);
                expectedArray = getArray();
                return x;
            }
        }

        public E get(int index) {
            synchronized (lock) {
                rangeCheck(index);
                checkForComodification();
                return CopyOnWriteArrayList.this.get(offset + index);
            }
        }

        public int size() {
            synchronized (lock) {
                checkForComodification();
                return size;
            }
        }

        public boolean add(E element) {
            synchronized (lock) {
                checkForComodification();
                CopyOnWriteArrayList.this.add(offset + size, element);
                expectedArray = getArray();
                size++;
            }
            return true;
        }

        public void add(int index, E element) {
            synchronized (lock) {
                checkForComodification();
                rangeCheckForAdd(index);
                CopyOnWriteArrayList.this.add(offset + index, element);
                expectedArray = getArray();
                size++;
            }
        }

        public boolean addAll(Collection<? extends E> c) {
            synchronized (lock) {
                final Object[] oldArray = getArrayChecked();
                boolean modified = CopyOnWriteArrayList.this.addAll(offset + size, c);
                size += (expectedArray = getArray()).length - oldArray.length;
                return modified;
            }
        }

        public boolean addAll(int index, Collection<? extends E> c) {
            synchronized (lock) {
                rangeCheckForAdd(index);
                final Object[] oldArray = getArrayChecked();
                boolean modified = CopyOnWriteArrayList.this.addAll(offset + index, c);
                size += (expectedArray = getArray()).length - oldArray.length;
                return modified;
            }
        }

        public void clear() {
            synchronized (lock) {
                checkForComodification();
                removeRange(offset, offset + size);
                expectedArray = getArray();
                size = 0;
            }
        }

        public E remove(int index) {
            synchronized (lock) {
                rangeCheck(index);
                checkForComodification();
                E result = CopyOnWriteArrayList.this.remove(offset + index);
                expectedArray = getArray();
                size--;
                return result;
            }
        }

        public boolean remove(Object o) {
            synchronized (lock) {
                checkForComodification();
                int index = indexOf(o);
                if (index == -1) return false;
                remove(index);
                return true;
            }
        }

        public Iterator<E> iterator() {
            return listIterator(0);
        }

        public ListIterator<E> listIterator() {
            return listIterator(0);
        }

        public ListIterator<E> listIterator(int index) {
            synchronized (lock) {
                checkForComodification();
                rangeCheckForAdd(index);
                return new COWSubListIterator<E>(CopyOnWriteArrayList.this, index, offset, size);
            }
        }

        public List<E> subList(int fromIndex, int toIndex) {
            synchronized (lock) {
                checkForComodification();
                if (fromIndex < 0 || toIndex > size || fromIndex > toIndex) throw new IndexOutOfBoundsException();
                return new COWSubList(expectedArray, fromIndex + offset, toIndex - fromIndex);
            }
        }

        public void forEach(Consumer<? super E> action) {
            Objects.requireNonNull(action);
            int i, end;
            final Object[] es;
            synchronized (lock) {
                es = getArrayChecked();
                i = offset;
                end = i + size;
            }
            for (; i < end; i++) action.accept(elementAt(es, i));
        }

        public void replaceAll(UnaryOperator<E> operator) {
            synchronized (lock) {
                checkForComodification();
                replaceAllRange(operator, offset, offset + size);
                expectedArray = getArray();
            }
        }

        public void sort(Comparator<? super E> c) {
            synchronized (lock) {
                checkForComodification();
                sortRange(c, offset, offset + size);
                expectedArray = getArray();
            }
        }

        public boolean removeAll(Collection<?> c) {
            throw ModelStuck.unsupported("CopyOnWriteArrayList.subList().removeAll");
        }

        public boolean retainAll(Collection<?> c) {
            throw ModelStuck.unsupported("CopyOnWriteArrayList.subList().retainAll");
        }

        public boolean removeIf(Predicate<? super E> filter) {
            throw ModelStuck.unsupported("CopyOnWriteArrayList.subList().removeIf");
        }
    }

    private static class COWSubListIterator<E> implements ListIterator<E> {
        private final ListIterator<E> it;
        private final int offset;
        private final int size;

        COWSubListIterator(List<E> l, int index, int offset, int size) {
            this.offset = offset;
            this.size = size;
            it = l.listIterator(index + offset);
        }

        public boolean hasNext() {
            return nextIndex() < size;
        }

        public E next() {
            if (hasNext()) return it.next();
            throw new NoSuchElementException();
        }

        public boolean hasPrevious() {
            return previousIndex() >= 0;
        }

        public E previous() {
            if (hasPrevious()) return it.previous();
            throw new NoSuchElementException();
        }

        public int nextIndex() {
            return it.nextIndex() - offset;
        }

        public int previousIndex() {
            return it.previousIndex() - offset;
        }

        public void remove() {
            throw new UnsupportedOperationException();
        }

        public void set(E e) {
            throw new UnsupportedOperationException();
        }

        public void add(E e) {
            throw new UnsupportedOperationException();
        }

        public void forEachRemaining(Consumer<? super E> action) {
            Objects.requireNonNull(action);
            while (hasNext()) action.accept(it.next());
        }
    }
}

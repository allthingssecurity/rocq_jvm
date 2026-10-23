/*
 * rocq-jvm model of java.util.AbstractList (clean-room, Apache-2.0).
 * Written from the Javadoc: iterators are implemented on top of get/set/add/remove(int) and
 * use the protected modCount field for fail-fast ConcurrentModificationException.
 * subList is not modelled (STUCK).
 */
package java.util;

public abstract class AbstractList<E> extends AbstractCollection<E> implements List<E> {
    protected transient int modCount = 0;

    protected AbstractList() {
    }

    public boolean add(E e) {
        add(size(), e);
        return true;
    }

    public abstract E get(int index);

    public E set(int index, E element) {
        throw new UnsupportedOperationException();
    }

    public void add(int index, E element) {
        throw new UnsupportedOperationException();
    }

    public E remove(int index) {
        throw new UnsupportedOperationException();
    }

    public int indexOf(Object o) {
        ListIterator<E> it = listIterator();
        if (o == null) {
            while (it.hasNext()) {
                if (it.next() == null) return it.previousIndex();
            }
        } else {
            while (it.hasNext()) {
                if (o.equals(it.next())) return it.previousIndex();
            }
        }
        return -1;
    }

    public int lastIndexOf(Object o) {
        ListIterator<E> it = listIterator(size());
        if (o == null) {
            while (it.hasPrevious()) {
                if (it.previous() == null) return it.nextIndex();
            }
        } else {
            while (it.hasPrevious()) {
                if (o.equals(it.previous())) return it.nextIndex();
            }
        }
        return -1;
    }

    public void clear() {
        removeRange(0, size());
    }

    public boolean addAll(int index, Collection<? extends E> c) {
        checkPositionForAdd(index);
        boolean changed = false;
        for (E e : c) {
            add(index++, e);
            changed = true;
        }
        return changed;
    }

    public Iterator<E> iterator() {
        return new Itr();
    }

    public ListIterator<E> listIterator() {
        return listIterator(0);
    }

    public ListIterator<E> listIterator(final int index) {
        checkPositionForAdd(index);
        return new ListItr(index);
    }

    public List<E> subList(int fromIndex, int toIndex) {
        throw ModelStuck.unsupported("AbstractList.subList");
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof List)) return false;
        ListIterator<E> a = listIterator();
        ListIterator<?> b = ((List<?>) o).listIterator();
        while (a.hasNext() && b.hasNext()) {
            E x = a.next();
            Object y = b.next();
            if (!(x == null ? y == null : x.equals(y))) return false;
        }
        return !(a.hasNext() || b.hasNext());
    }

    public int hashCode() {
        int h = 1;
        for (E e : this) h = 31 * h + (e == null ? 0 : e.hashCode());
        return h;
    }

    protected void removeRange(int fromIndex, int toIndex) {
        ListIterator<E> it = listIterator(fromIndex);
        for (int i = 0, n = toIndex - fromIndex; i < n; i++) {
            it.next();
            it.remove();
        }
    }

    private void checkPositionForAdd(int index) {
        if (index < 0 || index > size()) throw new IndexOutOfBoundsException();
    }

    /** Iterator over get(int); fail-fast through modCount. */
    private class Itr implements Iterator<E> {
        int cursor = 0;
        int lastRet = -1;
        int expectedModCount = modCount;

        Itr() {
        }

        public boolean hasNext() {
            return cursor != size();
        }

        public E next() {
            checkComod();
            try {
                int i = cursor;
                E e = get(i);
                lastRet = i;
                cursor = i + 1;
                return e;
            } catch (IndexOutOfBoundsException ex) {
                checkComod();
                throw new NoSuchElementException(ex);
            }
        }

        public void remove() {
            if (lastRet < 0) throw new IllegalStateException();
            checkComod();
            try {
                AbstractList.this.remove(lastRet);
                if (lastRet < cursor) cursor--;
                lastRet = -1;
                expectedModCount = modCount;
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
        }

        final void checkComod() {
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
        }
    }

    private class ListItr extends Itr implements ListIterator<E> {
        ListItr(int index) {
            cursor = index;
        }

        public boolean hasPrevious() {
            return cursor != 0;
        }

        public E previous() {
            checkComod();
            try {
                int i = cursor - 1;
                E e = get(i);
                lastRet = i;
                cursor = i;
                return e;
            } catch (IndexOutOfBoundsException ex) {
                checkComod();
                throw new NoSuchElementException(ex);
            }
        }

        public int nextIndex() {
            return cursor;
        }

        public int previousIndex() {
            return cursor - 1;
        }

        public void set(E e) {
            if (lastRet < 0) throw new IllegalStateException();
            checkComod();
            try {
                AbstractList.this.set(lastRet, e);
                expectedModCount = modCount;
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
        }

        public void add(E e) {
            checkComod();
            try {
                int i = cursor;
                AbstractList.this.add(i, e);
                lastRet = -1;
                cursor = i + 1;
                expectedModCount = modCount;
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
        }
    }
}

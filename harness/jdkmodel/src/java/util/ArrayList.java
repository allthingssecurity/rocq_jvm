/*
 * rocq-jvm model of java.util.ArrayList (clean-room, Apache-2.0).
 *
 * Written from the Javadoc and from the documented, observable behaviour of JDK 21:
 * - index checks: get/set/remove(int) throw IndexOutOfBoundsException for index < 0 or
 *   index >= size; add(int,E)/addAll(int,..)/listIterator(int) for index < 0 or index > size;
 *   new ArrayList(-1) throws IllegalArgumentException;
 * - modCount (fail-fast iterators): incremented by add/add(int)/remove(int)/a successful
 *   remove(Object)/clear/addAll (also when the argument is empty)/a removeAll or retainAll or
 *   removeIf that removes something/trimToSize/replaceAll/ensureCapacity when it grows;
 * - capacity: a list made by new ArrayList() gets capacity max(10, needed) on its first growth;
 *   otherwise growth is to max(needed, old + old/2).  The capacity is observable only through
 *   ensureCapacity's modCount increment.
 * - exception messages as JDK 21 (Objects.checkIndex for get/set/remove, "Index: i, Size: n" for
 *   positions, "From Index: a > To Index: b" for removeRange);
 * - subList: the JDK's ArrayList.SubList (views checked against the root's modCount).
 * spliterator is not modelled.
 */
package java.util;

import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

public class ArrayList<E> extends AbstractList<E> implements List<E>, RandomAccess, Cloneable, java.io.Serializable {
    private static final Object[] NO_ELEMENTS = {};
    /** The array of a list made by new ArrayList(): first growth goes to at least 10. */
    private static final Object[] DEFAULT_NO_ELEMENTS = {};

    transient Object[] elementData;
    private int size;

    public ArrayList(int initialCapacity) {
        if (initialCapacity > 0) {
            elementData = new Object[initialCapacity];
        } else if (initialCapacity == 0) {
            elementData = NO_ELEMENTS;
        } else {
            throw new IllegalArgumentException("Illegal Capacity: " + initialCapacity);
        }
    }

    public ArrayList() {
        elementData = DEFAULT_NO_ELEMENTS;
    }

    public ArrayList(Collection<? extends E> c) {
        Object[] a = c.toArray();
        size = a.length;
        if (size != 0) {
            if (c.getClass() == ArrayList.class) {
                elementData = a;
            } else {
                Object[] es = new Object[size];
                System.arraycopy(a, 0, es, 0, size);
                elementData = es;
            }
        } else {
            elementData = NO_ELEMENTS;
        }
    }

    public void trimToSize() {
        modCount++;
        if (size < elementData.length) {
            elementData = (size == 0) ? NO_ELEMENTS : AbstractCollection.copyObjects(elementData, size);
        }
    }

    public void ensureCapacity(int minCapacity) {
        if (minCapacity > elementData.length && !(elementData == DEFAULT_NO_ELEMENTS && minCapacity <= 10)) {
            modCount++;
            growTo(minCapacity);
        }
    }

    /** New capacity >= minCapacity (see class comment). */
    private Object[] growTo(int minCapacity) {
        int old = elementData.length;
        if (old > 0 || elementData != DEFAULT_NO_ELEMENTS) {
            int len = old + Math.max(minCapacity - old, old >> 1);
            if (0 < len && len <= Integer.MAX_VALUE - 8) return elementData = AbstractCollection.copyObjects(elementData, len);
            // the huge-array corner of the growth policy (OutOfMemoryError in practice) is not modelled
            throw ModelStuck.unsupported("ArrayList capacity near Integer.MAX_VALUE");
        } else {
            return elementData = new Object[Math.max(10, minCapacity)];
        }
    }

    private Object[] growByOne() {
        return growTo(size + 1);
    }

    public int size() {
        return size;
    }

    public boolean isEmpty() {
        return size == 0;
    }

    public boolean contains(Object o) {
        return indexOf(o) >= 0;
    }

    public int indexOf(Object o) {
        return indexIn(o, 0, size);
    }

    int indexIn(Object o, int from, int to) {
        Object[] es = elementData;
        if (o == null) {
            for (int i = from; i < to; i++) {
                if (es[i] == null) return i;
            }
        } else {
            for (int i = from; i < to; i++) {
                if (o.equals(es[i])) return i;
            }
        }
        return -1;
    }

    public int lastIndexOf(Object o) {
        Object[] es = elementData;
        if (o == null) {
            for (int i = size - 1; i >= 0; i--) {
                if (es[i] == null) return i;
            }
        } else {
            for (int i = size - 1; i >= 0; i--) {
                if (o.equals(es[i])) return i;
            }
        }
        return -1;
    }

    public Object clone() {
        try {
            ArrayList<?> v = (ArrayList<?>) super.clone();
            v.elementData = AbstractCollection.copyObjects(elementData, size);
            v.modCount = 0;
            return v;
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e);
        }
    }

    public Object[] toArray() {
        return AbstractCollection.copyObjects(elementData, size);
    }

    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
        if (a.length < size) return (T[]) fillFrom(AbstractCollection.newArrayLike(a, size));
        System.arraycopy(elementData, 0, a, 0, size);
        if (a.length > size) a[size] = null;
        return a;
    }

    private Object[] fillFrom(Object[] r) {
        System.arraycopy(elementData, 0, r, 0, size);
        return r;
    }

    @SuppressWarnings("unchecked")
    E at(int index) {
        return (E) elementData[index];
    }

    private void checkIndex(int index) {
        if (index < 0 || index >= size) throw AbstractList.checkIndexFail(index, size);
    }

    private void checkPosition(int index) {
        if (index > size || index < 0) throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + size);
    }

    @SuppressWarnings("unchecked")
    E elementData(int index) {
        return (E) elementData[index];
    }

    int lastIndexOfRange(Object o, int start, int end) {
        Object[] es = elementData;
        if (o == null) {
            for (int i = end - 1; i >= start; i--) {
                if (es[i] == null) return i;
            }
        } else {
            for (int i = end - 1; i >= start; i--) {
                if (o.equals(es[i])) return i;
            }
        }
        return -1;
    }

    boolean equalsRange(List<?> other, int from, int to) {
        final Object[] es = elementData;
        if (to > es.length) throw new ConcurrentModificationException();
        Iterator<?> oit = other.iterator();
        for (; from < to; from++) {
            if (!oit.hasNext() || !Objects.equals(es[from], oit.next())) return false;
        }
        return !oit.hasNext();
    }

    int hashCodeRange(int from, int to) {
        final Object[] es = elementData;
        if (to > es.length) throw new ConcurrentModificationException();
        int hashCode = 1;
        for (int i = from; i < to; i++) {
            Object e = es[i];
            hashCode = 31 * hashCode + (e == null ? 0 : e.hashCode());
        }
        return hashCode;
    }

    /** Moves the tail [hi, size) down to lo and clears the freed slots. */
    private void shiftTailOverGap(Object[] es, int lo, int hi) {
        System.arraycopy(es, hi, es, lo, size - hi);
        int to = size;
        size -= hi - lo;
        for (int i = size; i < to; i++) es[i] = null;
    }

    public E get(int index) {
        checkIndex(index);
        return at(index);
    }

    public E set(int index, E element) {
        checkIndex(index);
        E old = at(index);
        elementData[index] = element;
        return old;
    }

    public boolean add(E e) {
        modCount++;
        Object[] es = elementData;
        int s = size;
        if (s == es.length) es = growByOne();
        es[s] = e;
        size = s + 1;
        return true;
    }

    public void add(int index, E element) {
        checkPosition(index);
        modCount++;
        int s = size;
        Object[] es = elementData;
        if (s == es.length) es = growByOne();
        System.arraycopy(es, index, es, index + 1, s - index);
        es[index] = element;
        size = s + 1;
    }

    public E remove(int index) {
        checkIndex(index);
        Object[] es = elementData;
        @SuppressWarnings("unchecked") E old = (E) es[index];
        removeAt(es, index);
        return old;
    }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof List)) return false;
        int expected = modCount;
        boolean equal = (o.getClass() == ArrayList.class) ? equalsArrayList((ArrayList<?>) o)
                                                         : equalsList((List<?>) o);
        checkComod(expected);
        return equal;
    }

    private boolean equalsArrayList(ArrayList<?> other) {
        int otherExpected = other.modCount;
        int s = size;
        boolean equal = (s == other.size);
        if (equal) {
            Object[] b = other.elementData;
            Object[] a = elementData;
            if (s > a.length || s > b.length) throw new ConcurrentModificationException();
            for (int i = 0; i < s; i++) {
                if (!AbstractMap.eq(a[i], b[i])) {
                    equal = false;
                    break;
                }
            }
        }
        other.checkComod(otherExpected);
        return equal;
    }

    private boolean equalsList(List<?> other) {
        Object[] a = elementData;
        int s = size;
        if (s > a.length) throw new ConcurrentModificationException();
        Iterator<?> it = other.iterator();
        for (int i = 0; i < s; i++) {
            if (!it.hasNext() || !AbstractMap.eq(a[i], it.next())) return false;
        }
        return !it.hasNext();
    }

    private void checkComod(int expected) {
        if (modCount != expected) throw new ConcurrentModificationException();
    }

    public int hashCode() {
        int expected = modCount;
        Object[] es = elementData;
        int s = size;
        if (s > es.length) throw new ConcurrentModificationException();
        int h = 1;
        for (int i = 0; i < s; i++) {
            Object e = es[i];
            h = 31 * h + (e == null ? 0 : e.hashCode());
        }
        checkComod(expected);
        return h;
    }

    public boolean remove(Object o) {
        Object[] es = elementData;
        int s = size;
        int i = 0;
        if (o == null) {
            while (i < s && es[i] != null) i++;
        } else {
            while (i < s && !o.equals(es[i])) i++;
        }
        if (i == s) return false;
        removeAt(es, i);
        return true;
    }

    private void removeAt(Object[] es, int i) {
        modCount++;
        int newSize = size - 1;
        if (newSize > i) System.arraycopy(es, i + 1, es, i, newSize - i);
        es[newSize] = null;
        size = newSize;
    }

    public void clear() {
        modCount++;
        Object[] es = elementData;
        for (int i = 0; i < size; i++) es[i] = null;
        size = 0;
    }

    public boolean addAll(Collection<? extends E> c) {
        Object[] a = c.toArray();
        modCount++;
        int n = a.length;
        if (n == 0) return false;
        Object[] es = elementData;
        int s = size;
        if (n > es.length - s) es = growTo(s + n);
        System.arraycopy(a, 0, es, s, n);
        size = s + n;
        return true;
    }

    public boolean addAll(int index, Collection<? extends E> c) {
        checkPosition(index);
        Object[] a = c.toArray();
        modCount++;
        int n = a.length;
        if (n == 0) return false;
        Object[] es = elementData;
        int s = size;
        if (n > es.length - s) es = growTo(s + n);
        int moved = s - index;
        if (moved > 0) System.arraycopy(es, index, es, index + n, moved);
        System.arraycopy(a, 0, es, index, n);
        size = s + n;
        return true;
    }

    protected void removeRange(int fromIndex, int toIndex) {
        if (fromIndex > toIndex)
            throw new IndexOutOfBoundsException("From Index: " + fromIndex + " > To Index: " + toIndex);
        modCount++;
        shiftTailOverGap(elementData, fromIndex, toIndex);
    }

    public boolean removeAll(Collection<?> c) {
        return batchRemove(c, false, 0, size);
    }

    public boolean retainAll(Collection<?> c) {
        return batchRemove(c, true, 0, size);
    }

    /** Keeps exactly the elements e with c.contains(e) == keep, testing each element once in
     *  order; modCount grows by the number of removed elements. */
    boolean batchRemove(Collection<?> c, boolean keep, final int from, final int end) {
        if (c == null) throw new NullPointerException();
        Object[] es = elementData;
        int r = from;
        while (r < end && c.contains(es[r]) == keep) r++;
        if (r == end) return false;
        int w = r++;
        try {
            for (; r < end; r++) {
                Object e = es[r];
                if (c.contains(e) == keep) es[w++] = e;
            }
        } catch (Throwable ex) {
            // as documented for bulk operations: the elements not yet examined are kept
            System.arraycopy(es, r, es, w, end - r);
            w += end - r;
            throw ex;
        } finally {
            modCount += end - w;
            shiftTailOverGap(es, w, end);
        }
        return true;
    }

    public boolean removeIf(Predicate<? super E> filter) {
        return removeIf(filter, 0, size);
    }

    boolean removeIf(Predicate<? super E> filter, int i, final int end) {
        if (filter == null) throw new NullPointerException();
        int expected = modCount;
        Object[] es = elementData;
        while (i < end && !filter.test(elementAtArray(es, i))) i++;
        if (i < end) {
            int first = i;
            boolean[] dead = new boolean[end - first];
            dead[0] = true;
            for (i = first + 1; i < end; i++) {
                if (filter.test(elementAtArray(es, i))) dead[i - first] = true;
            }
            if (modCount != expected) throw new ConcurrentModificationException();
            modCount++;
            int w = first;
            for (i = first; i < end; i++) {
                if (!dead[i - first]) es[w++] = es[i];
            }
            shiftTailOverGap(es, w, end);
            return true;
        } else {
            if (modCount != expected) throw new ConcurrentModificationException();
            return false;
        }
    }

    public void forEach(Consumer<? super E> action) {
        if (action == null) throw new NullPointerException();
        int expected = modCount;
        Object[] es = elementData;
        int s = size;
        for (int i = 0; modCount == expected && i < s; i++) action.accept(elementAtArray(es, i));
        if (modCount != expected) throw new ConcurrentModificationException();
    }

    @SuppressWarnings("unchecked")
    static <E> E elementAtArray(Object[] es, int i) {
        return (E) es[i];
    }

    public void replaceAll(UnaryOperator<E> operator) {
        replaceAllRange(operator, 0, size);
        modCount++;
    }

    void replaceAllRange(UnaryOperator<E> operator, int i, int end) {
        if (operator == null) throw new NullPointerException();
        int expected = modCount;
        Object[] es = elementData;
        for (; modCount == expected && i < end; i++) es[i] = operator.apply(elementAtArray(es, i));
        if (modCount != expected) throw new ConcurrentModificationException();
    }

    /** Javadoc: a stable sort of the elements; a modification by the comparator is a CME. */
    public void sort(Comparator<? super E> c) {
        int expectedModCount = modCount;
        Arrays.sortRange(elementData, 0, size, c);
        if (modCount != expectedModCount) throw new ConcurrentModificationException();
        modCount++;
    }

public List<E> subList(int fromIndex, int toIndex) {
        AbstractList.subListRangeCheck(fromIndex, toIndex, size);
        return new SubList<>(this, fromIndex, toIndex);
    }

    /** JDK 21 ArrayList.SubList: a view of [offset, offset + size) of the root's array. */
    private static class SubList<E> extends AbstractList<E> implements RandomAccess {
        private final ArrayList<E> root;
        private final SubList<E> parent;
        private final int offset;
        private int size;

        SubList(ArrayList<E> root, int fromIndex, int toIndex) {
            this.root = root;
            this.parent = null;
            this.offset = fromIndex;
            this.size = toIndex - fromIndex;
            this.modCount = root.modCount;
        }

        private SubList(SubList<E> parent, int fromIndex, int toIndex) {
            this.root = parent.root;
            this.parent = parent;
            this.offset = parent.offset + fromIndex;
            this.size = toIndex - fromIndex;
            this.modCount = parent.modCount;
        }

        public E set(int index, E element) {
            if (index < 0 || index >= size) throw AbstractList.checkIndexFail(index, size);
            checkForComodification();
            E oldValue = root.elementData(offset + index);
            root.elementData[offset + index] = element;
            return oldValue;
        }

        public E get(int index) {
            if (index < 0 || index >= size) throw AbstractList.checkIndexFail(index, size);
            checkForComodification();
            return root.elementData(offset + index);
        }

        public int size() {
            checkForComodification();
            return size;
        }

        public void add(int index, E element) {
            rangeCheckForAdd(index);
            checkForComodification();
            root.add(offset + index, element);
            updateSizeAndModCount(1);
        }

        public E remove(int index) {
            if (index < 0 || index >= size) throw AbstractList.checkIndexFail(index, size);
            checkForComodification();
            E result = root.remove(offset + index);
            updateSizeAndModCount(-1);
            return result;
        }

        protected void removeRange(int fromIndex, int toIndex) {
            checkForComodification();
            root.removeRange(offset + fromIndex, offset + toIndex);
            updateSizeAndModCount(fromIndex - toIndex);
        }

        public boolean addAll(Collection<? extends E> c) {
            return addAll(this.size, c);
        }

        public boolean addAll(int index, Collection<? extends E> c) {
            rangeCheckForAdd(index);
            int cSize = c.size();
            if (cSize == 0) return false;
            checkForComodification();
            root.addAll(offset + index, c);
            updateSizeAndModCount(cSize);
            return true;
        }

        public void replaceAll(UnaryOperator<E> operator) {
            root.replaceAllRange(operator, offset, offset + size);
        }

        public boolean removeAll(Collection<?> c) {
            return batchRemove(c, false);
        }

        public boolean retainAll(Collection<?> c) {
            return batchRemove(c, true);
        }

        private boolean batchRemove(Collection<?> c, boolean complement) {
            checkForComodification();
            int oldSize = root.size;
            boolean modified = root.batchRemove(c, complement, offset, offset + size);
            if (modified) updateSizeAndModCount(root.size - oldSize);
            return modified;
        }

        public boolean removeIf(Predicate<? super E> filter) {
            checkForComodification();
            int oldSize = root.size;
            boolean modified = root.removeIf(filter, offset, offset + size);
            if (modified) updateSizeAndModCount(root.size - oldSize);
            return modified;
        }

        public Object[] toArray() {
            checkForComodification();
            Object[] r = new Object[size];
            System.arraycopy(root.elementData, offset, r, 0, size);
            return r;
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            checkForComodification();
            if (a.length < size) {
                Object[] r = AbstractCollection.newArrayLike(a, size);
                System.arraycopy(root.elementData, offset, r, 0, size);
                return (T[]) r;
            }
            System.arraycopy(root.elementData, offset, a, 0, size);
            if (a.length > size) a[size] = null;
            return a;
        }

        public boolean equals(Object o) {
            if (o == this) return true;
            if (!(o instanceof List)) return false;
            boolean equal = root.equalsRange((List<?>) o, offset, offset + size);
            checkForComodification();
            return equal;
        }

        public int hashCode() {
            int hash = root.hashCodeRange(offset, offset + size);
            checkForComodification();
            return hash;
        }

        public int indexOf(Object o) {
            int index = root.indexIn(o, offset, offset + size);
            checkForComodification();
            return index >= 0 ? index - offset : -1;
        }

        public int lastIndexOf(Object o) {
            int index = root.lastIndexOfRange(o, offset, offset + size);
            checkForComodification();
            return index >= 0 ? index - offset : -1;
        }

        public boolean contains(Object o) {
            return indexOf(o) >= 0;
        }

        public Iterator<E> iterator() {
            return listIterator();
        }

        public ListIterator<E> listIterator(int index) {
            checkForComodification();
            rangeCheckForAdd(index);
            return new SubItr(index);
        }

        private final class SubItr implements ListIterator<E> {
            int cursor;
            int lastRet = -1;
            int expectedModCount = SubList.this.modCount;

            SubItr(int index) {
                cursor = index;
            }

            public boolean hasNext() {
                return cursor != SubList.this.size;
            }

            @SuppressWarnings("unchecked")
            public E next() {
                checkForComod();
                int i = cursor;
                if (i >= SubList.this.size) throw new NoSuchElementException();
                Object[] elementData = root.elementData;
                if (offset + i >= elementData.length) throw new ConcurrentModificationException();
                cursor = i + 1;
                return (E) elementData[offset + (lastRet = i)];
            }

            public boolean hasPrevious() {
                return cursor != 0;
            }

            @SuppressWarnings("unchecked")
            public E previous() {
                checkForComod();
                int i = cursor - 1;
                if (i < 0) throw new NoSuchElementException();
                Object[] elementData = root.elementData;
                if (offset + i >= elementData.length) throw new ConcurrentModificationException();
                cursor = i;
                return (E) elementData[offset + (lastRet = i)];
            }

            public void forEachRemaining(Consumer<? super E> action) {
                Objects.requireNonNull(action);
                final int sz = SubList.this.size;
                int i = cursor;
                if (i < sz) {
                    final Object[] es = root.elementData;
                    if (offset + i >= es.length) throw new ConcurrentModificationException();
                    for (; i < sz && root.modCount == expectedModCount; i++) action.accept(elementAtArray(es, offset + i));
                    cursor = i;
                    lastRet = i - 1;
                    checkForComod();
                }
            }

            public int nextIndex() {
                return cursor;
            }

            public int previousIndex() {
                return cursor - 1;
            }

            public void remove() {
                if (lastRet < 0) throw new IllegalStateException();
                checkForComod();
                try {
                    SubList.this.remove(lastRet);
                    cursor = lastRet;
                    lastRet = -1;
                    expectedModCount = SubList.this.modCount;
                } catch (IndexOutOfBoundsException ex) {
                    throw new ConcurrentModificationException();
                }
            }

            public void set(E e) {
                if (lastRet < 0) throw new IllegalStateException();
                checkForComod();
                try {
                    root.set(offset + lastRet, e);
                } catch (IndexOutOfBoundsException ex) {
                    throw new ConcurrentModificationException();
                }
            }

            public void add(E e) {
                checkForComod();
                try {
                    int i = cursor;
                    SubList.this.add(i, e);
                    cursor = i + 1;
                    lastRet = -1;
                    expectedModCount = SubList.this.modCount;
                } catch (IndexOutOfBoundsException ex) {
                    throw new ConcurrentModificationException();
                }
            }

            final void checkForComod() {
                if (root.modCount != expectedModCount) throw new ConcurrentModificationException();
            }
        }

        public List<E> subList(int fromIndex, int toIndex) {
            AbstractList.subListRangeCheck(fromIndex, toIndex, size);
            return new SubList<>(this, fromIndex, toIndex);
        }

        private void rangeCheckForAdd(int index) {
            if (index < 0 || index > this.size)
                throw new IndexOutOfBoundsException("Index: " + index + ", Size: " + this.size);
        }

        private void checkForComodification() {
            if (root.modCount != modCount) throw new ConcurrentModificationException();
        }

        private void updateSizeAndModCount(int sizeChange) {
            SubList<E> slist = this;
            do {
                slist.size += sizeChange;
                slist.modCount = root.modCount;
                slist = slist.parent;
            } while (slist != null);
        }
    }

    public Iterator<E> iterator() {
        return new Itr();
    }

    public ListIterator<E> listIterator() {
        return new ListItr(0);
    }

    public ListIterator<E> listIterator(int index) {
        checkPosition(index);
        return new ListItr(index);
    }

    private class Itr implements Iterator<E> {
        int cursor;
        int lastRet = -1;
        int expectedModCount = modCount;

        Itr() {
        }

        public boolean hasNext() {
            return cursor != size;
        }

        @SuppressWarnings("unchecked")
        public E next() {
            checkComod();
            int i = cursor;
            if (i >= size) throw new NoSuchElementException();
            Object[] es = ArrayList.this.elementData;
            if (i >= es.length) throw new ConcurrentModificationException();
            cursor = i + 1;
            lastRet = i;
            return (E) es[i];
        }

        public void remove() {
            if (lastRet < 0) throw new IllegalStateException();
            checkComod();
            try {
                ArrayList.this.remove(lastRet);
                cursor = lastRet;
                lastRet = -1;
                expectedModCount = modCount;
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
        }

        public void forEachRemaining(Consumer<? super E> action) {
            if (action == null) throw new NullPointerException();
            int s = ArrayList.this.size;
            int i = cursor;
            if (i < s) {
                Object[] es = elementData;
                if (i >= es.length) throw new ConcurrentModificationException();
                for (; i < s && modCount == expectedModCount; i++) action.accept(elementAtArray(es, i));
                cursor = i;
                lastRet = i - 1;
                checkComod();
            }
        }

        final void checkComod() {
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
        }
    }

    private class ListItr extends Itr implements ListIterator<E> {
        ListItr(int index) {
            super();
            cursor = index;
        }

        public boolean hasPrevious() {
            return cursor != 0;
        }

        public int nextIndex() {
            return cursor;
        }

        public int previousIndex() {
            return cursor - 1;
        }

        @SuppressWarnings("unchecked")
        public E previous() {
            checkComod();
            int i = cursor - 1;
            if (i < 0) throw new NoSuchElementException();
            Object[] es = ArrayList.this.elementData;
            if (i >= es.length) throw new ConcurrentModificationException();
            cursor = i;
            lastRet = i;
            return (E) es[i];
        }

        public void set(E e) {
            if (lastRet < 0) throw new IllegalStateException();
            checkComod();
            try {
                ArrayList.this.set(lastRet, e);
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
        }

        public void add(E e) {
            checkComod();
            try {
                int i = cursor;
                ArrayList.this.add(i, e);
                cursor = i + 1;
                lastRet = -1;
                expectedModCount = modCount;
            } catch (IndexOutOfBoundsException ex) {
                throw new ConcurrentModificationException();
            }
        }
    }
}

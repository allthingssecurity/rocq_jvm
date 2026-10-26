/*
 * rocq-jvm model of java.util.PriorityQueue (clean-room, Apache-2.0).
 *
 * A binary min-heap in an array, with the JDK's sift-up / sift-down / heapify algorithms, so that
 * the array order (iteration, toString, toArray) is the JDK's. The iterator walks the array; when
 * Iterator.remove moves an element from the end of the heap to before the cursor, that element is
 * remembered and returned at the end ("forget-me-not"), as in the JDK. Exceptions that the JDK
 * raises implicitly inside compareTo (a null element in a collection given to the constructor, a
 * non-Comparable element, elements of different classes) are thrown explicitly with HotSpot's
 * messages (see TreeMap.cmpNat).
 * Not modelled (STUCK): serialization, spliterator / stream.
 */
package java.util;

import java.util.function.Consumer;
import java.util.function.Predicate;

@SuppressWarnings("unchecked")
public class PriorityQueue<E> extends AbstractQueue<E> implements java.io.Serializable {
    private static final int DEFAULT_INITIAL_CAPACITY = 11;

    transient Object[] queue;
    int size;
    private final Comparator<? super E> comparator;
    transient int modCount;

    public PriorityQueue() {
        this(DEFAULT_INITIAL_CAPACITY, null);
    }

    public PriorityQueue(int initialCapacity) {
        this(initialCapacity, null);
    }

    public PriorityQueue(Comparator<? super E> comparator) {
        this(DEFAULT_INITIAL_CAPACITY, comparator);
    }

    public PriorityQueue(int initialCapacity, Comparator<? super E> comparator) {
        if (initialCapacity < 1) throw new IllegalArgumentException();
        this.queue = new Object[initialCapacity];
        this.comparator = comparator;
    }

    public PriorityQueue(Collection<? extends E> c) {
        if (c instanceof SortedSet<?>) {
            SortedSet<? extends E> ss = (SortedSet<? extends E>) c;
            this.comparator = (Comparator<? super E>) ss.comparator();
            initElementsFromCollection(ss);
        } else if (c instanceof PriorityQueue<?>) {
            PriorityQueue<? extends E> pq = (PriorityQueue<? extends E>) c;
            this.comparator = (Comparator<? super E>) pq.comparator();
            initFromPriorityQueue(pq);
        } else {
            this.comparator = null;
            initFromCollection(c);
        }
    }

    public PriorityQueue(PriorityQueue<? extends E> c) {
        if (c == null) throw TreeMap.invokeOnNull("java.util.PriorityQueue.comparator()", "c");
        this.comparator = (Comparator<? super E>) c.comparator();
        initFromPriorityQueue(c);
    }

    public PriorityQueue(SortedSet<? extends E> c) {
        if (c == null) throw TreeMap.invokeOnNull("java.util.SortedSet.comparator()", "c");
        this.comparator = (Comparator<? super E>) c.comparator();
        initElementsFromCollection(c);
    }

    private static Object[] ensureNonEmpty(Object[] es) {
        return (es.length > 0) ? es : new Object[1];
    }

    private void initFromPriorityQueue(PriorityQueue<? extends E> c) {
        if (c.getClass() == PriorityQueue.class) {
            this.queue = ensureNonEmpty(c.toArray());
            this.size = c.size();
        } else {
            initFromCollection(c);
        }
    }

    private void initElementsFromCollection(Collection<? extends E> c) {
        if (c == null) throw TreeMap.invokeOnNull("java.util.Collection.toArray()", "c");
        Object[] a = c.toArray();
        int len = a.length;
        Object[] es = new Object[len];
        System.arraycopy(a, 0, es, 0, len);
        if (len == 1 || this.comparator != null) {
            for (Object e : es) {
                if (e == null) throw new NullPointerException();
            }
        }
        this.queue = ensureNonEmpty(es);
        this.size = len;
    }

    private void initFromCollection(Collection<? extends E> c) {
        initElementsFromCollection(c);
        heapify();
    }

    private void grow(int minCapacity) {
        int oldCapacity = queue.length;
        int pref = oldCapacity < 64 ? oldCapacity + 2 : oldCapacity >> 1;
        int newCapacity = oldCapacity + Math.max(minCapacity - oldCapacity, pref);
        if (newCapacity < 0) throw ModelStuck.unsupported("PriorityQueue: capacity overflow");
        Object[] n = new Object[newCapacity];
        System.arraycopy(queue, 0, n, 0, oldCapacity);
        queue = n;
    }

    public boolean add(E e) {
        return offer(e);
    }

    public boolean offer(E e) {
        if (e == null) throw new NullPointerException();
        modCount++;
        int i = size;
        if (i >= queue.length) grow(i + 1);
        siftUp(i, e);
        size = i + 1;
        return true;
    }

    public E peek() {
        return (E) queue[0];
    }

    private int indexOf(Object o) {
        if (o != null) {
            Object[] es = queue;
            for (int i = 0, n = size; i < n; i++) {
                if (o.equals(es[i])) return i;
            }
        }
        return -1;
    }

    public boolean remove(Object o) {
        int i = indexOf(o);
        if (i == -1) return false;
        removeAt(i);
        return true;
    }

    /** Removes the first element identical to o (used by the iterator). */
    void removeEq(Object o) {
        Object[] es = queue;
        for (int i = 0, n = size; i < n; i++) {
            if (o == es[i]) {
                removeAt(i);
                break;
            }
        }
    }

    public boolean contains(Object o) {
        return indexOf(o) >= 0;
    }

    public Object[] toArray() {
        return AbstractCollection.copyObjects(queue, size);
    }

    public <T> T[] toArray(T[] a) {
        if (a == null) throw new NullPointerException("Cannot read the array length because \"a\" is null");
        int size = this.size;
        if (a.length < size) {
            Object[] r = AbstractCollection.newArrayLike(a, size);
            System.arraycopy(queue, 0, r, 0, size);
            return (T[]) r;
        }
        System.arraycopy(queue, 0, a, 0, size);
        if (a.length > size) a[size] = null;
        return a;
    }

    public Iterator<E> iterator() {
        return new Itr();
    }

    private final class Itr implements Iterator<E> {
        private int cursor;
        private int lastRet = -1;
        private ArrayDeque<E> forgetMeNot;
        private E lastRetElt;
        private int expectedModCount = modCount;

        Itr() {
        }

        public boolean hasNext() {
            return cursor < size || (forgetMeNot != null && !forgetMeNot.isEmpty());
        }

        public E next() {
            if (expectedModCount != modCount) throw new ConcurrentModificationException();
            if (cursor < size) return (E) queue[lastRet = cursor++];
            if (forgetMeNot != null) {
                lastRet = -1;
                lastRetElt = forgetMeNot.poll();
                if (lastRetElt != null) return lastRetElt;
            }
            throw new NoSuchElementException();
        }

        public void remove() {
            if (expectedModCount != modCount) throw new ConcurrentModificationException();
            if (lastRet != -1) {
                E moved = PriorityQueue.this.removeAt(lastRet);
                lastRet = -1;
                if (moved == null) {
                    cursor--;
                } else {
                    if (forgetMeNot == null) forgetMeNot = new ArrayDeque<>();
                    forgetMeNot.add(moved);
                }
            } else if (lastRetElt != null) {
                PriorityQueue.this.removeEq(lastRetElt);
                lastRetElt = null;
            } else {
                throw new IllegalStateException();
            }
            expectedModCount = modCount;
        }
    }

    public int size() {
        return size;
    }

    public void clear() {
        modCount++;
        Object[] es = queue;
        for (int i = 0, n = size; i < n; i++) es[i] = null;
        size = 0;
    }

    public E poll() {
        Object[] es = queue;
        E result = (E) es[0];
        if (result != null) {
            modCount++;
            int n = --size;
            E x = (E) es[n];
            es[n] = null;
            if (n > 0) {
                if (comparator == null) siftDownComparable(0, x, es, n);
                else siftDownUsingComparator(0, x, es, n, comparator);
            }
        }
        return result;
    }

    /** Removes the i-th array element; returns the moved last element if it ended up before i
     *  (the iterator must still visit it), else null. */
    E removeAt(int i) {
        Object[] es = queue;
        modCount++;
        int s = --size;
        if (s == i) {
            es[i] = null;
        } else {
            E moved = (E) es[s];
            es[s] = null;
            siftDown(i, moved);
            if (es[i] == moved) {
                siftUp(i, moved);
                if (es[i] != moved) return moved;
            }
        }
        return null;
    }

    private void siftUp(int k, E x) {
        if (comparator != null) siftUpUsingComparator(k, x, queue, comparator);
        else siftUpComparable(k, x, queue);
    }

    /** The element as Comparable (the JDK's checkcast; null passes). */
    private static Object asComparable(Object x) {
        if (x != null && !(x instanceof Comparable)) throw TreeMap.castFail(x, "java.lang.Comparable");
        return x;
    }

    /** k.compareTo(x) where k (the JDK local variable named 'name') may be null. */
    private static int cmp(Object k, String name, Object x) {
        if (k == null) throw TreeMap.invokeOnNull("java.lang.Comparable.compareTo(Object)", name);
        return TreeMap.cmpNat(k, x);
    }

    private static <T> void siftUpComparable(int k, T x, Object[] es) {
        Object key = asComparable(x);
        while (k > 0) {
            int parent = (k - 1) >>> 1;
            Object e = es[parent];
            if (cmp(key, "key", e) >= 0) break;
            es[k] = e;
            k = parent;
        }
        es[k] = key;
    }

    private static <T> void siftUpUsingComparator(int k, T x, Object[] es, Comparator<? super T> cmp) {
        while (k > 0) {
            int parent = (k - 1) >>> 1;
            Object e = es[parent];
            if (cmp.compare(x, (T) e) >= 0) break;
            es[k] = e;
            k = parent;
        }
        es[k] = x;
    }

    private void siftDown(int k, E x) {
        if (comparator != null) siftDownUsingComparator(k, x, queue, size, comparator);
        else siftDownComparable(k, x, queue, size);
    }

    private static <T> void siftDownComparable(int k, T x, Object[] es, int n) {
        Object key = asComparable(x);
        int half = n >>> 1;
        while (k < half) {
            int child = (k << 1) + 1;
            Object c = es[child];
            int right = child + 1;
            if (right < n && cmp(asComparable(c), "c", es[right]) > 0) c = es[child = right];
            if (cmp(key, "key", c) <= 0) break;
            es[k] = c;
            k = child;
        }
        es[k] = key;
    }

    private static <T> void siftDownUsingComparator(int k, T x, Object[] es, int n, Comparator<? super T> cmp) {
        int half = n >>> 1;
        while (k < half) {
            int child = (k << 1) + 1;
            Object c = es[child];
            int right = child + 1;
            if (right < n && cmp.compare((T) c, (T) es[right]) > 0) c = es[child = right];
            if (cmp.compare(x, (T) c) <= 0) break;
            es[k] = c;
            k = child;
        }
        es[k] = x;
    }

    private void heapify() {
        Object[] es = queue;
        int n = size, i = (n >>> 1) - 1;
        if (comparator == null) {
            for (; i >= 0; i--) siftDownComparable(i, (E) es[i], es, n);
        } else {
            for (; i >= 0; i--) siftDownUsingComparator(i, (E) es[i], es, n, comparator);
        }
    }

    public Comparator<? super E> comparator() {
        return comparator;
    }

    public boolean removeIf(Predicate<? super E> filter) {
        if (filter == null) throw new NullPointerException();
        return bulkRemove(filter);
    }

    public boolean removeAll(Collection<?> c) {
        if (c == null) throw new NullPointerException();
        return bulkRemove(e -> c.contains(e));
    }

    public boolean retainAll(Collection<?> c) {
        if (c == null) throw new NullPointerException();
        return bulkRemove(e -> !c.contains(e));
    }

    /** JDK: test every element first (modCount bumped once, CME if the filter modified the
     *  queue), then compact the survivors in array order and heapify. */
    private boolean bulkRemove(Predicate<? super E> filter) {
        final int expectedModCount = ++modCount;
        final Object[] es = queue;
        final int end = size;
        int i;
        for (i = 0; i < end && !filter.test((E) es[i]); i++)
            ;
        if (i >= end) {
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            return false;
        }
        final int beg = i;
        boolean[] dead = new boolean[end - beg];
        dead[0] = true;
        for (i = beg + 1; i < end; i++) {
            if (filter.test((E) es[i])) dead[i - beg] = true;
        }
        if (modCount != expectedModCount) throw new ConcurrentModificationException();
        int w = beg;
        for (i = beg; i < end; i++) {
            if (!dead[i - beg]) es[w++] = es[i];
        }
        for (i = size = w; i < end; i++) es[i] = null;
        heapify();
        return true;
    }

    public void forEach(Consumer<? super E> action) {
        if (action == null) throw new NullPointerException();
        final int expectedModCount = modCount;
        final Object[] es = queue;
        for (int i = 0, n = size; i < n; i++) action.accept((E) es[i]);
        if (expectedModCount != modCount) throw new ConcurrentModificationException();
    }
}

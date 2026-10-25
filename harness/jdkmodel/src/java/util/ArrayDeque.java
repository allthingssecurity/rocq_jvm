/*
 * Clean-room model of java.util.ArrayDeque (from the Javadoc) for the Rocq machine; r82 hunt, adopted into harness/jdkmodel
 * (written by the r82 Camel hunt session; adopted into harness/jdkmodel). A circular array that doubles when full; null elements are rejected with
 * NullPointerException; the exceptions of the Javadoc (NoSuchElementException on an empty deque for
 * remove/get/element/pop). Iterators run from head to tail (descendingIterator: tail to head) and support remove();
 * they do not detect concurrent modification (the JDK's are fail-fast on a best-effort basis): a run that relies
 * on ConcurrentModificationException is not modelled. Not modelled: clone, toArray ordering beyond
 * AbstractCollection's, spliterator, streams, removeIf/removeAll/retainAll optimisations (the inherited default
 * behaviour applies), serialization.
 */
package java.util;

public class ArrayDeque<E> extends AbstractCollection<E> implements Deque<E>, Cloneable, java.io.Serializable {
    private Object[] elements;
    private int head;
    private int size;

    public ArrayDeque() {
        elements = new Object[16];
    }

    public ArrayDeque(int numElements) {
        elements = new Object[Math.max(1, numElements)];
    }

    public ArrayDeque(Collection<? extends E> c) {
        this(c.size());
        for (E e : c) {
            addLast(e);
        }
    }

    private int idx(int i) {
        return (head + i) % elements.length;
    }

    private void grow() {
        Object[] n = new Object[elements.length * 2];
        for (int i = 0; i < size; i++) {
            n[i] = elements[idx(i)];
        }
        elements = n;
        head = 0;
    }

    @SuppressWarnings("unchecked")
    private E at(int i) {
        return (E) elements[idx(i)];
    }

    public void addFirst(E e) {
        if (e == null) throw new NullPointerException();
        if (size == elements.length) grow();
        head = (head - 1 + elements.length) % elements.length;
        elements[head] = e;
        size++;
    }

    public void addLast(E e) {
        if (e == null) throw new NullPointerException();
        if (size == elements.length) grow();
        elements[idx(size)] = e;
        size++;
    }

    public boolean offerFirst(E e) {
        addFirst(e);
        return true;
    }

    public boolean offerLast(E e) {
        addLast(e);
        return true;
    }

    public E removeFirst() {
        E e = pollFirst();
        if (e == null) throw new NoSuchElementException();
        return e;
    }

    public E removeLast() {
        E e = pollLast();
        if (e == null) throw new NoSuchElementException();
        return e;
    }

    public E pollFirst() {
        if (size == 0) return null;
        E e = at(0);
        elements[head] = null;
        head = (head + 1) % elements.length;
        size--;
        return e;
    }

    public E pollLast() {
        if (size == 0) return null;
        int t = idx(size - 1);
        @SuppressWarnings("unchecked")
        E e = (E) elements[t];
        elements[t] = null;
        size--;
        return e;
    }

    public E getFirst() {
        if (size == 0) throw new NoSuchElementException();
        return at(0);
    }

    public E getLast() {
        if (size == 0) throw new NoSuchElementException();
        return at(size - 1);
    }

    public E peekFirst() {
        return size == 0 ? null : at(0);
    }

    public E peekLast() {
        return size == 0 ? null : at(size - 1);
    }

    /** Removes the element at position i (0 = head), shifting the later ones towards the head. */
    private void delete(int i) {
        for (int j = i; j + 1 < size; j++) {
            elements[idx(j)] = elements[idx(j + 1)];
        }
        elements[idx(size - 1)] = null;
        size--;
    }

    public boolean removeFirstOccurrence(Object o) {
        if (o == null) return false;
        for (int i = 0; i < size; i++) {
            if (o.equals(at(i))) {
                delete(i);
                return true;
            }
        }
        return false;
    }

    public boolean removeLastOccurrence(Object o) {
        if (o == null) return false;
        for (int i = size - 1; i >= 0; i--) {
            if (o.equals(at(i))) {
                delete(i);
                return true;
            }
        }
        return false;
    }

    public boolean add(E e) {
        addLast(e);
        return true;
    }

    public boolean offer(E e) {
        return offerLast(e);
    }

    public E remove() {
        return removeFirst();
    }

    public E poll() {
        return pollFirst();
    }

    public E element() {
        return getFirst();
    }

    public E peek() {
        return peekFirst();
    }

    public void push(E e) {
        addFirst(e);
    }

    public E pop() {
        return removeFirst();
    }

    public boolean remove(Object o) {
        return removeFirstOccurrence(o);
    }

    public boolean contains(Object o) {
        if (o == null) return false;
        for (int i = 0; i < size; i++) {
            if (o.equals(at(i))) return true;
        }
        return false;
    }

    public int size() {
        return size;
    }

    public boolean isEmpty() {
        return size == 0;
    }

    public void clear() {
        for (int i = 0; i < size; i++) {
            elements[idx(i)] = null;
        }
        head = 0;
        size = 0;
    }

    public Iterator<E> iterator() {
        return new Itr(false);
    }

    public Iterator<E> descendingIterator() {
        return new Itr(true);
    }

    private final class Itr implements Iterator<E> {
        private final boolean desc;
        private int next;        // number of elements returned so far
        private int last = -1;   // position of the element returned last

        Itr(boolean desc) {
            this.desc = desc;
        }

        public boolean hasNext() {
            return next < size;
        }

        public E next() {
            if (next >= size) throw new NoSuchElementException();
            int pos = desc ? size - 1 - next : next;
            last = pos;
            next++;
            return at(pos);
        }

        public void remove() {
            if (last < 0) throw new IllegalStateException();
            delete(last);
            next--;
            last = -1;
        }
    }
}

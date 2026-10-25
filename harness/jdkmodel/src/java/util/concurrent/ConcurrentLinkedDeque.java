/*
 * rocq-jvm model of java.util.concurrent.ConcurrentLinkedDeque (clean-room, Apache-2.0).
 * A doubly linked chain; removed elements keep their node with item == null and every traversal
 * skips them (the JDK unlinks them lazily; traversals see the same live elements in the same
 * order). Iterators (both directions) prefetch the next live element, as JDK 21's AbstractItr.
 * Operations are synchronized (atomic under the model's sequentially consistent threads).
 * spliterator: STUCK.
 */
package java.util.concurrent;

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Deque;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.function.Consumer;
import java.util.function.Predicate;

public class ConcurrentLinkedDeque<E> extends AbstractCollection<E> implements Deque<E>, java.io.Serializable {
    private static final long serialVersionUID = 876323262645176354L;

    static final class Node<E> {
        E item;
        Node<E> prev, next;

        Node(E item) {
            this.item = item;
        }
    }

    private transient Node<E> first, last; // ends of the chain (possibly dead)
    private final transient Object lock = new Object();

    public ConcurrentLinkedDeque() {
    }

    public ConcurrentLinkedDeque(Collection<? extends E> c) {
        for (E e : c) linkLast(new Node<E>(Objects.requireNonNull(e)));
    }

    private void linkFirst(Node<E> n) {
        synchronized (lock) {
            if (first == null) {
                first = last = n;
            } else {
                n.next = first;
                first.prev = n;
                first = n;
            }
        }
    }

    private void linkLast(Node<E> n) {
        synchronized (lock) {
            if (last == null) {
                first = last = n;
            } else {
                n.prev = last;
                last.next = n;
                last = n;
            }
        }
    }

    private Node<E> firstLive() {
        Node<E> p = first;
        while (p != null && p.item == null) p = p.next;
        return p;
    }

    private Node<E> lastLive() {
        Node<E> p = last;
        while (p != null && p.item == null) p = p.prev;
        return p;
    }

    private static <E> Node<E> nextLive(Node<E> p) {
        p = p.next;
        while (p != null && p.item == null) p = p.next;
        return p;
    }

    private static <E> Node<E> prevLive(Node<E> p) {
        p = p.prev;
        while (p != null && p.item == null) p = p.prev;
        return p;
    }

    private E screenNullResult(E v) {
        if (v == null) throw new NoSuchElementException();
        return v;
    }

    public void addFirst(E e) {
        linkFirst(new Node<E>(Objects.requireNonNull(e)));
    }

    public void addLast(E e) {
        linkLast(new Node<E>(Objects.requireNonNull(e)));
    }

    public boolean offerFirst(E e) {
        addFirst(e);
        return true;
    }

    public boolean offerLast(E e) {
        addLast(e);
        return true;
    }

    public E peekFirst() {
        synchronized (lock) {
            Node<E> p = firstLive();
            return p == null ? null : p.item;
        }
    }

    public E peekLast() {
        synchronized (lock) {
            Node<E> p = lastLive();
            return p == null ? null : p.item;
        }
    }

    public E getFirst() {
        return screenNullResult(peekFirst());
    }

    public E getLast() {
        return screenNullResult(peekLast());
    }

    public E pollFirst() {
        synchronized (lock) {
            Node<E> p = firstLive();
            if (p == null) return null;
            E item = p.item;
            p.item = null;
            return item;
        }
    }

    public E pollLast() {
        synchronized (lock) {
            Node<E> p = lastLive();
            if (p == null) return null;
            E item = p.item;
            p.item = null;
            return item;
        }
    }

    public E removeFirst() {
        return screenNullResult(pollFirst());
    }

    public E removeLast() {
        return screenNullResult(pollLast());
    }

    public boolean offer(E e) {
        return offerLast(e);
    }

    public boolean add(E e) {
        return offerLast(e);
    }

    public E poll() { return pollFirst(); }
    public E peek() { return peekFirst(); }
    public E remove() { return removeFirst(); }
    public E pop() { return removeFirst(); }
    public E element() { return getFirst(); }
    public void push(E e) { addFirst(e); }

    public boolean removeFirstOccurrence(Object o) {
        Objects.requireNonNull(o);
        synchronized (lock) {
            for (Node<E> p = firstLive(); p != null; p = nextLive(p)) {
                E item = p.item;
                if (item != null && o.equals(item)) {
                    p.item = null;
                    return true;
                }
            }
            return false;
        }
    }

    public boolean removeLastOccurrence(Object o) {
        Objects.requireNonNull(o);
        synchronized (lock) {
            for (Node<E> p = lastLive(); p != null; p = prevLive(p)) {
                E item = p.item;
                if (item != null && o.equals(item)) {
                    p.item = null;
                    return true;
                }
            }
            return false;
        }
    }

    public boolean contains(Object o) {
        if (o != null) {
            synchronized (lock) {
                for (Node<E> p = firstLive(); p != null; p = nextLive(p)) {
                    E item = p.item;
                    if (item != null && o.equals(item)) return true;
                }
            }
        }
        return false;
    }

    public boolean isEmpty() {
        return peekFirst() == null;
    }

    public int size() {
        synchronized (lock) {
            int count = 0;
            for (Node<E> p = firstLive(); p != null; p = nextLive(p)) {
                if (++count == Integer.MAX_VALUE) break;
            }
            return count;
        }
    }

    public boolean remove(Object o) {
        return removeFirstOccurrence(o);
    }

    public boolean addAll(Collection<? extends E> c) {
        if (c == this) throw new IllegalArgumentException();
        Node<E> beginningOfTheEnd = null, end = null;
        for (E e : c) {
            Node<E> n = new Node<E>(Objects.requireNonNull(e));
            if (beginningOfTheEnd == null) beginningOfTheEnd = end = n;
            else {
                end.next = n;
                n.prev = end;
                end = n;
            }
        }
        if (beginningOfTheEnd == null) return false;
        synchronized (lock) {
            if (last == null) {
                first = beginningOfTheEnd;
            } else {
                last.next = beginningOfTheEnd;
                beginningOfTheEnd.prev = last;
            }
            last = end;
        }
        return true;
    }

    public void clear() {
        while (pollFirst() != null) {
        }
    }

    public String toString() {
        StringBuilder sb = null;
        synchronized (lock) {
            for (Node<E> p = firstLive(); p != null; p = nextLive(p)) {
                String s = p.item.toString();
                if (sb == null) sb = new StringBuilder("[");
                else sb.append(", ");
                sb.append(s);
            }
        }
        return sb == null ? "[]" : sb.append(']').toString();
    }

    public Object[] toArray() {
        synchronized (lock) {
            java.util.ArrayList<Object> l = new java.util.ArrayList<>();
            for (Node<E> p = firstLive(); p != null; p = nextLive(p)) l.add(p.item);
            return l.toArray();
        }
    }

    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
        if (a == null) throw new NullPointerException();
        Object[] es = toArray();
        if (a.length < es.length) {
            T[] r = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), es.length);
            System.arraycopy(es, 0, r, 0, es.length);
            return r;
        }
        System.arraycopy(es, 0, a, 0, es.length);
        if (a.length > es.length) a[es.length] = null;
        return a;
    }

    public Iterator<E> iterator() {
        return new Itr(false);
    }

    public Iterator<E> descendingIterator() {
        return new Itr(true);
    }

    private final class Itr implements Iterator<E> {
        private final boolean descending;
        private Node<E> nextNode;
        private E nextItem;
        private Node<E> lastRet;

        Itr(boolean descending) {
            this.descending = descending;
            advance();
        }

        private void advance() {
            synchronized (lock) {
                lastRet = nextNode;
                Node<E> p = (nextNode == null)
                    ? (descending ? lastLive() : firstLive())
                    : (descending ? prevLive(nextNode) : nextLive(nextNode));
                if (p == null) {
                    nextNode = null;
                    nextItem = null;
                } else {
                    nextNode = p;
                    nextItem = p.item;
                }
            }
        }

        public boolean hasNext() {
            return nextItem != null;
        }

        public E next() {
            E item = nextItem;
            if (item == null) throw new NoSuchElementException();
            advance();
            return item;
        }

        public void remove() {
            Node<E> l = lastRet;
            if (l == null) throw new IllegalStateException();
            synchronized (lock) {
                l.item = null;
            }
            lastRet = null;
        }
    }

    public boolean removeIf(Predicate<? super E> filter) {
        Objects.requireNonNull(filter);
        return bulkRemove(filter);
    }

    public boolean removeAll(Collection<?> c) {
        Objects.requireNonNull(c);
        return bulkRemove(e -> c.contains(e));
    }

    public boolean retainAll(Collection<?> c) {
        Objects.requireNonNull(c);
        return bulkRemove(e -> !c.contains(e));
    }

    private boolean bulkRemove(Predicate<? super E> filter) {
        boolean removed = false;
        Node<E> p;
        synchronized (lock) {
            p = firstLive();
        }
        while (p != null) {
            E item;
            synchronized (lock) {
                item = p.item;
            }
            if (item != null && filter.test(item)) {
                synchronized (lock) {
                    if (p.item == item) {
                        p.item = null;
                        removed = true;
                    }
                }
            }
            synchronized (lock) {
                p = nextLive(p);
            }
        }
        return removed;
    }

    public void forEach(Consumer<? super E> action) {
        Objects.requireNonNull(action);
        Node<E> p;
        synchronized (lock) {
            p = firstLive();
        }
        while (p != null) {
            E item;
            synchronized (lock) {
                item = p.item;
            }
            if (item != null) action.accept(item);
            synchronized (lock) {
                p = nextLive(p);
            }
        }
    }

    public java.util.Spliterator<E> spliterator() {
        throw ModelStuck.unsupported("ConcurrentLinkedDeque.spliterator");
    }
}

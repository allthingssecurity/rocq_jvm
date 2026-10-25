/*
 * rocq-jvm model of java.util.concurrent.ConcurrentLinkedQueue (clean-room, Apache-2.0).
 * A chain of nodes; a removed element's node keeps its place with item == null and is skipped by
 * every traversal (the JDK unlinks such nodes lazily; a traversal sees the same live elements
 * in the same order). Iterators are weakly consistent as in JDK 21: each one prefetches the
 * next live element, so next() returns it even if it was removed meanwhile, and sees elements
 * added later behind its position. Operations are synchronized (atomic under the model's
 * sequentially consistent threads, as the JDK's CAS steps are). spliterator: STUCK.
 */
package java.util.concurrent;

import java.util.AbstractQueue;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Queue;
import java.util.function.Consumer;
import java.util.function.Predicate;

public class ConcurrentLinkedQueue<E> extends AbstractQueue<E> implements Queue<E>, java.io.Serializable {
    private static final long serialVersionUID = 196745693267521676L;

    static final class Node<E> {
        E item;
        Node<E> next;

        Node(E item) {
            this.item = item;
        }
    }

    /** First node that may be live (all nodes before it are dead); null when empty. */
    private transient Node<E> head;
    /** Last node of the chain (possibly dead). */
    private transient Node<E> tail;
    private final transient Object lock = new Object();

    public ConcurrentLinkedQueue() {
    }

    public ConcurrentLinkedQueue(Collection<? extends E> c) {
        for (E e : c) {
            Node<E> n = new Node<E>(Objects.requireNonNull(e));
            if (head == null) head = tail = n;
            else {
                tail.next = n;
                tail = n;
            }
        }
    }

    public boolean add(E e) {
        return offer(e);
    }

    public boolean offer(E e) {
        Node<E> n = new Node<E>(Objects.requireNonNull(e));
        synchronized (lock) {
            if (tail == null) {
                head = tail = n;
            } else {
                tail.next = n;
                tail = n;
                if (head == null) head = n;
            }
        }
        return true;
    }

    private Node<E> firstLive() {
        Node<E> p = head;
        while (p != null && p.item == null) p = p.next;
        head = p;
        return p;
    }

    public E poll() {
        synchronized (lock) {
            Node<E> p = firstLive();
            if (p == null) return null;
            E item = p.item;
            p.item = null;
            head = p.next;
            return item;
        }
    }

    public E peek() {
        synchronized (lock) {
            Node<E> p = firstLive();
            return p == null ? null : p.item;
        }
    }

    public boolean isEmpty() {
        return peek() == null;
    }

    public int size() {
        synchronized (lock) {
            int count = 0;
            for (Node<E> p = firstLive(); p != null; p = p.next) {
                if (p.item != null && ++count == Integer.MAX_VALUE) break;
            }
            return count;
        }
    }

    public boolean contains(Object o) {
        if (o == null) return false;
        synchronized (lock) {
            for (Node<E> p = firstLive(); p != null; p = p.next) {
                E item = p.item;
                if (item != null && o.equals(item)) return true;
            }
            return false;
        }
    }

    public boolean remove(Object o) {
        if (o == null) return false;
        synchronized (lock) {
            for (Node<E> p = firstLive(); p != null; p = p.next) {
                E item = p.item;
                if (item != null && o.equals(item)) {
                    p.item = null;
                    return true;
                }
            }
            return false;
        }
    }

    public boolean addAll(Collection<? extends E> c) {
        if (c == this) throw new IllegalArgumentException();
        Node<E> beginningOfTheEnd = null, last = null;
        for (E e : c) {
            Node<E> n = new Node<E>(Objects.requireNonNull(e));
            if (beginningOfTheEnd == null) beginningOfTheEnd = last = n;
            else {
                last.next = n;
                last = n;
            }
        }
        if (beginningOfTheEnd == null) return false;
        synchronized (lock) {
            if (tail == null) {
                head = beginningOfTheEnd;
            } else {
                tail.next = beginningOfTheEnd;
                if (head == null) head = beginningOfTheEnd;
            }
            tail = last;
        }
        return true;
    }

    public String toString() {
        StringBuilder sb = null;
        synchronized (lock) {
            for (Node<E> p = firstLive(); p != null; p = p.next) {
                E item = p.item;
                if (item != null) {
                    String s = item.toString();
                    if (sb == null) sb = new StringBuilder("[");
                    else sb.append(", ");
                    sb.append(s);
                }
            }
        }
        return sb == null ? "[]" : sb.append(']').toString();
    }

    public Object[] toArray() {
        synchronized (lock) {
            java.util.ArrayList<Object> l = new java.util.ArrayList<>();
            for (Node<E> p = firstLive(); p != null; p = p.next) {
                if (p.item != null) l.add(p.item);
            }
            return l.toArray();
        }
    }

    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
        Objects.requireNonNull(a);
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
        return new Itr();
    }

    private class Itr implements Iterator<E> {
        private Node<E> nextNode;
        private E nextItem;
        private Node<E> lastRet;

        Itr() {
            synchronized (lock) {
                Node<E> p = firstLive();
                if (p != null) {
                    nextNode = p;
                    nextItem = p.item;
                }
            }
        }

        public boolean hasNext() {
            return nextItem != null;
        }

        public E next() {
            synchronized (lock) {
                final Node<E> pred = nextNode;
                if (pred == null) throw new NoSuchElementException();
                lastRet = pred;
                Node<E> p = pred.next;
                while (p != null && p.item == null) p = p.next;
                nextNode = p;
                E x = nextItem;
                nextItem = (p == null) ? null : p.item;
                return x;
            }
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
                p = p.next;
            }
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

    public void clear() {
        bulkRemove(e -> true);
    }

    private boolean bulkRemove(Predicate<? super E> filter) {
        boolean removed = false;
        Node<E> p;
        synchronized (lock) {
            p = firstLive();
        }
        for (; p != null; ) {
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
                p = p.next;
            }
        }
        return removed;
    }

    public java.util.Spliterator<E> spliterator() {
        throw ModelStuck.unsupported("ConcurrentLinkedQueue.spliterator");
    }
}

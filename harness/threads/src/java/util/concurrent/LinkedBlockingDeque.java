/*
 * rocq-jvm model of java.util.concurrent.LinkedBlockingDeque (clean-room, Apache-2.0), for the
 * thread layer.
 *
 * An optionally bounded doubly linked list of non-null elements, guarded by one lock with two
 * conditions (not empty / not full), as in the JDK. The lock is the model's non-fair
 * ReentrantReadWriteLock write lock, whose conditions have the JDK's (AQS) FIFO semantics, so
 * that threads blocked in take/put are served in the order in which they started to wait.
 * Untimed put/take lock non-interruptibly and throw InterruptedException only when they have to
 * wait; the timed offer/poll lock interruptibly (an interrupted caller always gets
 * InterruptedException). A removed first (last) node links to itself, which the weakly
 * consistent iterators recognise (they restart from the current first / last node); iterators
 * prefetch their next element; forEach, removeIf/removeAll/retainAll work in batches of 64
 * nodes, calling the action / predicate outside the lock, as the JDK. addAll links all the
 * elements at once when they fit, else adds them one by one ("Deque full"). Not modelled:
 * spliterator (and so stream: STUCK), serialization.
 */
package java.util.concurrent;

import java.util.AbstractQueue;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantReadWriteLock;
import java.util.function.Consumer;
import java.util.function.Predicate;

public class LinkedBlockingDeque<E> extends AbstractQueue<E> implements BlockingDeque<E>, java.io.Serializable {
    private static final long serialVersionUID = -387911632671998426L;

    static final class Node<E> {
        E item;
        Node<E> prev;
        Node<E> next;
        Node(E x) { item = x; }
    }

    transient Node<E> first;
    transient Node<E> last;
    private transient int count;
    private final int capacity;
    final ReentrantReadWriteLock.WriteLock lock = new ReentrantReadWriteLock().writeLock();
    private final Condition notEmpty = lock.newCondition();
    private final Condition notFull = lock.newCondition();

    public LinkedBlockingDeque() {
        this(Integer.MAX_VALUE);
    }

    public LinkedBlockingDeque(int capacity) {
        if (capacity <= 0) throw new IllegalArgumentException();
        this.capacity = capacity;
    }

    public LinkedBlockingDeque(Collection<? extends E> c) {
        this(Integer.MAX_VALUE);
        addAll(c);
    }

    // ---- linking (lock held) ----

    private boolean linkFirst(Node<E> node) {
        if (count >= capacity) return false;
        Node<E> f = first;
        node.next = f;
        first = node;
        if (last == null) last = node;
        else f.prev = node;
        ++count;
        notEmpty.signal();
        return true;
    }

    private boolean linkLast(Node<E> node) {
        if (count >= capacity) return false;
        Node<E> l = last;
        node.prev = l;
        last = node;
        if (first == null) first = node;
        else l.next = node;
        ++count;
        notEmpty.signal();
        return true;
    }

    private E unlinkFirst() {
        Node<E> f = first;
        if (f == null) return null;
        Node<E> n = f.next;
        E item = f.item;
        f.item = null;
        f.next = f;           // self-link: iterators restart from first
        first = n;
        if (n == null) last = null;
        else n.prev = null;
        --count;
        notFull.signal();
        return item;
    }

    private E unlinkLast() {
        Node<E> l = last;
        if (l == null) return null;
        Node<E> p = l.prev;
        E item = l.item;
        l.item = null;
        l.prev = l;           // self-link
        last = p;
        if (p == null) first = null;
        else p.next = null;
        --count;
        notFull.signal();
        return item;
    }

    void unlink(Node<E> x) {
        Node<E> p = x.prev;
        Node<E> n = x.next;
        if (p == null) {
            unlinkFirst();
        } else if (n == null) {
            unlinkLast();
        } else {
            p.next = n;
            n.prev = p;
            x.item = null;
            --count;
            notFull.signal();
        }
    }

    // ---- BlockingDeque ----

    public void addFirst(E e) {
        if (!offerFirst(e)) throw new IllegalStateException("Deque full");
    }

    public void addLast(E e) {
        if (!offerLast(e)) throw new IllegalStateException("Deque full");
    }

    public boolean offerFirst(E e) {
        if (e == null) throw new NullPointerException();
        Node<E> node = new Node<E>(e);
        lock.lock();
        try {
            return linkFirst(node);
        } finally {
            lock.unlock();
        }
    }

    public boolean offerLast(E e) {
        if (e == null) throw new NullPointerException();
        Node<E> node = new Node<E>(e);
        lock.lock();
        try {
            return linkLast(node);
        } finally {
            lock.unlock();
        }
    }

    public void putFirst(E e) throws InterruptedException {
        if (e == null) throw new NullPointerException();
        Node<E> node = new Node<E>(e);
        lock.lock();
        try {
            while (!linkFirst(node)) notFull.await();
        } finally {
            lock.unlock();
        }
    }

    public void putLast(E e) throws InterruptedException {
        if (e == null) throw new NullPointerException();
        Node<E> node = new Node<E>(e);
        lock.lock();
        try {
            while (!linkLast(node)) notFull.await();
        } finally {
            lock.unlock();
        }
    }

    public boolean offerFirst(E e, long timeout, TimeUnit unit) throws InterruptedException {
        if (e == null) throw new NullPointerException();
        Node<E> node = new Node<E>(e);
        if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
        long nanos = unit.toNanos(timeout);
        lock.lockInterruptibly();
        try {
            while (!linkFirst(node)) {
                if (nanos <= 0L) return false;
                nanos = notFull.awaitNanos(nanos);
            }
            return true;
        } finally {
            lock.unlock();
        }
    }

    public boolean offerLast(E e, long timeout, TimeUnit unit) throws InterruptedException {
        if (e == null) throw new NullPointerException();
        Node<E> node = new Node<E>(e);
        if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
        long nanos = unit.toNanos(timeout);
        lock.lockInterruptibly();
        try {
            while (!linkLast(node)) {
                if (nanos <= 0L) return false;
                nanos = notFull.awaitNanos(nanos);
            }
            return true;
        } finally {
            lock.unlock();
        }
    }

    public E removeFirst() {
        E x = pollFirst();
        if (x == null) throw new NoSuchElementException();
        return x;
    }

    public E removeLast() {
        E x = pollLast();
        if (x == null) throw new NoSuchElementException();
        return x;
    }

    public E pollFirst() {
        lock.lock();
        try {
            return unlinkFirst();
        } finally {
            lock.unlock();
        }
    }

    public E pollLast() {
        lock.lock();
        try {
            return unlinkLast();
        } finally {
            lock.unlock();
        }
    }

    public E takeFirst() throws InterruptedException {
        lock.lock();
        try {
            E x;
            while ((x = unlinkFirst()) == null) notEmpty.await();
            return x;
        } finally {
            lock.unlock();
        }
    }

    public E takeLast() throws InterruptedException {
        lock.lock();
        try {
            E x;
            while ((x = unlinkLast()) == null) notEmpty.await();
            return x;
        } finally {
            lock.unlock();
        }
    }

    public E pollFirst(long timeout, TimeUnit unit) throws InterruptedException {
        if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
        long nanos = unit.toNanos(timeout);
        lock.lockInterruptibly();
        try {
            E x;
            while ((x = unlinkFirst()) == null) {
                if (nanos <= 0L) return null;
                nanos = notEmpty.awaitNanos(nanos);
            }
            return x;
        } finally {
            lock.unlock();
        }
    }

    public E pollLast(long timeout, TimeUnit unit) throws InterruptedException {
        if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
        long nanos = unit.toNanos(timeout);
        lock.lockInterruptibly();
        try {
            E x;
            while ((x = unlinkLast()) == null) {
                if (nanos <= 0L) return null;
                nanos = notEmpty.awaitNanos(nanos);
            }
            return x;
        } finally {
            lock.unlock();
        }
    }

    public E getFirst() {
        E x = peekFirst();
        if (x == null) throw new NoSuchElementException();
        return x;
    }

    public E getLast() {
        E x = peekLast();
        if (x == null) throw new NoSuchElementException();
        return x;
    }

    public E peekFirst() {
        lock.lock();
        try {
            return (first == null) ? null : first.item;
        } finally {
            lock.unlock();
        }
    }

    public E peekLast() {
        lock.lock();
        try {
            return (last == null) ? null : last.item;
        } finally {
            lock.unlock();
        }
    }

    public boolean removeFirstOccurrence(Object o) {
        if (o == null) return false;
        lock.lock();
        try {
            for (Node<E> p = first; p != null; p = p.next) {
                if (o.equals(p.item)) {
                    unlink(p);
                    return true;
                }
            }
            return false;
        } finally {
            lock.unlock();
        }
    }

    public boolean removeLastOccurrence(Object o) {
        if (o == null) return false;
        lock.lock();
        try {
            for (Node<E> p = last; p != null; p = p.prev) {
                if (o.equals(p.item)) {
                    unlink(p);
                    return true;
                }
            }
            return false;
        } finally {
            lock.unlock();
        }
    }

    // ---- BlockingQueue / Queue / stack ----

    public boolean add(E e) {
        addLast(e);
        return true;
    }

    public boolean offer(E e) { return offerLast(e); }

    public void put(E e) throws InterruptedException { putLast(e); }

    public boolean offer(E e, long timeout, TimeUnit unit) throws InterruptedException {
        return offerLast(e, timeout, unit);
    }

    public E remove() { return removeFirst(); }

    public E poll() { return pollFirst(); }

    public E take() throws InterruptedException { return takeFirst(); }

    public E poll(long timeout, TimeUnit unit) throws InterruptedException {
        return pollFirst(timeout, unit);
    }

    public E element() { return getFirst(); }

    public E peek() { return peekFirst(); }

    public int remainingCapacity() {
        lock.lock();
        try {
            return capacity - count;
        } finally {
            lock.unlock();
        }
    }

    public int drainTo(Collection<? super E> c) {
        return drainTo(c, Integer.MAX_VALUE);
    }

    public int drainTo(Collection<? super E> c, int maxElements) {
        Objects.requireNonNull(c);
        if (c == this) throw new IllegalArgumentException();
        if (maxElements <= 0) return 0;
        lock.lock();
        try {
            int n = Math.min(maxElements, count);
            for (int i = 0; i < n; i++) {
                c.add(first.item);    // add first, in case it throws
                unlinkFirst();
            }
            return n;
        } finally {
            lock.unlock();
        }
    }

    public void push(E e) { addFirst(e); }

    public E pop() { return removeFirst(); }

    public boolean remove(Object o) { return removeFirstOccurrence(o); }

    public int size() {
        lock.lock();
        try {
            return count;
        } finally {
            lock.unlock();
        }
    }

    public boolean contains(Object o) {
        if (o == null) return false;
        lock.lock();
        try {
            for (Node<E> p = first; p != null; p = p.next)
                if (o.equals(p.item)) return true;
            return false;
        } finally {
            lock.unlock();
        }
    }

    public boolean addAll(Collection<? extends E> c) {
        if (c == this) throw new IllegalArgumentException();
        if (c == null) throw new NullPointerException("Cannot invoke \"java.util.Collection.iterator()\" because \"c\" is null");
        Node<E> beg = null, end = null;
        int n = 0;
        for (E e : c) {
            Objects.requireNonNull(e);
            n++;
            Node<E> newNode = new Node<E>(e);
            if (beg == null) {
                beg = end = newNode;
            } else {
                end.next = newNode;
                newNode.prev = end;
                end = newNode;
            }
        }
        if (beg == null) return false;
        lock.lock();
        try {
            if (count + n <= capacity) {
                beg.prev = last;
                if (first == null) first = beg;
                else last.next = beg;
                last = end;
                count += n;
                notEmpty.signalAll();
                return true;
            }
        } finally {
            lock.unlock();
        }
        // does not fit: one by one, up to "Deque full"
        return super.addAll(c);
    }

    public Object[] toArray() {
        lock.lock();
        try {
            Object[] a = new Object[count];
            int k = 0;
            for (Node<E> p = first; p != null; p = p.next) a[k++] = p.item;
            return a;
        } finally {
            lock.unlock();
        }
    }

    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
        lock.lock();
        try {
            if (a == null) throw new NullPointerException("Cannot read the array length because \"a\" is null");
            if (a.length < count)
                a = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), count);
            int k = 0;
            for (Node<E> p = first; p != null; p = p.next) a[k++] = (T) p.item;
            if (a.length > k) a[k] = null;
            return a;
        } finally {
            lock.unlock();
        }
    }

    /** As the JDK (Helpers.collectionToString): from a toArray snapshot. */
    public String toString() {
        Object[] a = toArray();
        int size = a.length;
        if (size == 0) return "[]";
        StringBuilder sb = new StringBuilder();
        sb.append('[');
        for (int i = 0; i < size; i++) {
            Object e = a[i];
            String s;
            if (e == this) s = "(this Collection)";
            else s = (e == null || (s = e.toString()) == null) ? "null" : s;
            if (i > 0) sb.append(',').append(' ');
            sb.append(s);
        }
        return sb.append(']').toString();
    }

    public void clear() {
        lock.lock();
        try {
            for (Node<E> f = first; f != null; ) {
                f.item = null;
                Node<E> n = f.next;
                f.prev = null;
                f.next = null;
                f = n;
            }
            first = last = null;
            count = 0;
            notFull.signalAll();
        } finally {
            lock.unlock();
        }
    }

    /** The live successor of p: a self-linked p was removed as the first node; restart at first. */
    Node<E> succ(Node<E> p) {
        if (p == (p = p.next)) p = first;
        return p;
    }

    public Iterator<E> iterator() { return new Itr(); }

    public Iterator<E> descendingIterator() { return new DescendingItr(); }

    private abstract class AbstractItr implements Iterator<E> {
        Node<E> next;
        E nextItem;
        private Node<E> lastRet;

        abstract Node<E> firstNode();
        abstract Node<E> nextNode(Node<E> n);

        private Node<E> succ(Node<E> p) {
            if (p == (p = nextNode(p))) p = firstNode();
            return p;
        }

        AbstractItr() {
            lock.lock();
            try {
                if ((next = firstNode()) != null) nextItem = next.item;
            } finally {
                lock.unlock();
            }
        }

        public boolean hasNext() { return next != null; }

        public E next() {
            Node<E> p;
            if ((p = next) == null) throw new NoSuchElementException();
            lastRet = p;
            E x = nextItem;
            lock.lock();
            try {
                E e = null;
                for (p = nextNode(p); p != null && (e = p.item) == null; ) p = succ(p);
                next = p;
                nextItem = e;
            } finally {
                lock.unlock();
            }
            return x;
        }

        public void forEachRemaining(Consumer<? super E> action) {
            Objects.requireNonNull(action);
            Node<E> p;
            if ((p = next) == null) return;
            lastRet = p;
            next = null;
            final int batchSize = 64;
            Object[] es = null;
            int n, len = 1;
            do {
                lock.lock();
                try {
                    if (es == null) {
                        p = nextNode(p);
                        for (Node<E> q = p; q != null; q = succ(q))
                            if (q.item != null && ++len == batchSize) break;
                        es = new Object[len];
                        es[0] = nextItem;
                        nextItem = null;
                        n = 1;
                    } else {
                        n = 0;
                    }
                    for (; p != null && n < len; p = succ(p))
                        if ((es[n] = p.item) != null) {
                            lastRet = p;
                            n++;
                        }
                } finally {
                    lock.unlock();
                }
                for (int i = 0; i < n; i++) {
                    @SuppressWarnings("unchecked") E e = (E) es[i];
                    action.accept(e);
                }
            } while (n > 0 && p != null);
        }

        public void remove() {
            Node<E> n = lastRet;
            if (n == null) throw new IllegalStateException();
            lastRet = null;
            lock.lock();
            try {
                if (n.item != null) unlink(n);
            } finally {
                lock.unlock();
            }
        }
    }

    private class Itr extends AbstractItr {
        Itr() { }
        Node<E> firstNode() { return first; }
        Node<E> nextNode(Node<E> n) { return n.next; }
    }

    private class DescendingItr extends AbstractItr {
        DescendingItr() { }
        Node<E> firstNode() { return last; }
        Node<E> nextNode(Node<E> n) { return n.prev; }
    }

    public void forEach(Consumer<? super E> action) {
        Objects.requireNonNull(action);
        forEachFrom(action, null);
    }

    void forEachFrom(Consumer<? super E> action, Node<E> p) {
        final int batchSize = 64;
        Object[] es = null;
        int n, len = 0;
        do {
            lock.lock();
            try {
                if (es == null) {
                    if (p == null) p = first;
                    for (Node<E> q = p; q != null; q = succ(q))
                        if (q.item != null && ++len == batchSize) break;
                    es = new Object[len];
                }
                for (n = 0; p != null && n < len; p = succ(p))
                    if ((es[n] = p.item) != null) n++;
            } finally {
                lock.unlock();
            }
            for (int i = 0; i < n; i++) {
                @SuppressWarnings("unchecked") E e = (E) es[i];
                action.accept(e);
            }
        } while (n > 0 && p != null);
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

    @SuppressWarnings("unchecked")
    private boolean bulkRemove(Predicate<? super E> filter) {
        boolean removed = false;
        Node<E> p = null;
        Node<E>[] nodes = null;
        int n, len = 0;
        do {
            lock.lock();
            try {
                if (nodes == null) {
                    p = first;
                    for (Node<E> q = p; q != null; q = succ(q))
                        if (q.item != null && ++len == 64) break;
                    nodes = (Node<E>[]) new Node<?>[len];
                }
                for (n = 0; p != null && n < len; p = succ(p)) nodes[n++] = p;
            } finally {
                lock.unlock();
            }
            long deathRow = 0L;
            for (int i = 0; i < n; i++) {
                final E e;
                if ((e = nodes[i].item) != null && filter.test(e)) deathRow |= 1L << i;
            }
            if (deathRow != 0) {
                lock.lock();
                try {
                    for (int i = 0; i < n; i++) {
                        final Node<E> q;
                        if ((deathRow & (1L << i)) != 0L && (q = nodes[i]).item != null) {
                            unlink(q);
                            removed = true;
                        }
                        nodes[i] = null;
                    }
                } finally {
                    lock.unlock();
                }
            }
        } while (n > 0 && p != null);
        return removed;
    }
}

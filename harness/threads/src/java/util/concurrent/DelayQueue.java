/*
 * Clean-room model of java.util.concurrent.DelayQueue (from the Javadoc), for the thread layer:
 * an unbounded queue of Delayed elements kept in a binary heap ordered by compareTo (the same
 * array heap as java.util.PriorityQueue, so elements that compare equal come out in the same
 * order), guarded by this object's monitor. take() waits until the head's delay has expired,
 * on the model clock. Not modelled (STUCK): iterator order and spliterator (the JDK leaves the
 * order unspecified), drainTo with a limit.
 */
package java.util.concurrent;

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;

public class DelayQueue<E extends Delayed> extends AbstractCollection<E> {
    private Object[] queue = new Object[11];
    private int size;

    public DelayQueue() {
    }

    public DelayQueue(Collection<? extends E> c) {
        addAll(c);
    }

    @SuppressWarnings("unchecked")
    private E at(int i) {
        return (E) queue[i];
    }

    private void siftUp(int k, E x) {
        while (k > 0) {
            int parent = (k - 1) >>> 1;
            E e = at(parent);
            if (x.compareTo(e) >= 0) break;
            queue[k] = e;
            k = parent;
        }
        queue[k] = x;
    }

    private void siftDown(int k, E x) {
        int half = size >>> 1;
        while (k < half) {
            int child = (k << 1) + 1;
            E c = at(child);
            int right = child + 1;
            if (right < size && c.compareTo(at(right)) > 0) c = at(child = right);
            if (x.compareTo(c) <= 0) break;
            queue[k] = c;
            k = child;
        }
        queue[k] = x;
    }

    private E pollFirst() {
        E result = at(0);
        int n = --size;
        E x = at(n);
        queue[n] = null;
        if (n > 0) siftDown(0, x);
        return result;
    }

    private void removeAt(int i) {
        int s = --size;
        if (s == i) {
            queue[i] = null;
        } else {
            E moved = at(s);
            queue[s] = null;
            siftDown(i, moved);
            if (queue[i] == moved) siftUp(i, moved);
        }
    }

    public boolean add(E e) {
        return offer(e);
    }

    public synchronized boolean offer(E e) {
        if (e == null) throw new NullPointerException();
        if (size >= queue.length) {
            Object[] q = new Object[queue.length * 2];
            for (int i = 0; i < size; i++) q[i] = queue[i];
            queue = q;
        }
        siftUp(size++, e);
        notifyAll();
        return true;
    }

    public void put(E e) {
        offer(e);
    }

    public boolean offer(E e, long timeout, TimeUnit unit) {
        return offer(e);
    }

    public synchronized E poll() {
        if (size == 0) return null;
        return at(0).getDelay(TimeUnit.NANOSECONDS) > 0 ? null : pollFirst();
    }

    public synchronized E take() throws InterruptedException {
        for (;;) {
            if (size == 0) {
                wait();
                continue;
            }
            long delay = at(0).getDelay(TimeUnit.NANOSECONDS);
            if (delay <= 0L) return pollFirst();
            wait(Math.max(1L, (delay + 999999L) / 1000000L));
        }
    }

    public synchronized E poll(long timeout, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(timeout);
        long deadline = System.nanoTime() + nanos;
        for (;;) {
            if (size == 0) {
                if (nanos <= 0L) return null;
                wait(Math.max(1L, nanos / 1000000L));
            } else {
                long delay = at(0).getDelay(TimeUnit.NANOSECONDS);
                if (delay <= 0L) return pollFirst();
                if (nanos <= 0L) return null;
                wait(Math.max(1L, (Math.min(delay, nanos) + 999999L) / 1000000L));
            }
            nanos = deadline - System.nanoTime();
        }
    }

    public synchronized E peek() {
        return size == 0 ? null : at(0);
    }

    public E remove() {
        E x = poll();
        if (x == null) throw new NoSuchElementException();
        return x;
    }

    public E element() {
        E x = peek();
        if (x == null) throw new NoSuchElementException();
        return x;
    }

    public synchronized int size() {
        return size;
    }

    public int remainingCapacity() {
        return Integer.MAX_VALUE;
    }

    public synchronized boolean remove(Object o) {
        if (o != null) {
            for (int i = 0; i < size; i++) {
                if (o.equals(queue[i])) {
                    removeAt(i);
                    return true;
                }
            }
        }
        return false;
    }

    public synchronized void clear() {
        for (int i = 0; i < size; i++) queue[i] = null;
        size = 0;
    }

    /** Moves every expired element, in order, into c. */
    public synchronized int drainTo(Collection<? super E> c) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        int n = 0;
        while (size > 0 && at(0).getDelay(TimeUnit.NANOSECONDS) <= 0) {
            c.add(pollFirst());
            n++;
        }
        return n;
    }

    public int drainTo(Collection<? super E> c, int maxElements) {
        throw ModelStuckDq.unsupported("DelayQueue.drainTo(Collection, int)");
    }

    public synchronized Object[] toArray() {
        Object[] r = new Object[size];
        for (int i = 0; i < size; i++) r[i] = queue[i];
        return r;
    }

    public Iterator<E> iterator() {
        throw ModelStuckDq.unsupported("DelayQueue.iterator (unspecified order)");
    }
}

final class ModelStuckDq {
    private ModelStuckDq() {
    }

    static native RuntimeException unsupported(String what);
}

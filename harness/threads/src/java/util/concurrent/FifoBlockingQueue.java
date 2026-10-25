/*
 * The common clean-room model behind LinkedBlockingQueue and ArrayBlockingQueue (from their
 * Javadoc): a bounded FIFO of non-null elements guarded by this object's monitor; put/take wait
 * (on the thread layer), the timed forms use the model clock. Iterators walk a snapshot taken
 * when they are created (the JDK's are weakly consistent; they agree when the queue is not
 * changed by another thread during the iteration) and remove the element they returned.
 */
package java.util.concurrent;

import java.util.AbstractQueue;
import java.util.Collection;
import java.util.Iterator;
import java.util.NoSuchElementException;

abstract class FifoBlockingQueue<E> extends AbstractQueue<E> implements BlockingQueue<E>, java.io.Serializable {
    final int capacity;
    private Object[] items;
    private int head, count;

    FifoBlockingQueue(int capacity) {
        if (capacity <= 0) throw new IllegalArgumentException();
        this.capacity = capacity;
        this.items = new Object[Math.min(capacity, 16)];
    }

    @SuppressWarnings("unchecked")
    private E at(int i) {
        return (E) items[(head + i) % items.length];
    }

    private void enqueue(E e) {
        if (count == items.length) {
            Object[] n = new Object[Math.min(capacity, items.length * 2)];
            for (int i = 0; i < count; i++) n[i] = at(i);
            items = n;
            head = 0;
        }
        items[(head + count) % items.length] = e;
        count++;
        notifyAll();
    }

    private E dequeue() {
        E x = at(0);
        items[head] = null;
        head = (head + 1) % items.length;
        count--;
        notifyAll();
        return x;
    }

    private void removeAt(int i) {
        for (int j = i; j + 1 < count; j++) items[(head + j) % items.length] = items[(head + j + 1) % items.length];
        items[(head + count - 1) % items.length] = null;
        count--;
        notifyAll();
    }

    public synchronized int size() {
        return count;
    }

    public synchronized int remainingCapacity() {
        return capacity - count;
    }

    public synchronized boolean offer(E e) {
        if (e == null) throw new NullPointerException();
        if (count == capacity) return false;
        enqueue(e);
        return true;
    }

    public synchronized void put(E e) throws InterruptedException {
        if (e == null) throw new NullPointerException();
        if (Thread.interrupted()) throw new InterruptedException();
        while (count == capacity) wait();
        enqueue(e);
    }

    public synchronized boolean offer(E e, long timeout, TimeUnit unit) throws InterruptedException {
        if (e == null) throw new NullPointerException();
        long nanos = unit.toNanos(timeout);
        if (Thread.interrupted()) throw new InterruptedException();
        long deadline = System.nanoTime() + nanos;
        while (count == capacity) {
            if (nanos <= 0L) return false;
            wait(Math.max(1L, nanos / 1000000L));
            nanos = deadline - System.nanoTime();
        }
        enqueue(e);
        return true;
    }

    public synchronized E take() throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        while (count == 0) wait();
        return dequeue();
    }

    public synchronized E poll(long timeout, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(timeout);
        if (Thread.interrupted()) throw new InterruptedException();
        long deadline = System.nanoTime() + nanos;
        while (count == 0) {
            if (nanos <= 0L) return null;
            wait(Math.max(1L, nanos / 1000000L));
            nanos = deadline - System.nanoTime();
        }
        return dequeue();
    }

    public synchronized E poll() {
        return (count == 0) ? null : dequeue();
    }

    public synchronized E peek() {
        return (count == 0) ? null : at(0);
    }

    public synchronized boolean remove(Object o) {
        if (o == null) return false;
        for (int i = 0; i < count; i++) {
            if (o.equals(at(i))) {
                removeAt(i);
                return true;
            }
        }
        return false;
    }

    synchronized boolean removeIdentical(Object o) {
        for (int i = 0; i < count; i++) {
            if (at(i) == o) {
                removeAt(i);
                return true;
            }
        }
        return false;
    }

    public synchronized boolean contains(Object o) {
        if (o == null) return false;
        for (int i = 0; i < count; i++) {
            if (o.equals(at(i))) return true;
        }
        return false;
    }

    public synchronized Object[] toArray() {
        Object[] r = new Object[count];
        for (int i = 0; i < count; i++) r[i] = at(i);
        return r;
    }

    public synchronized void clear() {
        while (count > 0) dequeue();
    }

    public int drainTo(Collection<? super E> c) {
        return drainTo(c, Integer.MAX_VALUE);
    }

    public synchronized int drainTo(Collection<? super E> c, int maxElements) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        int n = 0;
        while (n < maxElements && count > 0) {
            c.add(dequeue());
            n++;
        }
        return n;
    }

    public Iterator<E> iterator() {
        final Object[] snap = toArray();
        return new Iterator<E>() {
            int i;
            Object last;

            public boolean hasNext() {
                return i < snap.length;
            }

            @SuppressWarnings("unchecked")
            public E next() {
                if (i >= snap.length) throw new NoSuchElementException();
                last = snap[i++];
                return (E) last;
            }

            public void remove() {
                if (last == null) throw new IllegalStateException();
                removeIdentical(last);
                last = null;
            }
        };
    }
}

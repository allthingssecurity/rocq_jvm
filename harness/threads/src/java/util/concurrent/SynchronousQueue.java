/*
 * Clean-room model of java.util.concurrent.SynchronousQueue (from the Javadoc): every insert
 * waits for a remove by another thread and vice versa; the queue never holds elements (size 0,
 * empty iterator, peek null). offer(e) succeeds only if a thread is waiting to take, poll() only
 * if a thread is waiting to put. Waiting takers and putters are matched in arrival order when
 * fair and most recent first otherwise (the JDK's queue and stack). Guarded by this monitor.
 */
package java.util.concurrent;

import java.util.AbstractQueue;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;

public class SynchronousQueue<E> extends AbstractQueue<E> implements BlockingQueue<E>, java.io.Serializable {
    private final boolean fair;

    /** A waiting taker or putter. */
    private static final class Waiter {
        Object item;       // putter: its element; taker: the element handed to it
        boolean matched;
        boolean cancelled;
    }

    private final java.util.ArrayList<Waiter> takers = new java.util.ArrayList<>();
    private final java.util.ArrayList<Waiter> putters = new java.util.ArrayList<>();

    public SynchronousQueue() {
        this(false);
    }

    public SynchronousQueue(boolean fair) {
        this.fair = fair;
    }

    /** The waiter to match next, removed from its list, or null. */
    private Waiter next(java.util.ArrayList<Waiter> l) {
        while (!l.isEmpty()) {
            Waiter w = fair ? l.remove(0) : l.remove(l.size() - 1);
            if (!w.cancelled) return w;
        }
        return null;
    }

    /** Hand e to a waiting taker; true if there was one. */
    private boolean handToTaker(E e) {
        Waiter w = next(takers);
        if (w == null) return false;
        w.item = e;
        w.matched = true;
        notifyAll();
        return true;
    }

    @SuppressWarnings("unchecked")
    private E takeFromPutter() {
        Waiter w = next(putters);
        if (w == null) return null;
        w.matched = true;
        notifyAll();
        return (E) w.item;
    }

    public synchronized boolean offer(E e) {
        if (e == null) throw new NullPointerException();
        return handToTaker(e);
    }

    public void put(E e) throws InterruptedException {
        if (e == null) throw new NullPointerException();
        transferPut(e, -1L);
    }

    public boolean offer(E e, long timeout, TimeUnit unit) throws InterruptedException {
        if (e == null) throw new NullPointerException();
        return transferPut(e, Math.max(0L, unit.toNanos(timeout)));
    }

    private synchronized boolean transferPut(E e, long nanos) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        if (handToTaker(e)) return true;
        if (nanos == 0L) return false;
        Waiter w = new Waiter();
        w.item = e;
        putters.add(w);
        long deadline = System.nanoTime() + nanos;
        try {
            while (!w.matched) {
                if (nanos < 0L) {
                    wait();
                } else {
                    long rem = deadline - System.nanoTime();
                    if (rem <= 0L) {
                        w.cancelled = true;
                        putters.remove(w);
                        return false;
                    }
                    wait(Math.max(1L, rem / 1000000L));
                }
            }
            return true;
        } catch (InterruptedException ie) {
            if (w.matched) {
                Thread.currentThread().interrupt();
                return true;
            }
            w.cancelled = true;
            putters.remove(w);
            throw ie;
        }
    }

    public E take() throws InterruptedException {
        return transferTake(-1L);
    }

    public E poll(long timeout, TimeUnit unit) throws InterruptedException {
        return transferTake(Math.max(0L, unit.toNanos(timeout)));
    }

    public synchronized E poll() {
        return takeFromPutter();
    }

    @SuppressWarnings("unchecked")
    private synchronized E transferTake(long nanos) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        E x = takeFromPutter();
        if (x != null) return x;
        if (nanos == 0L) return null;
        Waiter w = new Waiter();
        takers.add(w);
        long deadline = System.nanoTime() + nanos;
        try {
            while (!w.matched) {
                if (nanos < 0L) {
                    wait();
                } else {
                    long rem = deadline - System.nanoTime();
                    if (rem <= 0L) {
                        w.cancelled = true;
                        takers.remove(w);
                        return null;
                    }
                    wait(Math.max(1L, rem / 1000000L));
                }
            }
            return (E) w.item;
        } catch (InterruptedException ie) {
            if (w.matched) {
                Thread.currentThread().interrupt();
                return (E) w.item;
            }
            w.cancelled = true;
            takers.remove(w);
            throw ie;
        }
    }

    public boolean isEmpty() {
        return true;
    }

    public int size() {
        return 0;
    }

    public int remainingCapacity() {
        return 0;
    }

    public void clear() {
    }

    public boolean contains(Object o) {
        return false;
    }

    public boolean remove(Object o) {
        return false;
    }

    public boolean containsAll(Collection<?> c) {
        return c.isEmpty();
    }

    public boolean removeAll(Collection<?> c) {
        return false;
    }

    public boolean retainAll(Collection<?> c) {
        return false;
    }

    public E peek() {
        return null;
    }

    public Iterator<E> iterator() {
        return Collections.emptyIterator();
    }

    public Object[] toArray() {
        return new Object[0];
    }

    public <T> T[] toArray(T[] a) {
        if (a.length > 0) a[0] = null;
        return a;
    }

    public String toString() {
        return "[]";
    }

    public int drainTo(Collection<? super E> c) {
        return drainTo(c, Integer.MAX_VALUE);
    }

    public synchronized int drainTo(Collection<? super E> c, int maxElements) {
        if (c == null) throw new NullPointerException();
        if (c == this) throw new IllegalArgumentException();
        int n = 0;
        for (E e; n < maxElements && (e = takeFromPutter()) != null; n++) c.add(e);
        return n;
    }
}

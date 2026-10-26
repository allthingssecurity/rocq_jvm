/*
 * rocq-jvm model of java.util.concurrent.Exchanger (clean-room, Apache-2.0), for the thread
 * layer, over a private monitor: one slot (the JDK's slot; its arena only spreads contention and
 * pairs threads in some order, which is a timing race). A thread that finds a waiting partner
 * takes its item and hands over its own; otherwise it waits in the slot until a partner comes,
 * it is interrupted (InterruptedException; it leaves the slot) or the timed form times out
 * (TimeoutException). The interrupt status is checked first (an interrupted thread does not
 * exchange); an interrupt that arrives after the exchange is kept. null items are allowed.
 */
package java.util.concurrent;

public class Exchanger<V> {
    private static final Object NULL_ITEM = new Object();

    private static final class Node {
        final Object item;
        Object match;
        Node(Object item) { this.item = item; }
    }

    private final Object lock = new Object();
    private Node slot;

    public Exchanger() {
    }

    /** The partner's item (translated), or throws. */
    private Object doExchange(Object item, boolean timed, long ns) throws InterruptedException, TimeoutException {
        if (Thread.interrupted()) throw new InterruptedException();
        synchronized (lock) {
            Node q = slot;
            if (q != null) {
                slot = null;
                q.match = item;
                lock.notifyAll();
                return q.item;
            }
            Node p = new Node(item);
            slot = p;
            long end = timed ? System.nanoTime() + ns : 0L;
            boolean interrupted = false;
            while (p.match == null) {
                if (interrupted || (timed && (ns = end - System.nanoTime()) <= 0L)) {
                    slot = null;
                    if (interrupted) throw new InterruptedException();
                    throw new TimeoutException();
                }
                try {
                    if (!timed) lock.wait();
                    else lock.wait(Math.max(1L, ns / 1000000L));
                } catch (InterruptedException e) {
                    interrupted = true;
                }
            }
            if (interrupted) Thread.currentThread().interrupt();   // after the exchange: kept
            return p.match;
        }
    }

    @SuppressWarnings("unchecked")
    public V exchange(V x) throws InterruptedException {
        Object item = (x == null) ? NULL_ITEM : x;
        Object v;
        try {
            v = doExchange(item, false, 0L);
        } catch (TimeoutException e) {
            throw new Error(e);
        }
        return (v == NULL_ITEM) ? null : (V) v;
    }

    @SuppressWarnings("unchecked")
    public V exchange(V x, long timeout, TimeUnit unit) throws InterruptedException, TimeoutException {
        Object item = (x == null) ? NULL_ITEM : x;
        if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
        long ns = unit.toNanos(timeout);
        Object v = doExchange(item, true, ns);
        return (v == NULL_ITEM) ? null : (V) v;
    }
}

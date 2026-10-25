/*
 * Clean-room model of java.util.concurrent.Semaphore (from the Javadoc), for the thread layer.
 * Permits are an int guarded by this object's monitor. A fair semaphore hands permits out in
 * arrival order: a waiting thread may take permits only when it is the oldest waiter, and a new
 * arrival waits while others wait. A non-fair one lets any thread take available permits.
 * tryAcquire() without a timeout barges even when fair (Javadoc). Interruption while waiting
 * throws InterruptedException (acquireUninterruptibly keeps waiting and re-asserts the interrupt
 * status); timed waits use the thread layer's clock.
 */
package java.util.concurrent;

public class Semaphore implements java.io.Serializable {
    private final boolean fair;
    private int permits;
    /** Arrival tickets of the threads waiting now, oldest first. */
    private long[] queue = new long[4];
    private int qlen;
    private long nextTicket;

    public Semaphore(int permits) {
        this(permits, false);
    }

    public Semaphore(int permits, boolean fair) {
        this.permits = permits;
        this.fair = fair;
    }

    private static void check(int n) {
        if (n < 0) throw new IllegalArgumentException();
    }

    private long enqueue() {
        if (qlen == queue.length) {
            long[] q = new long[qlen * 2];
            for (int i = 0; i < qlen; i++) q[i] = queue[i];
            queue = q;
        }
        long t = nextTicket++;
        queue[qlen++] = t;
        return t;
    }

    private void dequeue(long t) {
        int i = 0;
        while (i < qlen && queue[i] != t) i++;
        for (; i + 1 < qlen; i++) queue[i] = queue[i + 1];
        if (qlen > 0) qlen--;
        notifyAll();
    }

    private boolean mayTake(long ticket, int n) {
        return permits >= n && (!fair || queue[0] == ticket);
    }

    /** Wait for n permits; timeoutNanos < 0: no timeout. False on timeout. */
    private synchronized boolean acquireImpl(int n, boolean interruptible, long timeoutNanos) throws InterruptedException {
        if (interruptible && Thread.interrupted()) throw new InterruptedException();
        long ticket = enqueue();
        boolean interrupted = false;
        long deadline = (timeoutNanos >= 0L) ? System.nanoTime() + timeoutNanos : 0L;
        long nanos = timeoutNanos;
        try {
            while (!mayTake(ticket, n)) {
                try {
                    if (timeoutNanos < 0L) {
                        wait();
                    } else {
                        if (nanos <= 0L) return false;
                        wait(Math.max(1L, nanos / 1000000L));
                        nanos = deadline - System.nanoTime();
                    }
                } catch (InterruptedException e) {
                    if (interruptible) throw e;
                    interrupted = true;
                }
            }
            permits -= n;
            return true;
        } finally {
            dequeue(ticket);
            if (interrupted) Thread.currentThread().interrupt();
        }
    }

    public void acquire() throws InterruptedException {
        acquireImpl(1, true, -1L);
    }

    public void acquire(int permits) throws InterruptedException {
        check(permits);
        acquireImpl(permits, true, -1L);
    }

    public void acquireUninterruptibly() {
        try {
            acquireImpl(1, false, -1L);
        } catch (InterruptedException e) {
            throw new IllegalStateException(e);   // not reached
        }
    }

    public void acquireUninterruptibly(int permits) {
        check(permits);
        try {
            acquireImpl(permits, false, -1L);
        } catch (InterruptedException e) {
            throw new IllegalStateException(e);   // not reached
        }
    }

    public synchronized boolean tryAcquire() {
        if (permits >= 1) {
            permits--;
            return true;
        }
        return false;
    }

    public synchronized boolean tryAcquire(int permits) {
        check(permits);
        if (this.permits >= permits) {
            this.permits -= permits;
            return true;
        }
        return false;
    }

    public boolean tryAcquire(long timeout, TimeUnit unit) throws InterruptedException {
        return acquireImpl(1, true, Math.max(0L, unit.toNanos(timeout)));
    }

    public boolean tryAcquire(int permits, long timeout, TimeUnit unit) throws InterruptedException {
        check(permits);
        return acquireImpl(permits, true, Math.max(0L, unit.toNanos(timeout)));
    }

    public synchronized void release() {
        permits++;
        notifyAll();
    }

    public synchronized void release(int permits) {
        check(permits);
        this.permits += permits;
        notifyAll();
    }

    public synchronized int availablePermits() {
        return permits;
    }

    /** Javadoc: takes all available permits, or releases the negative ones; zero remain. */
    public synchronized int drainPermits() {
        int n = permits;
        permits = 0;
        if (n < 0) notifyAll();
        return n;
    }

    protected synchronized void reducePermits(int reduction) {
        check(reduction);
        permits -= reduction;
    }

    public boolean isFair() {
        return fair;
    }

    public final synchronized boolean hasQueuedThreads() {
        return qlen > 0;
    }

    public final synchronized int getQueueLength() {
        return qlen;
    }

    public String toString() {
        return super.toString() + "[Permits = " + availablePermits() + "]";
    }
}

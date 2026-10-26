/*
 * Clean-room model of ReentrantLock over a monitor. A fair lock is granted in arrival order (a
 * thread that finds others waiting queues behind them); a non-fair one lets a newcomer take a free
 * lock. tryLock() barges even when fair (Javadoc). lock() is not interruptible (an interrupt during
 * lock() is remembered and re-asserted, as in AQS); lockInterruptibly() is. Conditions:
 * newCondition() (await / signal / signalAll, timed awaits, awaitUntil(Date)).
 */
package java.util.concurrent.locks;

import java.util.concurrent.TimeUnit;

public class ReentrantLock implements Lock, java.io.Serializable {
    private Thread owner;
    private int holds;
    private final Object mon = new Object();
    private final boolean fair;
    /** Arrival tickets of the threads waiting for the lock, oldest first. */
    private final java.util.ArrayList<Long> queue = new java.util.ArrayList<>();
    private final java.util.ArrayList<Thread> queuedThreads = new java.util.ArrayList<>();
    private long nextTicket;

    public ReentrantLock() { this.fair = false; }
    public ReentrantLock(boolean fair) { this.fair = fair; }

    /** May the waiter with this ticket take the free lock now? Fair: only the oldest waiter. */
    private boolean mayTake(long ticket) {
        return owner == null && (!fair || queue.get(0).longValue() == ticket);
    }

    /** Acquire for me (mon held). timeoutNanos < 0: no timeout. False on timeout. */
    private boolean acquire(Thread me, boolean interruptible, long timeoutNanos, int count) throws InterruptedException {
        if (owner == me) { holds += count; return true; }
        if (owner == null && (!fair || queue.isEmpty())) { owner = me; holds = count; return true; }
        long ticket = nextTicket++;
        queue.add(ticket);
        queuedThreads.add(me);
        boolean interrupted = false;
        long deadline = timeoutNanos >= 0 ? System.nanoTime() + timeoutNanos : 0L;
        long nanos = timeoutNanos;
        try {
            while (!mayTake(ticket)) {
                try {
                    if (timeoutNanos < 0) {
                        mon.wait();
                    } else {
                        if (nanos <= 0) return false;
                        mon.wait(Math.max(1, nanos / 1000000L));
                        nanos = deadline - System.nanoTime();
                    }
                } catch (InterruptedException e) {
                    if (interruptible) throw e;
                    interrupted = true;
                }
            }
            owner = me;
            holds = count;
            return true;
        } finally {
            queue.remove(Long.valueOf(ticket));
            queuedThreads.remove(me);
            mon.notifyAll();
            if (interrupted) me.interrupt();
        }
    }

    public void lock() {
        Thread me = Thread.currentThread();
        synchronized (mon) {
            try { acquire(me, false, -1L, 1); } catch (InterruptedException e) { throw new IllegalStateException(e); }
        }
    }
    public void lockInterruptibly() throws InterruptedException {
        Thread me = Thread.currentThread();
        if (Thread.interrupted()) throw new InterruptedException();
        synchronized (mon) { acquire(me, true, -1L, 1); }
    }
    /** Javadoc: barges even when the lock is fair. */
    public boolean tryLock() {
        Thread me = Thread.currentThread();
        synchronized (mon) {
            if (owner == null || owner == me) { owner = me; holds++; return true; }
            return false;
        }
    }
    public boolean tryLock(long timeout, TimeUnit unit) throws InterruptedException {
        Thread me = Thread.currentThread();
        if (Thread.interrupted()) throw new InterruptedException();
        long nanos = Math.max(0L, unit.toNanos(timeout));
        synchronized (mon) { return acquire(me, true, nanos, 1); }
    }
    public void unlock() {
        synchronized (mon) {
            if (owner != Thread.currentThread()) throw new IllegalMonitorStateException();
            if (--holds == 0) { owner = null; mon.notifyAll(); }
        }
    }
    public final boolean hasQueuedThreads() { synchronized (mon) { return !queue.isEmpty(); } }
    public final boolean hasQueuedThread(Thread thread) { synchronized (mon) { return queuedThreads.contains(thread); } }
    public final int getQueueLength() { synchronized (mon) { return queue.size(); } }
    protected Thread getOwner() { synchronized (mon) { return owner; } }
    public boolean isLocked() { synchronized (mon) { return owner != null; } }
    public boolean isHeldByCurrentThread() { synchronized (mon) { return owner == Thread.currentThread(); } }
    public int getHoldCount() { synchronized (mon) { return owner == Thread.currentThread() ? holds : 0; } }
    public final boolean isFair() { return fair; }
    public Condition newCondition() { return new Cond(this); }

    // release fully, wait on the condition's monitor, then reacquire with the same hold count
    private int releaseAll() {
        synchronized (mon) {
            if (owner != Thread.currentThread()) throw new IllegalMonitorStateException();
            int h = holds; holds = 0; owner = null; mon.notifyAll(); return h;
        }
    }
    private void reacquire(int h) {
        Thread me = Thread.currentThread();
        synchronized (mon) {
            try { acquire(me, false, -1L, h); } catch (InterruptedException e) { throw new IllegalStateException(e); }
        }
    }
    private boolean ownedByMe() { synchronized (mon) { return owner == Thread.currentThread(); } }

    static final class Cond implements Condition {
        private final ReentrantLock lock;
        private int generation;   // bumped by signalAll; signal hands out one permit
        private int permits;
        private int waiting;
        Cond(ReentrantLock lock) { this.lock = lock; }

        public void await() throws InterruptedException {
            if (Thread.interrupted()) throw new InterruptedException();
            if (!lock.ownedByMe()) throw new IllegalMonitorStateException();
            InterruptedException ie = null;
            int h;
            synchronized (this) {
                h = lock.releaseAll();       // lock order: condition monitor, then the lock's monitor
                int gen = generation;
                waiting++;
                try {
                    while (permits == 0 && gen == generation) wait();
                    if (gen == generation) permits--;
                } catch (InterruptedException e) { ie = e; }
                waiting--;
            }
            lock.reacquire(h);
            if (ie != null) throw ie;
        }
        public void awaitUninterruptibly() {
            boolean interrupted = false;
            for (;;) {
                try { await(); break; } catch (InterruptedException e) { interrupted = true; }
            }
            if (interrupted) Thread.currentThread().interrupt();
        }
        public long awaitNanos(long nanos) throws InterruptedException {
            if (Thread.interrupted()) throw new InterruptedException();
            if (!lock.ownedByMe()) throw new IllegalMonitorStateException();
            InterruptedException ie = null;
            int h;
            long rem = nanos;
            synchronized (this) {
                h = lock.releaseAll();
                int gen = generation;
                waiting++;
                long deadline = System.nanoTime() + nanos;
                try {
                    while (permits == 0 && gen == generation && rem > 0) {
                        wait(Math.max(1, rem / 1000000L));
                        rem = deadline - System.nanoTime();
                    }
                    if (gen == generation && permits > 0) permits--;
                } catch (InterruptedException e) { ie = e; }
                waiting--;
            }
            lock.reacquire(h);
            if (ie != null) throw ie;
            return rem;
        }
        public boolean await(long time, TimeUnit unit) throws InterruptedException { return awaitNanos(unit.toNanos(time)) > 0; }
        /** As awaitNanos, with a deadline on currentTimeMillis; true unless the deadline passed first. */
        public boolean awaitUntil(java.util.Date deadline) throws InterruptedException {
            if (deadline == null) throw new NullPointerException("Cannot invoke \"java.util.Date.getTime()\" because \"deadline\" is null");
            long abstime = deadline.getTime();
            if (Thread.interrupted()) throw new InterruptedException();
            if (!lock.ownedByMe()) throw new IllegalMonitorStateException();
            InterruptedException ie = null;
            int h;
            boolean signalled = false;
            synchronized (this) {
                h = lock.releaseAll();
                int gen = generation;
                waiting++;
                try {
                    long now;
                    while (permits == 0 && gen == generation && (now = System.currentTimeMillis()) < abstime) {
                        wait(abstime - now);
                    }
                    if (gen != generation) signalled = true;
                    else if (permits > 0) { permits--; signalled = true; }
                } catch (InterruptedException e) { ie = e; }
                waiting--;
            }
            lock.reacquire(h);
            if (ie != null) throw ie;
            return signalled;
        }
        public void signal() {
            if (!lock.ownedByMe()) throw new IllegalMonitorStateException();
            synchronized (this) { if (waiting > permits) { permits++; notifyAll(); } }
        }
        public void signalAll() {
            if (!lock.ownedByMe()) throw new IllegalMonitorStateException();
            synchronized (this) { generation++; permits = 0; notifyAll(); }
        }
    }
}

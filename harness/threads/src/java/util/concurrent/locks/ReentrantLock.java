/*
 * Clean-room model of ReentrantLock (non-fair) over a monitor. lock() is not interruptible (an
 * interrupt during lock() is remembered and re-asserted, as in AQS); lockInterruptibly() is.
 * Conditions: newCondition() (await / signal / signalAll). Timed operations are STUCK.
 */
package java.util.concurrent.locks;

import java.util.concurrent.TimeUnit;

public class ReentrantLock implements Lock, java.io.Serializable {
    private Thread owner;
    private int holds;
    private final Object mon = new Object();

    public ReentrantLock() { }
    public ReentrantLock(boolean fair) { if (fair) fairNotModelled0(); }
    private native void fairNotModelled0();

    public void lock() {
        Thread me = Thread.currentThread();
        boolean interrupted = false;
        synchronized (mon) {
            while (owner != null && owner != me) {
                try { mon.wait(); } catch (InterruptedException e) { interrupted = true; }
            }
            owner = me; holds++;
        }
        if (interrupted) me.interrupt();
    }
    public void lockInterruptibly() throws InterruptedException {
        Thread me = Thread.currentThread();
        if (Thread.interrupted()) throw new InterruptedException();
        synchronized (mon) {
            while (owner != null && owner != me) mon.wait();
            owner = me; holds++;
        }
    }
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
        long nanos = unit.toNanos(timeout);
        synchronized (mon) {
            long deadline = System.nanoTime() + nanos;
            while (owner != null && owner != me) {
                if (nanos <= 0) return false;
                mon.wait(Math.max(1, nanos / 1000000L));
                nanos = deadline - System.nanoTime();
            }
            owner = me; holds++;
            return true;
        }
    }
    public void unlock() {
        synchronized (mon) {
            if (owner != Thread.currentThread()) throw new IllegalMonitorStateException();
            if (--holds == 0) { owner = null; mon.notifyAll(); }
        }
    }
    public boolean isLocked() { synchronized (mon) { return owner != null; } }
    public boolean isHeldByCurrentThread() { synchronized (mon) { return owner == Thread.currentThread(); } }
    public int getHoldCount() { synchronized (mon) { return owner == Thread.currentThread() ? holds : 0; } }
    public final boolean isFair() { return false; }
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
        boolean interrupted = false;
        synchronized (mon) {
            while (owner != null && owner != me) {
                try { mon.wait(); } catch (InterruptedException e) { interrupted = true; }
            }
            owner = me; holds = h;
        }
        if (interrupted) me.interrupt();
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
        public boolean awaitUntil(java.util.Date deadline) throws InterruptedException { return awaitUntil0(); }
        private native boolean awaitUntil0();
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

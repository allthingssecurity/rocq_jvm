/*
 * rocq-jvm model of java.util.concurrent.locks.StampedLock (clean-room, Apache-2.0), for the
 * thread layer, over a monitor.
 *
 * Stamps are observable values, so the state word is the JDK's: bits 0-6 count read holds (127 =
 * overflow, the extra holds counted in readerOverflow), bit 7 is the write bit, the rest a version
 * that a write release advances (state starts at 256; tryOptimisticRead returns the version
 * bits; validate compares them). Bad stamps throw IllegalMonitorStateException, as the JDK.
 *
 * Blocking follows the JDK's queue discipline: a thread that cannot take the lock queues FIFO, a
 * reader arriving behind a queued reader joins that reader's group (released together), and only
 * the first queued node may take the lock; newcomers barge as in the JDK (writeLock/tryWriteLock/
 * readLock/tryReadLock/the interruptible forms try first; the timed tryReadLock and a readLock
 * that finds the fast path closed only when nobody is queued). Untimed non-interruptible
 * acquires remember an interrupt and re-assert it; the interruptible and timed ones check the
 * interrupt status first and throw InterruptedException. A timed acquire that times out
 * returns 0. Views asReadLock/asWriteLock/asReadWriteLock as the JDK (newCondition unsupported).
 * toString is Object.toString plus the state (the identity hash is STUCK in the machine).
 */
package java.util.concurrent.locks;

import java.util.ArrayList;
import java.util.concurrent.TimeUnit;

public class StampedLock implements java.io.Serializable {
    private static final long serialVersionUID = -6001602636862214147L;

    private static final int LG_READERS = 7;
    private static final long RUNIT = 1L;
    private static final long WBIT = 1L << LG_READERS;
    private static final long RBITS = WBIT - 1L;
    private static final long RFULL = RBITS - 1L;
    private static final long ABITS = RBITS | WBIT;
    private static final long SBITS = ~RBITS;
    private static final long RSAFE = ~(3L << (LG_READERS - 1));
    private static final long ORIGIN = WBIT << 1;
    private static final long INTERRUPTED = 1L;

    private long state;
    private int readerOverflow;
    private final Object mon = new Object();

    /** A queued writer, or a group of readers (its first member is the leader). */
    private static final class Node {
        final boolean reader;
        boolean done;          // the group was released, or its leader gave up
        Node(boolean reader) { this.reader = reader; }
    }
    private final ArrayList<Node> queue = new ArrayList<>();

    transient ReadLockView readLockView;
    transient WriteLockView writeLockView;
    transient ReadWriteLockView readWriteLockView;

    public StampedLock() { state = ORIGIN; }

    // ---- state transitions (mon held) ----

    private long tryAcquireWrite() {
        long s = state;
        if ((s & ABITS) == 0L) return state = s | WBIT;
        return 0L;
    }
    private long tryAcquireRead() {
        long s = state, m = s & ABITS;
        if (m < RFULL) return state = s + RUNIT;
        if (m == WBIT) return 0L;
        ++readerOverflow;      // m == RFULL: count the hold in readerOverflow
        return s;
    }
    private static long unlockWriteState(long s) {
        return ((s += WBIT) == 0L) ? ORIGIN : s;
    }
    private long releaseWrite(long s) {
        long nextState = state = unlockWriteState(s);
        mon.notifyAll();
        return nextState;
    }
    /** One read hold less (state has read holds); returns the new state. */
    private long releaseRead(long s) {
        long m = s & RBITS;
        if (m < RFULL) {
            state = s - RUNIT;
            if (m == RUNIT) mon.notifyAll();
        } else if (readerOverflow > 0) {
            readerOverflow--;
        } else {
            state = s - RUNIT;
        }
        return state;
    }

    /** Waits on mon until the deadline (timed) or a notification; false when the deadline has passed. */
    private boolean park(boolean timed, long deadline) throws InterruptedException {
        if (!timed) { mon.wait(); return true; }
        long nanos = deadline - System.nanoTime();
        if (nanos <= 0L) return false;
        mon.wait(Math.max(1L, nanos / 1000000L));
        return true;
    }

    /** Queued write acquire; the stamp, 0 on timeout, or INTERRUPTED. */
    private long acquireWrite(boolean interruptible, boolean timed, long deadline) {
        Thread me = Thread.currentThread();
        synchronized (mon) {
            long ns;
            if ((ns = tryAcquireWrite()) != 0L) return ns;
            Node node = new Node(false);
            queue.add(node);
            boolean interrupted = false;
            for (;;) {
                if (queue.get(0) == node && (ns = tryAcquireWrite()) != 0L) {
                    queue.remove(0);
                    mon.notifyAll();
                    if (interrupted) me.interrupt();
                    return ns;
                }
                try {
                    if (!park(timed, deadline)) break;
                } catch (InterruptedException e) {
                    interrupted = true;
                    if (interruptible) break;
                }
            }
            queue.remove(node);
            mon.notifyAll();
            return (interrupted || Thread.interrupted()) ? INTERRUPTED : 0L;
        }
    }

    /** Queued read acquire; the stamp, 0 on timeout, or INTERRUPTED. */
    private long acquireRead(boolean interruptible, boolean timed, long deadline) {
        Thread me = Thread.currentThread();
        synchronized (mon) {
            boolean interrupted = false;
            long ns;
            for (;;) {
                if (queue.isEmpty() && (ns = tryAcquireRead()) != 0L) {
                    if (interrupted) me.interrupt();
                    return ns;
                }
                Node last = queue.isEmpty() ? null : queue.get(queue.size() - 1);
                if (last != null && last.reader && !last.done) {
                    // join the queued group; once it is released (or its leader gave up) try again
                    while (!last.done) {
                        boolean timedOut = false;
                        try {
                            if (!park(timed, deadline)) timedOut = true;
                        } catch (InterruptedException e) {
                            interrupted = true;
                            if (interruptible) timedOut = true;
                        }
                        if (timedOut && !last.done) return (interrupted || Thread.interrupted()) ? INTERRUPTED : 0L;
                    }
                    ns = tryAcquireRead();
                    if (interrupted) { me.interrupt(); interrupted = false; }
                    if (ns != 0L) return ns;
                    continue;   // queue again
                }
                Node node = new Node(true);
                queue.add(node);
                for (;;) {
                    if (queue.get(0) == node && (ns = tryAcquireRead()) != 0L) {
                        queue.remove(0);
                        node.done = true;
                        mon.notifyAll();
                        if (interrupted) me.interrupt();
                        return ns;
                    }
                    boolean giveUp = false;
                    try {
                        if (!park(timed, deadline)) giveUp = true;
                    } catch (InterruptedException e) {
                        interrupted = true;
                        if (interruptible) giveUp = true;
                    }
                    if (giveUp) {
                        queue.remove(node);
                        node.done = true;
                        mon.notifyAll();
                        return (interrupted || Thread.interrupted()) ? INTERRUPTED : 0L;
                    }
                }
            }
        }
    }

    // ---- write lock ----

    public long writeLock() {
        synchronized (mon) {
            long ns;
            if ((ns = tryAcquireWrite()) != 0L) return ns;
        }
        return acquireWrite(false, false, 0L);
    }
    public long tryWriteLock() {
        synchronized (mon) { return tryAcquireWrite(); }
    }
    public long tryWriteLock(long time, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(time);
        if (!Thread.interrupted()) {
            long nextState;
            synchronized (mon) {
                if ((nextState = tryAcquireWrite()) != 0L) return nextState;
            }
            if (nanos <= 0L) return 0L;
            nextState = acquireWrite(true, true, System.nanoTime() + nanos);
            if (nextState != INTERRUPTED) return nextState;
        }
        throw new InterruptedException();
    }
    public long writeLockInterruptibly() throws InterruptedException {
        long nextState;
        if (!Thread.interrupted()) {
            synchronized (mon) {
                if ((nextState = tryAcquireWrite()) != 0L) return nextState;
            }
            if ((nextState = acquireWrite(true, false, 0L)) != INTERRUPTED) return nextState;
        }
        throw new InterruptedException();
    }

    // ---- read lock ----

    public long readLock() {
        synchronized (mon) {
            long s = state;
            if ((s & RSAFE) == s) return state = s + RUNIT;   // the JDK's fast path: no writer, < 64 readers
        }
        return acquireRead(false, false, 0L);
    }
    public long tryReadLock() {
        synchronized (mon) { return tryAcquireRead(); }
    }
    public long tryReadLock(long time, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(time);
        if (!Thread.interrupted()) {
            long nextState;
            synchronized (mon) {
                if (queue.isEmpty() && (nextState = tryAcquireRead()) != 0L) return nextState;
            }
            if (nanos <= 0L) return 0L;
            nextState = acquireRead(true, true, System.nanoTime() + nanos);
            if (nextState != INTERRUPTED) return nextState;
        }
        throw new InterruptedException();
    }
    public long readLockInterruptibly() throws InterruptedException {
        long nextState;
        if (!Thread.interrupted()) {
            synchronized (mon) {
                if ((nextState = tryAcquireRead()) != 0L) return nextState;
            }
            if ((nextState = acquireRead(true, false, 0L)) != INTERRUPTED) return nextState;
        }
        throw new InterruptedException();
    }

    // ---- optimistic reads ----

    public long tryOptimisticRead() {
        synchronized (mon) {
            long s = state;
            return ((s & WBIT) == 0L) ? (s & SBITS) : 0L;
        }
    }
    public boolean validate(long stamp) {
        synchronized (mon) { return (stamp & SBITS) == (state & SBITS); }
    }

    // ---- unlocking ----

    public void unlockWrite(long stamp) {
        synchronized (mon) {
            if (state != stamp || (stamp & WBIT) == 0L) throw new IllegalMonitorStateException();
            releaseWrite(stamp);
        }
    }
    public void unlockRead(long stamp) {
        synchronized (mon) {
            long s = state;
            if ((stamp & RBITS) != 0L && (s & SBITS) == (stamp & SBITS) && (s & RBITS) != 0L) {
                releaseRead(s);
                return;
            }
        }
        throw new IllegalMonitorStateException();
    }
    public void unlock(long stamp) {
        if ((stamp & WBIT) != 0L) unlockWrite(stamp);
        else unlockRead(stamp);
    }

    // ---- conversions ----

    public long tryConvertToWriteLock(long stamp) {
        synchronized (mon) {
            long a = stamp & ABITS, s = state, m;
            if ((s & SBITS) != (stamp & SBITS)) return 0L;
            if ((m = s & ABITS) == 0L) {
                if (a != 0L) return 0L;
                return state = s | WBIT;
            } else if (m == WBIT) {
                return (a != m) ? 0L : stamp;
            } else if (m == RUNIT && a != 0L) {
                return state = s - RUNIT + WBIT;
            }
            return 0L;
        }
    }
    public long tryConvertToReadLock(long stamp) {
        synchronized (mon) {
            long a = stamp & ABITS, s = state;
            if ((s & SBITS) != (stamp & SBITS)) return 0L;
            if (a >= WBIT) {
                if (s != stamp) return 0L;
                long nextState = state = unlockWriteState(s) + RUNIT;
                mon.notifyAll();
                return nextState;
            } else if (a == 0L) {
                return tryAcquireRead();   // not write-locked here (the version bits matched a non-write stamp)
            } else {
                if ((s & ABITS) == 0L) return 0L;
                return stamp;
            }
        }
    }
    public long tryConvertToOptimisticRead(long stamp) {
        synchronized (mon) {
            long a = stamp & ABITS, s = state, m;
            if ((s & SBITS) != (stamp & SBITS)) return 0L;
            if (a >= WBIT) {
                if (s != stamp) return 0L;
                return releaseWrite(s);
            } else if (a == 0L) {
                return stamp;
            } else if ((m = s & ABITS) == 0L) {
                return 0L;
            }
            return releaseRead(s) & SBITS;
        }
    }

    public boolean tryUnlockWrite() {
        synchronized (mon) {
            long s = state;
            if ((s & WBIT) != 0L) { releaseWrite(s); return true; }
            return false;
        }
    }
    public boolean tryUnlockRead() {
        synchronized (mon) {
            long s = state, m = s & ABITS;
            if (m != 0L && m < WBIT) { releaseRead(s); return true; }
            return false;
        }
    }

    // ---- inspection ----

    private int getReadLockCount(long s) {
        long readers;
        if ((readers = s & RBITS) >= RFULL) readers = RFULL + readerOverflow;
        return (int) readers;
    }
    public boolean isWriteLocked() { synchronized (mon) { return (state & WBIT) != 0L; } }
    public boolean isReadLocked() { synchronized (mon) { return (state & RBITS) != 0L; } }
    public static boolean isWriteLockStamp(long stamp) { return (stamp & ABITS) == WBIT; }
    public static boolean isReadLockStamp(long stamp) { return (stamp & RBITS) != 0L; }
    public static boolean isLockStamp(long stamp) { return (stamp & ABITS) != 0L; }
    public static boolean isOptimisticReadStamp(long stamp) { return (stamp & ABITS) == 0L && stamp != 0L; }
    public int getReadLockCount() { synchronized (mon) { return getReadLockCount(state); } }

    public String toString() {
        long s; int rc;
        synchronized (mon) { s = state; rc = getReadLockCount(s); }
        return super.toString() + ((s & ABITS) == 0L ? "[Unlocked]" : (s & WBIT) != 0L ? "[Write-locked]" : "[Read-locks:" + rc + "]");
    }

    // ---- views ----

    public Lock asReadLock() {
        ReadLockView v;
        if ((v = readLockView) != null) return v;
        return readLockView = new ReadLockView();
    }
    public Lock asWriteLock() {
        WriteLockView v;
        if ((v = writeLockView) != null) return v;
        return writeLockView = new WriteLockView();
    }
    public ReadWriteLock asReadWriteLock() {
        ReadWriteLockView v;
        if ((v = readWriteLockView) != null) return v;
        return readWriteLockView = new ReadWriteLockView();
    }

    final class ReadLockView implements Lock {
        public void lock() { readLock(); }
        public void lockInterruptibly() throws InterruptedException { readLockInterruptibly(); }
        public boolean tryLock() { return tryReadLock() != 0L; }
        public boolean tryLock(long time, TimeUnit unit) throws InterruptedException { return tryReadLock(time, unit) != 0L; }
        public void unlock() { unstampedUnlockRead(); }
        public Condition newCondition() { throw new UnsupportedOperationException(); }
    }
    final class WriteLockView implements Lock {
        public void lock() { writeLock(); }
        public void lockInterruptibly() throws InterruptedException { writeLockInterruptibly(); }
        public boolean tryLock() { return tryWriteLock() != 0L; }
        public boolean tryLock(long time, TimeUnit unit) throws InterruptedException { return tryWriteLock(time, unit) != 0L; }
        public void unlock() { unstampedUnlockWrite(); }
        public Condition newCondition() { throw new UnsupportedOperationException(); }
    }
    final class ReadWriteLockView implements ReadWriteLock {
        public Lock readLock() { return asReadLock(); }
        public Lock writeLock() { return asWriteLock(); }
    }

    final void unstampedUnlockWrite() {
        synchronized (mon) {
            long s = state;
            if ((s & WBIT) == 0L) throw new IllegalMonitorStateException();
            releaseWrite(s);
        }
    }
    final void unstampedUnlockRead() {
        synchronized (mon) {
            long s = state;
            if ((s & RBITS) > 0L) { releaseRead(s); return; }
        }
        throw new IllegalMonitorStateException();
    }
}

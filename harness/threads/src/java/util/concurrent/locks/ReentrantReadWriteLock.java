/*
 * rocq-jvm model of java.util.concurrent.locks.ReentrantReadWriteLock (clean-room, Apache-2.0),
 * for the thread layer, over a monitor (the Sync object) instead of AQS/CAS.
 *
 * The state word is the JDK's: the low 16 bits count write holds, the high 16 bits read holds.
 * Per-thread read hold counts follow the JDK's bookkeeping (a "first reader" with its own count,
 * the other threads' counts in a table), because it is observable (getReadHoldCount, and which
 * unlock throws IllegalMonitorStateException after a Condition wait of a write holder that also
 * held read holds). Acquisition follows the AQS discipline: an arriving thread tries first
 * (non-fair: writers barge, readers barge unless the first queued thread is a writer, and a
 * reentrant read never waits; fair: nobody barges past a queued thread, except reentrant reads
 * and reads by the write holder), else it queues FIFO; only the first queued thread may take the
 * lock. Readers released together form a group in the JDK (signalNextIfShared); here every
 * queued thread rechecks when notified, with the same outcome. tryLock() barges even when fair.
 * Untimed non-interruptible acquires remember an interrupt and re-assert it; lockInterruptibly
 * and the timed tryLock check the interrupt status first. 65535 holds: Error("Maximum lock
 * count exceeded").
 *
 * Conditions (write lock only): FIFO wait queue; signal moves the first waiter to the tail of
 * the lock queue (as AQS's ConditionObject); await releases the whole state and reacquires it.
 * await / awaitUninterruptibly / awaitNanos / await(time, unit) / awaitUntil(Date), hasWaiters,
 * getWaitQueueLength, getWaitingThreads. Not modelled: serialization. toString of the lock and
 * its views starts with Object.toString (identity hash: STUCK in the machine).
 */
package java.util.concurrent.locks;

import java.util.ArrayList;
import java.util.Collection;
import java.util.concurrent.TimeUnit;

public class ReentrantReadWriteLock implements ReadWriteLock, java.io.Serializable {
    private static final long serialVersionUID = -6992448646407690164L;

    private final ReentrantReadWriteLock.ReadLock readerLock;
    private final ReentrantReadWriteLock.WriteLock writerLock;
    final Sync sync;

    public ReentrantReadWriteLock() {
        this(false);
    }

    public ReentrantReadWriteLock(boolean fair) {
        sync = new Sync(fair);
        readerLock = new ReadLock(this);
        writerLock = new WriteLock(this);
    }

    public ReentrantReadWriteLock.WriteLock writeLock() { return writerLock; }
    public ReentrantReadWriteLock.ReadLock readLock() { return readerLock; }

    /** A thread waiting in the lock queue (or in a condition's queue, cond = true). */
    static final class Node {
        final Thread waiter;
        final boolean shared;
        boolean cond;
        Node(Thread waiter, boolean shared) { this.waiter = waiter; this.shared = shared; }
    }

    /** The synchronizer; its monitor guards every field. */
    static final class Sync implements java.io.Serializable {
        static final int SHARED_SHIFT = 16;
        static final int SHARED_UNIT = (1 << SHARED_SHIFT);
        static final int MAX_COUNT = (1 << SHARED_SHIFT) - 1;
        static final int EXCLUSIVE_MASK = (1 << SHARED_SHIFT) - 1;
        static int sharedCount(int c) { return c >>> SHARED_SHIFT; }
        static int exclusiveCount(int c) { return c & EXCLUSIVE_MASK; }

        final boolean fair;
        int state;
        Thread owner;
        Thread firstReader;
        int firstReaderHoldCount;
        /** Read hold counts of the threads other than firstReader (the JDK's readHolds). */
        private final ArrayList<Thread> holdThreads = new ArrayList<>();
        private final ArrayList<int[]> holdCounts = new ArrayList<>();
        /** The lock queue, oldest first. */
        final ArrayList<Node> queue = new ArrayList<>();

        Sync(boolean fair) { this.fair = fair; }

        private int holdIndex(Thread t) {
            for (int i = 0; i < holdThreads.size(); i++) if (holdThreads.get(i) == t) return i;
            return -1;
        }
        int holdsOf(Thread t) {
            int i = holdIndex(t);
            return i < 0 ? 0 : holdCounts.get(i)[0];
        }
        void setHolds(Thread t, int c) {
            int i = holdIndex(t);
            if (c == 0) {
                if (i >= 0) { holdThreads.remove(i); holdCounts.remove(i); }
            } else if (i >= 0) {
                holdCounts.get(i)[0] = c;
            } else {
                holdThreads.add(t);
                holdCounts.add(new int[] { c });
            }
        }

        boolean hasQueuedPredecessors(Thread me) {
            return !queue.isEmpty() && queue.get(0).waiter != me;
        }
        boolean apparentlyFirstQueuedIsExclusive() {
            return !queue.isEmpty() && !queue.get(0).shared;
        }
        boolean readerShouldBlock(Thread me) {
            return fair ? hasQueuedPredecessors(me) : apparentlyFirstQueuedIsExclusive();
        }
        boolean writerShouldBlock(Thread me) {
            return fair && hasQueuedPredecessors(me);
        }

        // ---- the JDK's tryAcquire / tryRelease family (monitor held) ----

        boolean tryRelease(Thread me, int releases) {
            if (owner != me) throw new IllegalMonitorStateException();
            int nextc = state - releases;
            boolean free = exclusiveCount(nextc) == 0;
            if (free) owner = null;
            state = nextc;
            return free;
        }

        boolean tryAcquire(Thread me, int acquires) {
            int c = state;
            int w = exclusiveCount(c);
            if (c != 0) {
                if (w == 0 || me != owner) return false;
                if (w + exclusiveCount(acquires) > MAX_COUNT) throw new Error("Maximum lock count exceeded");
                state = c + acquires;
                return true;
            }
            if (writerShouldBlock(me)) return false;
            state = c + acquires;
            owner = me;
            return true;
        }

        boolean tryReleaseShared(Thread me) {
            if (firstReader == me) {
                if (firstReaderHoldCount == 1) firstReader = null;
                else firstReaderHoldCount--;
            } else {
                int count = holdsOf(me);
                if (count <= 1) {
                    setHolds(me, 0);
                    if (count <= 0) throw unmatchedUnlockException();
                } else {
                    setHolds(me, count - 1);
                }
            }
            int nextc = state - SHARED_UNIT;
            state = nextc;
            return nextc == 0;
        }

        private static IllegalMonitorStateException unmatchedUnlockException() {
            return new IllegalMonitorStateException("attempt to unlock read lock, not locked by current thread");
        }

        private void recordRead(Thread me, int r) {
            if (r == 0) {
                firstReader = me;
                firstReaderHoldCount = 1;
            } else if (firstReader == me) {
                firstReaderHoldCount++;
            } else {
                setHolds(me, holdsOf(me) + 1);
            }
        }

        int tryAcquireShared(Thread me) {
            int c = state;
            if (exclusiveCount(c) != 0 && owner != me) return -1;
            int r = sharedCount(c);
            if (!readerShouldBlock(me) && r < MAX_COUNT) {
                state = c + SHARED_UNIT;
                recordRead(me, r);
                return 1;
            }
            return fullTryAcquireShared(me);
        }

        private int fullTryAcquireShared(Thread me) {
            int c = state;
            if (exclusiveCount(c) != 0) {
                if (owner != me) return -1;
                // the write holder never blocks on the read lock
            } else if (readerShouldBlock(me)) {
                // only a reentrant read may proceed
                if (firstReader != me && holdsOf(me) == 0) return -1;
            }
            if (sharedCount(c) == MAX_COUNT) throw new Error("Maximum lock count exceeded");
            state = c + SHARED_UNIT;
            recordRead(me, sharedCount(c));
            return 1;
        }

        boolean tryWriteLock(Thread me) {
            int c = state;
            if (c != 0) {
                int w = exclusiveCount(c);
                if (w == 0 || me != owner) return false;
                if (w == MAX_COUNT) throw new Error("Maximum lock count exceeded");
            }
            state = c + 1;
            owner = me;
            return true;
        }

        boolean tryReadLock(Thread me) {
            int c = state;
            if (exclusiveCount(c) != 0 && owner != me) return false;
            int r = sharedCount(c);
            if (r == MAX_COUNT) throw new Error("Maximum lock count exceeded");
            state = c + SHARED_UNIT;
            recordRead(me, r);
            return true;
        }

        // ---- the AQS acquire loop (monitor held) ----

        /**
         * Acquires for me: node null (or not queued) = a thread that tries before it queues; a
         * queued node tries only when it is first. 1: acquired; 0: timed out (or an interrupt
         * of a non-interruptible acquire, which is re-asserted); -1: interrupted (interruptible).
         */
        int acquire(Thread me, Node node, boolean shared, int arg, boolean interruptible, boolean timed, long deadline) {
            boolean interrupted = false;
            for (;;) {
                boolean queued = node != null && queue.contains(node);
                if (!queued || queue.get(0) == node) {
                    boolean acquired;
                    try {
                        acquired = shared ? (tryAcquireShared(me) >= 0) : tryAcquire(me, arg);
                    } catch (Error | RuntimeException ex) {
                        cancel(node, interrupted, false);
                        throw ex;
                    }
                    if (acquired) {
                        if (queued) {
                            queue.remove(node);
                            notifyAll();
                        }
                        if (interrupted) me.interrupt();
                        return 1;
                    }
                }
                if (!queued) {
                    if (node == null) node = new Node(me, shared);
                    queue.add(node);
                    continue;
                }
                try {
                    if (!timed) {
                        wait();
                    } else {
                        long nanos = deadline - System.nanoTime();
                        if (nanos <= 0L) break;
                        wait(Math.max(1L, nanos / 1000000L));
                    }
                } catch (InterruptedException e) {
                    interrupted = true;
                    if (interruptible) break;
                }
            }
            return cancel(node, interrupted, interruptible);
        }

        private int cancel(Node node, boolean interrupted, boolean interruptible) {
            if (node != null && queue.remove(node)) notifyAll();
            if (interrupted) {
                if (interruptible) return -1;
                Thread.currentThread().interrupt();
            }
            return 0;
        }

        // ---- exported operations ----

        synchronized void acquireWrite() {
            Thread me = Thread.currentThread();
            if (!tryAcquire(me, 1)) acquire(me, null, false, 1, false, false, 0L);
        }
        synchronized boolean acquireWriteInterruptibly() {
            Thread me = Thread.currentThread();
            return Thread.interrupted() || (!tryAcquire(me, 1) && acquire(me, null, false, 1, true, false, 0L) < 0);
        }
        /** 1 acquired, 0 timed out, -1 interrupted. */
        synchronized int acquireWriteNanos(long nanosTimeout) {
            Thread me = Thread.currentThread();
            if (Thread.interrupted()) return -1;
            if (tryAcquire(me, 1)) return 1;
            if (nanosTimeout <= 0L) return 0;
            return acquire(me, null, false, 1, true, true, System.nanoTime() + nanosTimeout);
        }
        synchronized void releaseWrite() {
            if (tryRelease(Thread.currentThread(), 1)) notifyAll();
        }
        synchronized void acquireRead() {
            Thread me = Thread.currentThread();
            if (tryAcquireShared(me) < 0) acquire(me, null, true, 1, false, false, 0L);
        }
        synchronized boolean acquireReadInterruptibly() {
            Thread me = Thread.currentThread();
            return Thread.interrupted() || (tryAcquireShared(me) < 0 && acquire(me, null, true, 1, true, false, 0L) < 0);
        }
        synchronized int acquireReadNanos(long nanosTimeout) {
            Thread me = Thread.currentThread();
            if (Thread.interrupted()) return -1;
            if (tryAcquireShared(me) >= 0) return 1;
            if (nanosTimeout <= 0L) return 0;
            return acquire(me, null, true, 1, true, true, System.nanoTime() + nanosTimeout);
        }
        synchronized void releaseRead() {
            if (tryReleaseShared(Thread.currentThread())) notifyAll();
        }
        synchronized boolean tryWriteLock() { return tryWriteLock(Thread.currentThread()); }
        synchronized boolean tryReadLock() { return tryReadLock(Thread.currentThread()); }

        synchronized boolean isHeldExclusively() { return owner == Thread.currentThread(); }
        synchronized Thread getOwner() { return exclusiveCount(state) == 0 ? null : owner; }
        synchronized int getReadLockCount() { return sharedCount(state); }
        synchronized boolean isWriteLocked() { return exclusiveCount(state) != 0; }
        synchronized int getWriteHoldCount() { return owner == Thread.currentThread() ? exclusiveCount(state) : 0; }
        synchronized int getReadHoldCount() {
            if (sharedCount(state) == 0) return 0;
            Thread me = Thread.currentThread();
            if (firstReader == me) return firstReaderHoldCount;
            return holdsOf(me);
        }
        synchronized int getCount() { return state; }

        synchronized boolean hasQueuedThreads() { return !queue.isEmpty(); }
        synchronized boolean isQueued(Thread thread) {
            if (thread == null) throw new NullPointerException();
            for (Node n : queue) if (n.waiter == thread) return true;
            return false;
        }
        synchronized int getQueueLength() { return queue.size(); }
        /** 0: all, 1: writers, 2: readers; from the most recently queued to the oldest (as AQS). */
        synchronized Collection<Thread> queuedThreads(int which) {
            ArrayList<Thread> list = new ArrayList<>();
            for (int i = queue.size() - 1; i >= 0; i--) {
                Node n = queue.get(i);
                if (which == 0 || (which == 1) == !n.shared) list.add(n.waiter);
            }
            return list;
        }
    }

    /** The write lock's Condition (AQS ConditionObject semantics). */
    static final class Cond implements Condition, java.io.Serializable {
        private final Sync sync;
        private final ArrayList<Node> waiters = new ArrayList<>();
        Cond(Sync sync) { this.sync = sync; }

        boolean isOwnedBy(Sync s) { return s == sync; }

        /** enableWait: queue a node and release the whole state; IMSE when the lock is not held. */
        private int enableWait(Thread me, Node node) {
            if (sync.owner == me) {
                node.cond = true;
                waiters.add(node);
                int savedState = sync.state;
                sync.tryRelease(me, savedState);
                sync.notifyAll();
                return savedState;
            }
            throw new IllegalMonitorStateException();
        }

        /** Leaves the condition queue unless signalled meanwhile; true if it left (cancelled). */
        private boolean cancelWait(Node node) {
            if (node.cond) {
                node.cond = false;
                waiters.remove(node);
                return true;
            }
            return false;
        }

        /**
         * Waits until signalled (the node is in the lock queue), or interrupted / past the
         * deadline (mode 0: untimed and interruptible; 1: uninterruptible; 2: nanoTime deadline;
         * 3: currentTimeMillis deadline). Returns {interrupted, cancelled}.
         */
        private boolean[] block(Node node, int mode, long deadline) {
            boolean interrupted = false, cancelled = false;
            while (node.cond) {
                if (mode != 1 && interrupted) {
                    cancelled = cancelWait(node);
                    break;
                }
                try {
                    if (mode == 0 || mode == 1) {
                        sync.wait();
                    } else {
                        long ms;
                        if (mode == 2) {
                            long nanos = deadline - System.nanoTime();
                            if (nanos <= 0L) { cancelled = cancelWait(node); break; }
                            ms = Math.max(1L, nanos / 1000000L);
                        } else {
                            long now = System.currentTimeMillis();
                            if (now >= deadline) { cancelled = cancelWait(node); break; }
                            ms = deadline - now;
                        }
                        sync.wait(ms);
                    }
                } catch (InterruptedException e) {
                    interrupted = true;
                }
            }
            return new boolean[] { interrupted, cancelled };
        }

        /** Reacquire with the saved state (non-interruptible; a cancelled node tries before queueing). */
        private void reacquire(Thread me, Node node, int savedState) {
            sync.acquire(me, node, false, savedState, false, false, 0L);
        }

        public void awaitUninterruptibly() {
            Thread me = Thread.currentThread();
            boolean interrupted;
            synchronized (sync) {
                Node node = new Node(me, false);
                int savedState = enableWait(me, node);
                interrupted = block(node, 1, 0L)[0];
                reacquire(me, node, savedState);
            }
            if (interrupted) me.interrupt();
        }

        public void await() throws InterruptedException {
            if (Thread.interrupted()) throw new InterruptedException();
            Thread me = Thread.currentThread();
            boolean[] r;
            synchronized (sync) {
                Node node = new Node(me, false);
                int savedState = enableWait(me, node);
                r = block(node, 0, 0L);
                reacquire(me, node, savedState);
            }
            if (r[0]) {
                if (r[1]) throw new InterruptedException();
                me.interrupt();
            }
        }

        public long awaitNanos(long nanosTimeout) throws InterruptedException {
            if (Thread.interrupted()) throw new InterruptedException();
            Thread me = Thread.currentThread();
            boolean[] r;
            long deadline;
            synchronized (sync) {
                Node node = new Node(me, false);
                int savedState = enableWait(me, node);
                long nanos = (nanosTimeout < 0L) ? 0L : nanosTimeout;
                deadline = System.nanoTime() + nanos;
                r = block(node, 2, deadline);
                reacquire(me, node, savedState);
            }
            finishTimed(me, r);
            long remaining = deadline - System.nanoTime();
            return (remaining <= nanosTimeout) ? remaining : Long.MIN_VALUE;
        }

        private static void finishTimed(Thread me, boolean[] r) throws InterruptedException {
            if (r[1]) {
                if (r[0]) throw new InterruptedException();
            } else if (r[0]) {
                me.interrupt();
            }
        }

        public boolean awaitUntil(java.util.Date deadline) throws InterruptedException {
            if (deadline == null) throw new NullPointerException("Cannot invoke \"java.util.Date.getTime()\" because \"deadline\" is null");
            long abstime = deadline.getTime();
            if (Thread.interrupted()) throw new InterruptedException();
            Thread me = Thread.currentThread();
            boolean[] r;
            synchronized (sync) {
                Node node = new Node(me, false);
                int savedState = enableWait(me, node);
                r = block(node, 3, abstime);
                reacquire(me, node, savedState);
            }
            finishTimed(me, r);
            return !r[1];
        }

        public boolean await(long time, TimeUnit unit) throws InterruptedException {
            if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
            long nanosTimeout = unit.toNanos(time);
            if (Thread.interrupted()) throw new InterruptedException();
            Thread me = Thread.currentThread();
            boolean[] r;
            synchronized (sync) {
                Node node = new Node(me, false);
                int savedState = enableWait(me, node);
                long nanos = (nanosTimeout < 0L) ? 0L : nanosTimeout;
                r = block(node, 2, System.nanoTime() + nanos);
                reacquire(me, node, savedState);
            }
            finishTimed(me, r);
            return !r[1];
        }

        private void doSignal(boolean all) {
            while (!waiters.isEmpty()) {
                Node n = waiters.remove(0);
                n.cond = false;
                sync.queue.add(n);
                if (!all) break;
            }
            sync.notifyAll();
        }

        public void signal() {
            synchronized (sync) {
                if (sync.owner != Thread.currentThread()) throw new IllegalMonitorStateException();
                if (!waiters.isEmpty()) doSignal(false);
            }
        }

        public void signalAll() {
            synchronized (sync) {
                if (sync.owner != Thread.currentThread()) throw new IllegalMonitorStateException();
                if (!waiters.isEmpty()) doSignal(true);
            }
        }

        boolean hasWaiters() {
            synchronized (sync) {
                if (sync.owner != Thread.currentThread()) throw new IllegalMonitorStateException();
                return !waiters.isEmpty();
            }
        }

        int getWaitQueueLength() {
            synchronized (sync) {
                if (sync.owner != Thread.currentThread()) throw new IllegalMonitorStateException();
                return waiters.size();
            }
        }

        Collection<Thread> getWaitingThreads() {
            synchronized (sync) {
                if (sync.owner != Thread.currentThread()) throw new IllegalMonitorStateException();
                ArrayList<Thread> list = new ArrayList<>();
                for (Node n : waiters) list.add(n.waiter);
                return list;
            }
        }
    }

    public static class ReadLock implements Lock, java.io.Serializable {
        private static final long serialVersionUID = -5992448646407690164L;
        private final Sync sync;

        protected ReadLock(ReentrantReadWriteLock lock) {
            sync = lock.sync;
        }

        public void lock() { sync.acquireRead(); }

        public void lockInterruptibly() throws InterruptedException {
            if (sync.acquireReadInterruptibly()) throw new InterruptedException();
        }

        public boolean tryLock() { return sync.tryReadLock(); }

        public boolean tryLock(long timeout, TimeUnit unit) throws InterruptedException {
            if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
            int stat = sync.acquireReadNanos(unit.toNanos(timeout));
            if (stat < 0) throw new InterruptedException();
            return stat > 0;
        }

        public void unlock() { sync.releaseRead(); }

        public Condition newCondition() { throw new UnsupportedOperationException(); }

        public String toString() {
            int r = sync.getReadLockCount();
            return super.toString() + "[Read locks = " + r + "]";
        }
    }

    public static class WriteLock implements Lock, java.io.Serializable {
        private static final long serialVersionUID = -4992448646407690164L;
        private final Sync sync;

        protected WriteLock(ReentrantReadWriteLock lock) {
            sync = lock.sync;
        }

        public void lock() { sync.acquireWrite(); }

        public void lockInterruptibly() throws InterruptedException {
            if (sync.acquireWriteInterruptibly()) throw new InterruptedException();
        }

        public boolean tryLock() { return sync.tryWriteLock(); }

        public boolean tryLock(long timeout, TimeUnit unit) throws InterruptedException {
            if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
            int stat = sync.acquireWriteNanos(unit.toNanos(timeout));
            if (stat < 0) throw new InterruptedException();
            return stat > 0;
        }

        public void unlock() { sync.releaseWrite(); }

        public Condition newCondition() { return new Cond(sync); }

        public String toString() {
            Thread o = sync.getOwner();
            return super.toString() + ((o == null) ? "[Unlocked]" : "[Locked by thread " + o.getName() + "]");
        }

        public boolean isHeldByCurrentThread() { return sync.isHeldExclusively(); }

        public int getHoldCount() { return sync.getWriteHoldCount(); }
    }

    public final boolean isFair() { return sync.fair; }
    protected Thread getOwner() { return sync.getOwner(); }
    public int getReadLockCount() { return sync.getReadLockCount(); }
    public boolean isWriteLocked() { return sync.isWriteLocked(); }
    public boolean isWriteLockedByCurrentThread() { return sync.isHeldExclusively(); }
    public int getWriteHoldCount() { return sync.getWriteHoldCount(); }
    public int getReadHoldCount() { return sync.getReadHoldCount(); }
    protected Collection<Thread> getQueuedWriterThreads() { return sync.queuedThreads(1); }
    protected Collection<Thread> getQueuedReaderThreads() { return sync.queuedThreads(2); }
    public final boolean hasQueuedThreads() { return sync.hasQueuedThreads(); }
    public final boolean hasQueuedThread(Thread thread) { return sync.isQueued(thread); }
    public final int getQueueLength() { return sync.getQueueLength(); }
    protected Collection<Thread> getQueuedThreads() { return sync.queuedThreads(0); }

    /** The JDK's checks: null, not an AQS ConditionObject ("not owner"), another lock's ("Not owner"). */
    private Cond own(Condition condition) {
        if (condition == null) throw new NullPointerException();
        // in the JDK the conditions of ReentrantLock and of this class are AQS ConditionObjects
        if (!(condition instanceof Cond) && !(condition instanceof ReentrantLock.Cond))
            throw new IllegalArgumentException("not owner");
        if (!(condition instanceof Cond) || !((Cond) condition).isOwnedBy(sync))
            throw new IllegalArgumentException("Not owner");
        return (Cond) condition;
    }

    public boolean hasWaiters(Condition condition) { return own(condition).hasWaiters(); }
    public int getWaitQueueLength(Condition condition) { return own(condition).getWaitQueueLength(); }
    protected Collection<Thread> getWaitingThreads(Condition condition) { return own(condition).getWaitingThreads(); }

    public String toString() {
        int c = sync.getCount();
        int w = Sync.exclusiveCount(c);
        int r = Sync.sharedCount(c);
        return super.toString() + "[Write locks = " + w + ", Read locks = " + r + "]";
    }
}

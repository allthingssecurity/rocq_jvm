// ReentrantReadWriteLock (fair / non-fair, views, reentrancy, downgrading, queue inspection,
// write-lock Conditions incl. awaitUntil), Condition.awaitUntil of ReentrantLock, LockSupport,
// CyclicBarrier, Phaser (incl. tiers), Exchanger, LinkedBlockingDeque, ExecutorService.invokeAny
// and timed invokeAll under the thread layer. Results do not depend on the schedule: threads
// are ordered by waiting for observable states (queue lengths, waiting parties, blockers) or by
// 100 ms sleeps; only values that every schedule produces are returned.
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;
import java.util.function.BooleanSupplier;

public class LockTests2 {
    static int small(int n) { return Math.floorMod(n, 10); }

    static void until(BooleanSupplier c) throws InterruptedException {
        while (!c.getAsBoolean()) Thread.sleep(1);
    }

    static String ex(Throwable t) {
        if (t == null) return "null";
        return t.getClass().getName() + "(" + t.getMessage() + ")";
    }

    static String names(Collection<Thread> ts) {
        StringBuilder b = new StringBuilder("[");
        for (Thread t : ts) b.append(t.getName()).append(' ');
        return b.append(']').toString();
    }

    /** Exposes the protected inspection methods. */
    static final class RW extends ReentrantReadWriteLock {
        RW(boolean fair) { super(fair); }
        String owner() { Thread o = getOwner(); return o == null ? "none" : o.getName(); }
        String queued() { return names(getQueuedThreads()) + names(getQueuedReaderThreads()) + names(getQueuedWriterThreads()); }
        String waiting(Condition c) { return names(getWaitingThreads(c)); }
    }

    /** One thread: holds, reentrancy, downgrading, failed upgrade, errors and their messages. */
    public static String rwBasic(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        RW rw = new RW(n % 2 == 0);
        ReentrantReadWriteLock.ReadLock r = rw.readLock();
        ReentrantReadWriteLock.WriteLock w = rw.writeLock();
        b.append(rw.isFair()).append(' ');
        int k = 1 + small(n) % 3;
        for (int i = 0; i < k; i++) r.lock();
        b.append(rw.getReadLockCount()).append(rw.getReadHoldCount()).append(rw.isWriteLocked()).append(w.tryLock()).append(r.tryLock()).append(' ');
        b.append(w.tryLock(0, TimeUnit.MILLISECONDS)).append(rw.getReadHoldCount()).append(' ');
        for (int i = 0; i <= k; i++) r.unlock();
        try { r.unlock(); } catch (IllegalMonitorStateException e) { b.append(ex(e)).append(' '); }
        w.lock(); w.lock();
        b.append(rw.getWriteHoldCount()).append(rw.isWriteLockedByCurrentThread()).append(w.isHeldByCurrentThread()).append(w.getHoldCount()).append(rw.owner()).append(' ');
        r.lock();   // downgrade
        b.append(rw.getReadLockCount()).append(rw.getReadHoldCount()).append(' ');
        w.unlock(); w.unlock();
        b.append(rw.isWriteLocked()).append(rw.getReadHoldCount()).append(rw.getWriteHoldCount()).append(rw.owner()).append(' ');
        r.unlock();
        try { w.unlock(); } catch (IllegalMonitorStateException e) { b.append(ex(e)).append(' '); }
        try { r.newCondition(); } catch (UnsupportedOperationException e) { b.append(ex(e)).append(' '); }
        Condition c = w.newCondition();
        try { c.await(); } catch (IllegalMonitorStateException e) { b.append("a:").append(ex(e)).append(' '); }
        try { c.signal(); } catch (IllegalMonitorStateException e) { b.append("s:").append(ex(e)).append(' '); }
        try { c.signalAll(); } catch (IllegalMonitorStateException e) { b.append("sa:").append(ex(e)).append(' '); }
        try { c.awaitUninterruptibly(); } catch (IllegalMonitorStateException e) { b.append("au:").append(ex(e)).append(' '); }
        try { rw.hasWaiters(c); } catch (IllegalMonitorStateException e) { b.append("hw:").append(ex(e)).append(' '); }
        try { rw.hasWaiters(null); } catch (NullPointerException e) { b.append("npe "); }
        try { rw.getWaitQueueLength(new ReentrantLock().newCondition()); } catch (IllegalArgumentException e) { b.append(ex(e)).append(' '); }
        try { rw.hasWaiters(new ReentrantReadWriteLock().writeLock().newCondition()); } catch (IllegalArgumentException e) { b.append(ex(e)).append(' '); }
        Condition foreign = new Condition() {
            public void await() { }
            public void awaitUninterruptibly() { }
            public long awaitNanos(long x) { return 0; }
            public boolean await(long t, TimeUnit u) { return false; }
            public boolean awaitUntil(Date d) { return false; }
            public void signal() { }
            public void signalAll() { }
        };
        try { rw.getWaitQueueLength(foreign); } catch (IllegalArgumentException e) { b.append(ex(e)).append(' '); }
        w.lock();
        r.lock();
        b.append(rw.hasWaiters(c)).append(rw.getWaitQueueLength(c)).append(rw.waiting(c)).append(' ');
        b.append(c.awaitNanos(1000000L) <= 0).append(c.await(5, TimeUnit.MILLISECONDS)).append(c.awaitUntil(new Date(System.currentTimeMillis() + 5)))
            .append(c.awaitUntil(new Date(0))).append(c.await(-1, TimeUnit.SECONDS)).append(' ');
        b.append(rw.getWriteHoldCount()).append(rw.getReadHoldCount()).append(rw.getReadLockCount()).append(' ');
        try { c.awaitUntil(null); } catch (NullPointerException e) { b.append(ex(e)).append(' '); }
        Thread.currentThread().interrupt();
        try { c.await(); } catch (InterruptedException e) { b.append("ie1 ").append(rw.getWriteHoldCount()).append(Thread.interrupted()).append(' '); }
        Thread.currentThread().interrupt();
        try { c.awaitNanos(5); } catch (InterruptedException e) { b.append("ie2 "); }
        r.unlock();
        w.unlock();
        Thread.currentThread().interrupt();
        try { r.lockInterruptibly(); } catch (InterruptedException e) { b.append("ie3 ").append(Thread.currentThread().isInterrupted()).append(' '); }
        Thread.currentThread().interrupt();
        r.lock();   // not interruptible, no wait: the interrupt stays
        b.append(rw.getReadHoldCount()).append(Thread.interrupted()).append(' ');
        r.unlock();
        Thread.currentThread().interrupt();
        try { w.tryLock(1, TimeUnit.SECONDS); } catch (InterruptedException e) { b.append("ie4 "); }
        Thread.currentThread().interrupt();
        try { w.lockInterruptibly(); } catch (InterruptedException e) { b.append("ie5 "); }
        Thread.currentThread().interrupt();
        b.append(w.tryLock()).append(Thread.interrupted());
        w.unlock();
        b.append(' ').append(rw.isWriteLocked()).append(rw.getReadLockCount()).append(rw.hasQueuedThreads()).append(rw.getQueueLength());
        return b.toString();
    }

    /** Queued readers and writers are granted in arrival order (readers together), fair or not. */
    public static String rwQueue(int n) throws Exception {
        RW rw = new RW(n % 2 == 0);
        AtomicInteger seq = new AtomicInteger();
        int[] at = new int[4];
        CountDownLatch bothReaders = new CountDownLatch(2);
        rw.writeLock().lock();
        String[] nm = { "R1", "R2", "W3", "R4" };
        Thread[] ts = new Thread[4];
        for (int i = 0; i < 4; i++) {
            int id = i;
            boolean reader = i != 2;
            ts[i] = new Thread(() -> {
                Lock l = reader ? rw.readLock() : rw.writeLock();
                l.lock();
                try {
                    at[id] = seq.getAndIncrement();
                    if (id < 2) {
                        bothReaders.countDown();
                        try { bothReaders.await(); } catch (InterruptedException e) { }
                    }
                } finally {
                    l.unlock();
                }
            }, nm[i]);
            ts[i].start();
            int q = i + 1;
            until(() -> rw.getQueueLength() == q);
        }
        String insp = rw.getQueueLength() + " " + rw.hasQueuedThreads() + rw.hasQueuedThread(ts[1]) + rw.hasQueuedThread(Thread.currentThread())
            + " " + rw.queued() + " " + rw.owner() + rw.getWriteHoldCount();
        String npe;
        try { rw.hasQueuedThread(null); npe = "no"; } catch (NullPointerException e) { npe = "npe"; }
        rw.writeLock().unlock();
        for (Thread t : ts) t.join();
        return insp + " " + npe + " " + Math.min(at[0], at[1]) + Math.max(at[0], at[1]) + at[2] + at[3] + " " + rw.getQueueLength() + rw.getReadLockCount();
    }

    /** A queued writer blocks new readers (tryLock barges); reentrant reads never wait. */
    public static String rwBarging(int n) throws Exception {
        RW rw = new RW(n % 2 == 0);
        StringBuilder b = new StringBuilder();
        rw.readLock().lock();
        Thread wr = new Thread(() -> { rw.writeLock().lock(); rw.writeLock().unlock(); }, "W");
        wr.start();
        until(() -> rw.getQueueLength() == 1);
        String[] res = new String[1];
        Thread x = new Thread(() -> {
            try {
                boolean a = rw.readLock().tryLock();
                if (a) rw.readLock().unlock();
                boolean t0 = rw.readLock().tryLock(0, TimeUnit.MILLISECONDS);
                boolean t1 = rw.readLock().tryLock(50, TimeUnit.MILLISECONDS);
                boolean w0 = rw.writeLock().tryLock();
                res[0] = a + " " + t0 + t1 + w0 + " " + rw.getReadHoldCount();
            } catch (InterruptedException e) { res[0] = "ie"; }
        }, "X");
        x.start();
        x.join();
        rw.readLock().lock();   // reentrant: does not wait behind the writer
        b.append(res[0]).append(' ').append(rw.getReadHoldCount()).append(rw.getReadLockCount()).append(rw.queued()).append(' ');
        rw.readLock().unlock();
        rw.readLock().unlock();
        wr.join();
        b.append(rw.isWriteLocked()).append(rw.getQueueLength());
        return b.toString();
    }

    /** Write-lock Condition: FIFO wait queue, signal moves a waiter to the lock queue. */
    public static String rwCond(int n) throws Exception {
        RW rw = new RW(n % 2 == 0);
        ReentrantReadWriteLock.WriteLock w = rw.writeLock();
        Condition c = w.newCondition();
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        Thread[] ts = new Thread[3];
        for (int i = 0; i < 3; i++) {
            String name = "T" + i;
            ts[i] = new Thread(() -> {
                w.lock();
                try {
                    c.await();
                    log.add(name + rw.getWriteHoldCount());
                } catch (InterruptedException e) {
                    log.add(name + "ie");
                } finally {
                    w.unlock();
                }
            }, name);
            ts[i].start();
            int q = i + 1;
            until(() -> { w.lock(); try { return rw.getWaitQueueLength(c) == q; } finally { w.unlock(); } });
        }
        StringBuilder b = new StringBuilder();
        w.lock();
        b.append(rw.hasWaiters(c)).append(rw.waiting(c)).append(rw.getQueueLength()).append(' ');
        c.signal();
        b.append(rw.getWaitQueueLength(c)).append(rw.getQueueLength()).append(rw.hasQueuedThread(ts[0])).append(rw.waiting(c)).append(' ');
        if (n % 3 == 0) {
            w.unlock();
            until(() -> log.size() == 1);
            w.lock();
        }
        c.signalAll();
        b.append(rw.getWaitQueueLength(c)).append(rw.hasWaiters(c)).append(' ');
        w.unlock();
        for (Thread t : ts) t.join();
        return b + "" + log;
    }

    /** Interrupts and timeouts of Condition waits; awaitUninterruptibly; interrupt after signal. */
    public static String rwCondInterrupt(int n) throws Exception {
        RW rw = new RW(n % 2 == 0);
        ReentrantReadWriteLock.WriteLock w = rw.writeLock();
        Condition c = w.newCondition();
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        int mode = small(n) % 4;
        Thread t = new Thread(() -> {
            w.lock();
            w.lock();
            try {
                if (mode == 0) {
                    try { c.await(); log.add("ret"); } catch (InterruptedException e) { log.add("ie" + w.getHoldCount() + Thread.currentThread().isInterrupted()); }
                } else if (mode == 1) {
                    c.awaitUninterruptibly();
                    log.add("unint" + w.getHoldCount() + Thread.currentThread().isInterrupted());
                } else if (mode == 2) {
                    try { c.await(); log.add("after-signal" + w.getHoldCount() + Thread.currentThread().isInterrupted()); } catch (InterruptedException e) { log.add("ie"); }
                } else {
                    try { log.add("timed" + c.await(100, TimeUnit.MILLISECONDS) + w.getHoldCount()); } catch (InterruptedException e) { log.add("ie"); }
                }
            } finally {
                w.unlock();
                w.unlock();
            }
        }, "T");
        t.start();
        until(() -> { w.lock(); try { return rw.getWaitQueueLength(c) == 1; } finally { w.unlock(); } });
        if (mode == 0) {
            t.interrupt();
        } else if (mode == 1) {
            t.interrupt();
            Thread.sleep(50);
            w.lock();
            log.add("q" + rw.getWaitQueueLength(c));
            c.signal();
            w.unlock();
        } else if (mode == 2) {
            w.lock();
            c.signal();
            t.interrupt();
            w.unlock();
        } else {
            w.lock();   // the timed wait times out but must reacquire
            Thread.sleep(300);
            log.add("q" + rw.getQueueLength() + rw.getWaitQueueLength(c));
            w.unlock();
        }
        t.join();
        return mode + " " + log + " " + rw.isWriteLocked() + rw.getQueueLength();
    }

    /** The JDK's read-hold bookkeeping across a Condition wait of a write holder that also reads. */
    public static String rwDowngradeAwait(int n) throws Exception {
        RW rw = new RW(n % 2 == 0);
        ReentrantReadWriteLock.WriteLock w = rw.writeLock();
        ReentrantReadWriteLock.ReadLock r = rw.readLock();
        Condition c = w.newCondition();
        boolean otherReads = (n & 2) == 0;
        String[] out = new String[1];
        Thread a = new Thread(() -> {
            w.lock();
            r.lock();
            try {
                c.await();
            } catch (InterruptedException e) { }
            StringBuilder b = new StringBuilder();
            b.append(rw.getReadHoldCount()).append(rw.getReadLockCount()).append(rw.getWriteHoldCount()).append(' ');
            try { r.unlock(); b.append("unlocked "); } catch (IllegalMonitorStateException e) { b.append(ex(e)).append(' '); }
            w.unlock();
            b.append(rw.isWriteLocked()).append(rw.getReadLockCount()).append(rw.getReadHoldCount());
            out[0] = b.toString();
        }, "A");
        a.start();
        until(() -> { w.lock(); try { return rw.getWaitQueueLength(c) == 1; } finally { w.unlock(); } });
        String during = rw.isWriteLocked() + " " + rw.getReadLockCount();
        if (otherReads) {
            boolean got = r.tryLock();
            during += got + "" + rw.getReadHoldCount();
            if (got) r.unlock();
        }
        w.lock();
        c.signal();
        w.unlock();
        a.join();
        return during + " " + out[0];
    }

    /** Timed and interruptible acquires that fail or are interrupted; a non-interruptible lock keeps the interrupt. */
    public static String rwTimed(int n) throws Exception {
        RW rw = new RW(n % 2 == 0);
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        int mode = small(n) % 3;
        if (mode == 0) rw.writeLock().lock(); else rw.readLock().lock();
        Thread t = new Thread(() -> {
            try {
                boolean rr = rw.readLock().tryLock(100, TimeUnit.MILLISECONDS);
                if (rr) rw.readLock().unlock();
                log.add("r" + rr);
                log.add("w" + rw.writeLock().tryLock(100, TimeUnit.MILLISECONDS));
                log.add("q" + rw.getQueueLength());
                if (mode == 2) {
                    rw.writeLock().lock();   // waits; interrupted meanwhile
                    log.add("locked" + Thread.currentThread().isInterrupted());
                    rw.writeLock().unlock();
                } else {
                    try { rw.writeLock().lockInterruptibly(); log.add("locked"); rw.writeLock().unlock(); }
                    catch (InterruptedException e) { log.add("ie" + rw.getQueueLength()); }
                }
            } catch (InterruptedException e) {
                log.add("ie?");
            }
        }, "T");
        t.start();
        until(() -> log.size() == 3 && rw.getQueueLength() == 1);
        t.interrupt();
        if (mode == 2) {
            Thread.sleep(50);
            rw.readLock().unlock();
        }
        t.join();
        if (mode == 0) rw.writeLock().unlock(); else if (mode == 1) rw.readLock().unlock();
        return mode + " " + log + " " + rw.isWriteLocked() + rw.getReadLockCount() + rw.getQueueLength();
    }

    /** ReentrantLock's Condition.awaitUntil: deadline, signal, interrupt, null. */
    public static String awaitUntil(int n) throws Exception {
        ReentrantLock l = new ReentrantLock(n % 2 == 0);
        Condition c = l.newCondition();
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        int mode = small(n) % 3;
        l.lock();
        log.add("past" + c.awaitUntil(new Date(System.currentTimeMillis() - 10)));
        try { c.awaitUntil(null); } catch (NullPointerException e) { log.add(ex(e)); }
        l.unlock();
        try { c.awaitUntil(new Date(System.currentTimeMillis() + 10)); } catch (IllegalMonitorStateException e) { log.add("imse"); }
        AtomicBoolean waiting = new AtomicBoolean();
        Thread t = new Thread(() -> {
            l.lock();
            try {
                waiting.set(true);
                boolean r = c.awaitUntil(new Date(System.currentTimeMillis() + (mode == 0 ? 100 : 100000)));
                log.add("r" + r + l.getHoldCount());
            } catch (InterruptedException e) {
                log.add("ie" + l.isHeldByCurrentThread());
            } finally {
                l.unlock();
            }
        }, "T");
        t.start();
        until(() -> waiting.get() && !l.isLocked());
        if (mode == 1) {
            l.lock();
            c.signal();
            l.unlock();
        } else if (mode == 2) {
            t.interrupt();
        }
        t.join();
        return mode + " " + log;
    }

    /** LockSupport: permits, interrupts, timeouts, blockers. */
    public static String lockSupport(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        LockSupport.unpark(Thread.currentThread());
        LockSupport.park();                       // the permit: returns at once
        LockSupport.unpark(null);
        LockSupport.parkNanos(-5);
        LockSupport.parkNanos(0);
        LockSupport.parkUntil(0);
        long t0 = System.currentTimeMillis();
        LockSupport.parkNanos("blk", 20000000L);   // a timeout (it may return early: not observed)
        b.append("timed ");
        Thread.currentThread().interrupt();
        LockSupport.park(this0());
        b.append(Thread.interrupted()).append(' ');
        try { LockSupport.getBlocker(null); } catch (NullPointerException e) { b.append("npe "); }
        Object blocker = new Object();
        int mode = small(n) % 3;
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        AtomicBoolean go = new AtomicBoolean();
        Thread t = new Thread(() -> {
            while (!go.get()) LockSupport.park(blocker);
            log.add("woke" + Thread.currentThread().isInterrupted());
        }, "P");
        t.start();
        until(() -> LockSupport.getBlocker(t) == blocker);
        b.append(LockSupport.getBlocker(Thread.currentThread())).append(' ');
        go.set(true);
        if (mode == 0) LockSupport.unpark(t);
        else if (mode == 1) t.interrupt();
        else { LockSupport.unpark(t); LockSupport.unpark(t); }
        t.join();
        b.append(log).append(' ').append(LockSupport.getBlocker(t));
        // parkUntil with a deadline in the future, ended by unpark
        Thread u = new Thread(() -> {
            LockSupport.parkUntil(blocker, System.currentTimeMillis() + 100000);
            log.add("u");
        }, "U");
        u.start();
        until(() -> LockSupport.getBlocker(u) == blocker);
        LockSupport.unpark(u);
        u.join();
        return b + " " + log;
    }

    static Object this0() { return "self"; }

    /** CyclicBarrier: indexes, the barrier action once per trip, generations. */
    public static String barrier(int n) throws Exception {
        int k = 2 + small(n) % 3;
        AtomicInteger trips = new AtomicInteger();
        CyclicBarrier cb = new CyclicBarrier(k, trips::incrementAndGet);
        List<List<Integer>> idx = new ArrayList<>();
        for (int g = 0; g < 3; g++) idx.add(Collections.synchronizedList(new ArrayList<>()));
        Thread[] ts = new Thread[k - 1];
        for (int i = 0; i < k - 1; i++) {
            ts[i] = new Thread(() -> {
                try {
                    for (int g = 0; g < 3; g++) idx.get(g).add(cb.await());
                } catch (Exception e) { idx.get(0).add(-100); }
            });
            ts[i].start();
        }
        for (int g = 0; g < 3; g++) idx.get(g).add(cb.await(1, TimeUnit.MINUTES));
        for (Thread t : ts) t.join();
        StringBuilder b = new StringBuilder();
        for (List<Integer> l : idx) { List<Integer> s = new ArrayList<>(l); Collections.sort(s); b.append(s); }
        try { new CyclicBarrier(0); } catch (IllegalArgumentException e) { b.append(" iae"); }
        return b + " " + trips.get() + " " + cb.getNumberWaiting() + cb.isBroken() + cb.getParties();
    }

    /** Breaking a barrier: reset, interrupt, timeout, a failing action. */
    public static String barrierBreak(int n) throws Exception {
        int mode = small(n) % 4;
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        CyclicBarrier cb = mode == 3
            ? new CyclicBarrier(2, () -> { throw new IllegalStateException("boom"); })
            : new CyclicBarrier(3);
        Thread a = new Thread(() -> {
            try { log.add("a" + cb.await()); } catch (Exception e) { log.add("a:" + e.getClass().getName()); }
        }, "A");
        a.start();
        until(() -> cb.getNumberWaiting() == 1);
        String m;
        if (mode == 0) {
            cb.reset();
            a.join();
            m = cb.isBroken() + "" + cb.getNumberWaiting();
        } else if (mode == 1) {
            a.interrupt();
            a.join();
            m = "" + cb.isBroken() + cb.getNumberWaiting();
            try { cb.await(); } catch (BrokenBarrierException e) { m += " bbe"; }
            cb.reset();
            m += cb.isBroken();
        } else if (mode == 2) {
            try { cb.await(100, TimeUnit.MILLISECONDS); m = "ret"; } catch (TimeoutException e) { m = "timeout"; }
            a.join();
            m += cb.isBroken();
            try { cb.await(0, TimeUnit.SECONDS); } catch (BrokenBarrierException e) { m += " bbe"; }
        } else {
            try { cb.await(); m = "ret"; } catch (IllegalStateException e) { m = ex(e); }
            a.join();
            m += cb.isBroken();
        }
        Thread.currentThread().interrupt();
        try { new CyclicBarrier(2).await(); } catch (InterruptedException e) { m += " ie" + Thread.currentThread().isInterrupted(); }
        return mode + " " + m + " " + log;
    }

    /** Exchanger: pairs, null items, timeout, interrupt. */
    public static String exchanger(int n) throws Exception {
        Exchanger<String> x = new Exchanger<>();
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        String mine = "m" + small(n);
        Thread t = new Thread(() -> {
            try {
                for (int i = 0; i < 3; i++) log.add("t" + x.exchange(i == 1 ? null : "t" + i));
                log.add("t" + x.exchange("late", 1, TimeUnit.MINUTES));
            } catch (Exception e) { log.add("t:" + ex(e)); }
        }, "T");
        t.start();
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < 3; i++) b.append(x.exchange(i == 2 ? null : mine + i)).append(',');
        b.append(x.exchange("m3", 1, TimeUnit.MINUTES)).append(' ');
        t.join();
        try { x.exchange("none", 50, TimeUnit.MILLISECONDS); } catch (TimeoutException e) { b.append("timeout "); }
        Thread.currentThread().interrupt();
        try { x.exchange("i"); } catch (InterruptedException e) { b.append("ie ").append(Thread.currentThread().isInterrupted()).append(' '); }
        Thread u = new Thread(() -> {
            try { x.exchange("u"); log.add("u?"); } catch (InterruptedException e) { log.add("u:ie"); }
        }, "U");
        u.start();
        Thread.sleep(100);
        u.interrupt();
        u.join();
        try { x.exchange("none", 0, TimeUnit.MILLISECONDS); } catch (TimeoutException e) { b.append("timeout0"); }
        return b + " " + log;
    }

    /** Phaser: phases, arrivals, deregistration, termination, onAdvance, getters. */
    public static String phaser(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        int k = 1 + small(n) % 3;
        Phaser p = new Phaser(1);
        List<List<Integer>> got = Collections.synchronizedList(new ArrayList<>());
        Thread[] ts = new Thread[k];
        for (int i = 0; i < k; i++) {
            b.append(p.register());
            ts[i] = new Thread(() -> {
                List<Integer> mine = new ArrayList<>();
                for (int g = 0; g < 3; g++) mine.add(p.arriveAndAwaitAdvance());
                mine.add(p.arriveAndDeregister());
                got.add(mine);
            });
        }
        b.append(' ').append(p.getRegisteredParties()).append(p.getArrivedParties()).append(p.getUnarrivedParties()).append(p.getPhase()).append(' ');
        for (Thread t : ts) t.start();
        List<Integer> me = new ArrayList<>();
        for (int g = 0; g < 3; g++) me.add(p.arriveAndAwaitAdvance());
        b.append(me).append(' ');
        for (Thread t : ts) t.join();
        b.append(got.size()).append(got.get(0)).append(' ').append(p.getRegisteredParties()).append(p.isTerminated()).append(' ');
        b.append(p.arriveAndDeregister()).append(' ').append(p.isTerminated()).append(p.getPhase()).append(p.getRegisteredParties())
            .append(p.arrive()).append(p.register()).append(p.awaitAdvance(3)).append(p.arriveAndAwaitAdvance()).append(' ');
        // onAdvance: terminate after phase 2
        Phaser q = new Phaser(2) {
            protected boolean onAdvance(int phase, int parties) { b.append("<adv").append(phase).append(parties).append('>'); return phase >= 2; }
        };
        for (int i = 0; i < 4; i++) {
            b.append(q.arrive()).append(',').append(q.getArrivedParties()).append(q.getUnarrivedParties()).append(',');
            b.append(q.arrive()).append(',').append(q.getPhase()).append(';');
        }
        b.append(q.isTerminated()).append(q.awaitAdvance(0)).append(q.awaitAdvance(-3)).append(q.bulkRegister(0)).append(' ');
        Phaser e = new Phaser();
        b.append(e.getPhase()).append(e.getRegisteredParties()).append(e.bulkRegister(3)).append(e.getUnarrivedParties()).append(e.arrive()).append(e.arriveAndDeregister())
            .append(e.getRegisteredParties()).append(e.getArrivedParties()).append(e.arrive()).append(e.getPhase()).append(e.getArrivedParties()).append(e.getRoot() == e).append(e.getParent());
        try { new Phaser(65536); } catch (IllegalArgumentException x) { b.append(' ').append(ex(x)); }
        try { e.bulkRegister(-1); } catch (IllegalArgumentException x) { b.append(' ').append(ex(x)); }
        return b.toString();
    }

    /** Phaser waits: awaitAdvance, interruptible and timed waits, forceTermination. */
    public static String phaserWait(int n) throws Exception {
        int mode = small(n) % 4;
        Phaser p = new Phaser(2);
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        AtomicBoolean waiting = new AtomicBoolean();
        Thread t = new Thread(() -> {
            try {
                if (mode == 0) { waiting.set(true); log.add("aaa" + p.arriveAndAwaitAdvance() + Thread.currentThread().isInterrupted()); }
                else if (mode == 1) { waiting.set(true); log.add("int" + p.awaitAdvanceInterruptibly(0)); }
                else if (mode == 2) { waiting.set(true); log.add("timed" + p.awaitAdvanceInterruptibly(0, 100, TimeUnit.MILLISECONDS)); }
                else { p.arrive(); waiting.set(true); log.add("aw" + p.awaitAdvance(0)); }
            } catch (InterruptedException e) {
                log.add("ie" + Thread.currentThread().isInterrupted());
            } catch (TimeoutException e) {
                log.add("timeout" + p.getPhase());
            }
        }, "T");
        t.start();
        until(() -> waiting.get() && (mode != 0 || p.getArrivedParties() == 1));
        Thread.sleep(50);
        if (mode == 0) { t.interrupt(); Thread.sleep(50); int r = p.arrive(); t.join(); log.add("m" + r); }
        else if (mode == 1) { t.interrupt(); }
        else if (mode == 3) { p.forceTermination(); }
        t.join();
        return mode + " " + log + " " + p.getPhase() + p.isTerminated() + p.getArrivedParties();
    }

    /** Tiered phasers: a sub-phaser is one party of its parent while it has parties. */
    public static String phaserTree(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        Phaser root = new Phaser();
        Phaser c1 = new Phaser(root, 2);
        Phaser c2 = new Phaser(root);
        b.append(root.getRegisteredParties()).append(c1.getRegisteredParties()).append(c2.getRegisteredParties()).append(c2.getParent() == root).append(c1.getRoot() == root).append(' ');
        b.append(c2.register()).append(root.getRegisteredParties()).append(' ');
        b.append(c1.arrive()).append(c1.getArrivedParties()).append(root.getArrivedParties()).append(c1.arrive()).append(c1.getArrivedParties()).append(root.getArrivedParties()).append(root.getPhase()).append(' ');
        b.append(c2.arrive()).append(root.getPhase()).append(c1.getPhase()).append(c1.getArrivedParties()).append(c1.getUnarrivedParties()).append(' ');
        // deregistering all of a child's parties deregisters it from the parent
        b.append(c2.arriveAndDeregister()).append(c2.getRegisteredParties()).append(root.getRegisteredParties()).append(root.getPhase()).append(' ');
        b.append(c2.register()).append(root.getRegisteredParties()).append(' ');
        List<String> res = Collections.synchronizedList(new ArrayList<>());
        Thread t = new Thread(() -> res.add("t" + c1.arriveAndAwaitAdvance() + c1.arriveAndAwaitAdvance()));
        Thread u = new Thread(() -> res.add("u" + c2.arriveAndAwaitAdvance() + c2.arriveAndAwaitAdvance()));
        t.start();
        u.start();
        String m = "m" + c1.arriveAndAwaitAdvance() + c1.arriveAndAwaitAdvance();
        t.join();
        u.join();
        List<String> sorted = new ArrayList<>(res);
        Collections.sort(sorted);
        b.append(m).append(sorted).append(root.getPhase()).append(c1.getArrivedParties()).append(c2.getUnarrivedParties()).append(' ');
        int k = small(n) % 3;
        for (int i = 0; i < k; i++) { c1.arrive(); c1.arrive(); c2.arrive(); }
        b.append(root.getPhase()).append(c2.getPhase()).append(' ');
        c1.forceTermination();
        b.append(root.isTerminated()).append(c2.isTerminated()).append(c2.getPhase() < 0).append(c2.arrive() < 0).append(c1.register() < 0);
        return b.toString();
    }

    static ThreadFactory named(String prefix) {
        AtomicInteger k = new AtomicInteger();
        return r -> new Thread(r, prefix + k.incrementAndGet());
    }

    /** invokeAny: the only task that succeeds, all fail, errors, timeout and cancellation. */
    public static String invokeAny(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        int mode = small(n) % 2;
        ExecutorService es = mode == 0 ? Executors.newFixedThreadPool(2, named("p")) : new ThreadPoolExecutor(2, 2, 0, TimeUnit.SECONDS, new LinkedBlockingQueue<>(), named("q"));
        List<Callable<Integer>> cs = new ArrayList<>();
        for (int i = 0; i < 3; i++) {
            int v = i;
            cs.add(() -> { if (v != 1) throw new IllegalStateException("bad"); return 42; });
        }
        b.append(es.invokeAny(cs)).append(' ');
        b.append(es.invokeAny(cs, 1, TimeUnit.MINUTES)).append(' ');
        List<Callable<Integer>> fail = new ArrayList<>();
        for (int i = 0; i < 2; i++) fail.add(() -> { throw new ArithmeticException("x"); });
        try { es.invokeAny(fail); } catch (ExecutionException e) { b.append(ex(e)).append(ex(e.getCause())).append(' '); }
        try { es.invokeAny(new ArrayList<Callable<Integer>>()); } catch (IllegalArgumentException e) { b.append("iae "); }
        try { es.invokeAny(null); } catch (NullPointerException e) { b.append("npe "); }
        try { es.invokeAny(Collections.singletonList(null)); } catch (NullPointerException e) { b.append("npe2 "); }
        AtomicInteger interrupted = new AtomicInteger();
        CountDownLatch done = new CountDownLatch(2);
        List<Callable<Integer>> slow = new ArrayList<>();
        for (int i = 0; i < 2; i++) slow.add(() -> {
            try { Thread.sleep(100000); } catch (InterruptedException e) { interrupted.incrementAndGet(); }
            finally { done.countDown(); }
            return 1;
        });
        try { es.invokeAny(slow, 100, TimeUnit.MILLISECONDS); } catch (TimeoutException e) { b.append("timeout "); }
        done.await();
        b.append(interrupted.get()).append(' ');
        ExecutorService single = Executors.newSingleThreadExecutor(named("s"));
        List<Callable<String>> seq = new ArrayList<>();
        seq.add(() -> { Thread.sleep(50); return "first"; });
        seq.add(() -> "second");
        b.append(single.invokeAny(seq)).append(' ');
        single.shutdown();
        es.shutdown();
        b.append(es.awaitTermination(1, TimeUnit.MINUTES)).append(single.awaitTermination(1, TimeUnit.MINUTES));
        try { es.invokeAny(cs); } catch (RejectedExecutionException e) { b.append(" rejected"); }
        return b.toString();
    }

    /** Timed invokeAll: the tasks not done by the deadline are cancelled; zero timeout runs nothing. */
    public static String invokeAllTimed(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        ExecutorService es = Executors.newFixedThreadPool(2, named("p"));
        AtomicInteger ran = new AtomicInteger();
        List<Callable<Integer>> cs = new ArrayList<>();
        cs.add(() -> { ran.incrementAndGet(); return 1; });
        cs.add(() -> { ran.incrementAndGet(); Thread.sleep(100000); return 2; });
        cs.add(() -> { ran.incrementAndGet(); return 3; });
        if (n % 2 == 0) cs.add(() -> { throw new IllegalStateException("t"); });
        List<Future<Integer>> fs = es.invokeAll(cs, 300, TimeUnit.MILLISECONDS);
        for (Future<Integer> f : fs) {
            b.append(f.isDone()).append(f.isCancelled());
            try { b.append(f.get()); } catch (CancellationException e) { b.append("C"); } catch (ExecutionException e) { b.append("E").append(ex(e.getCause())); }
            b.append(',');
        }
        b.append(' ').append(ran.get()).append(' ');
        AtomicInteger ran0 = new AtomicInteger();
        List<Callable<Integer>> cs0 = new ArrayList<>();
        for (int i = 0; i < 2; i++) cs0.add(() -> { ran0.incrementAndGet(); return 0; });
        for (Future<Integer> f : es.invokeAll(cs0, 0, TimeUnit.SECONDS)) b.append(f.isCancelled());
        List<Future<Integer>> all = es.invokeAll(cs0.subList(0, 1), 1, TimeUnit.MINUTES);
        b.append(' ').append(all.get(0).get()).append(ran0.get());
        try { es.invokeAll(null, 1, TimeUnit.SECONDS); } catch (NullPointerException e) { b.append(" npe"); }
        es.shutdownNow();
        b.append(' ').append(es.awaitTermination(1, TimeUnit.MINUTES));
        return b.toString();
    }

    /** LinkedBlockingDeque, one thread: a random sequence of operations (capacity 1..5 or unbounded). */
    public static String lbdOps(int seed) throws Exception {
        int[] s = { seed };
        java.util.function.IntUnaryOperator r = m -> { s[0] = s[0] * 1103515245 + 12345; return ((s[0] >>> 8) & 0x7fffff) % m; };
        int cap = r.applyAsInt(6);
        LinkedBlockingDeque<Integer> d = cap == 0 ? new LinkedBlockingDeque<>() : new LinkedBlockingDeque<>(cap);
        StringBuilder b = new StringBuilder();
        int steps = 20 + r.applyAsInt(40);
        for (int i = 0; i < steps; i++) {
            Integer v = r.applyAsInt(8);
            try {
                switch (r.applyAsInt(30)) {
                    case 0: d.addFirst(v); b.append("aF"); break;
                    case 1: d.addLast(v); b.append("aL"); break;
                    case 2: b.append(d.offerFirst(v)); break;
                    case 3: b.append(d.offerLast(v)); break;
                    case 4: b.append(d.pollFirst()); break;
                    case 5: b.append(d.pollLast()); break;
                    case 6: b.append(d.removeFirst()); break;
                    case 7: b.append(d.removeLast()); break;
                    case 8: b.append(d.getFirst()).append(d.getLast()); break;
                    case 9: b.append(d.peekFirst()).append(d.peekLast()).append(d.peek()); break;
                    case 10: b.append(d.removeFirstOccurrence(v)).append(d.removeLastOccurrence(v + 1)); break;
                    case 11: d.push(v); b.append(d.pop()); break;
                    case 12: b.append(d.add(v)).append(d.offer(v)); break;
                    case 13: b.append(d).append(d.size()).append(d.remainingCapacity()); break;
                    case 14: b.append(d.contains(v)).append(d.remove(v)); break;
                    case 15: { List<Integer> l = new ArrayList<>(); b.append(d.drainTo(l, 1 + r.applyAsInt(3))).append(l); break; }
                    case 16: { Iterator<Integer> it = d.iterator(); while (it.hasNext()) { int x = it.next(); b.append(x); if (x % 2 == 0) it.remove(); } break; }
                    case 17: { Iterator<Integer> it = d.descendingIterator(); while (it.hasNext()) { int x = it.next(); b.append(x); if (x % 3 == 0) it.remove(); } break; }
                    case 18: b.append(Arrays.toString(d.toArray())).append(Arrays.toString(d.toArray(new Integer[1]))); break;
                    case 19: b.append(d.addAll(Arrays.asList(v, v + 1))); break;
                    case 20: b.append(d.removeIf(x -> x > v)).append(d.retainAll(Arrays.asList(1, 2, 3, 4, 5, 6))); break;
                    case 21: d.forEach(x -> b.append('f').append(x)); break;
                    case 22: b.append(d.offer(v, 0, TimeUnit.SECONDS)).append(d.poll(0, TimeUnit.SECONDS)); break;
                    case 23: b.append(d.offerFirst(v, 1, TimeUnit.MILLISECONDS)).append(d.pollLast(1, TimeUnit.MILLISECONDS)); break;
                    case 24: { Iterator<Integer> it = d.iterator(); if (it.hasNext()) { b.append(it.next()); d.pollFirst(); d.addLast(v); while (it.hasNext()) b.append('i').append(it.next()); } break; }
                    case 25: { Iterator<Integer> it = d.iterator(); b.append(it.hasNext()); d.clear(); while (it.hasNext()) b.append('c').append(it.next()); break; }
                    case 26: b.append(d.element()).append(d.remove()); break;
                    case 27: if (d.remainingCapacity() >= 2) { d.put(v); d.putFirst(v + 1); b.append(d.takeLast()).append(d.take()); } else b.append("full"); break;
                    case 28: b.append(d.removeAll(Arrays.asList(v))).append(d.containsAll(Arrays.asList(v, 1))); break;
                    default: { Iterator<Integer> it = d.iterator(); it.remove(); break; }
                }
            } catch (RuntimeException e) {
                b.append('!').append(e.getClass().getName()).append(':').append(e.getMessage());
            }
            b.append(';');
        }
        try { d.offer(null); } catch (NullPointerException e) { b.append("npe"); }
        try { new LinkedBlockingDeque<Integer>(0); } catch (IllegalArgumentException e) { b.append("iae"); }
        try { d.drainTo(d); } catch (IllegalArgumentException e) { b.append("iae2"); }
        try { d.addAll(d); } catch (IllegalArgumentException e) { b.append("iae3"); }
        try { d.addAll(Arrays.asList(1, null)); } catch (NullPointerException e) { b.append("npe2"); }
        return b + " " + d + d.size();
    }

    /** LinkedBlockingDeque: blocked takers and putters are served in the order they started to wait. */
    public static String lbdBlocking(int n) throws Exception {
        int mode = small(n) % 3;
        LinkedBlockingDeque<String> d = new LinkedBlockingDeque<>(1);
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        List<String> takes = new ArrayList<>();
        Thread[] ts = new Thread[2];
        if (mode == 0) {
            for (int i = 0; i < 2; i++) {
                String name = "T" + i;
                ts[i] = new Thread(() -> { try { log.add(name + "=" + (name.equals("T0") ? d.takeFirst() : d.take())); } catch (InterruptedException e) { log.add(name + "ie"); } }, name);
                ts[i].start();
                Thread.sleep(100);
            }
            d.put("a");
            d.put("b");
        } else if (mode == 1) {
            d.put("x");
            for (int i = 0; i < 2; i++) {
                String name = "P" + i;
                ts[i] = new Thread(() -> { try { if (name.equals("P0")) d.putLast(name); else d.putFirst(name); log.add(name); } catch (InterruptedException e) { log.add(name + "ie"); } }, name);
                ts[i].start();
                Thread.sleep(100);
            }
            takes.add(d.take());
            takes.add(d.take());
            takes.add(d.take());
        } else {
            ts[0] = new Thread(() -> { try { log.add("t" + d.takeLast()); } catch (InterruptedException e) { log.add("t-ie" + Thread.currentThread().isInterrupted()); } }, "T0");
            ts[0].start();
            ts[1] = new Thread(() -> {
                try { log.add("p" + d.pollFirst(100, TimeUnit.MILLISECONDS)); } catch (InterruptedException e) { log.add("p-ie"); }
                Thread.currentThread().interrupt();
                try { log.add("o" + d.offerLast("z", 1, TimeUnit.SECONDS)); } catch (InterruptedException e) { log.add("o-ie" + d.size()); }
                Thread.currentThread().interrupt();
                try { d.put("w"); log.add("put" + Thread.interrupted() + d.size()); } catch (InterruptedException e) { log.add("put-ie"); }
            }, "T1");
            Thread.sleep(100);
            ts[0].interrupt();
            ts[0].join();
            ts[1].start();
        }
        for (Thread t : ts) t.join();
        List<String> sorted = new ArrayList<>(log);
        if (mode != 2) Collections.sort(sorted);
        return mode + " " + sorted + takes + " " + d;
    }

    interface Act { Object run() throws Exception; }

    static void tr(StringBuilder b, Act a) {
        try { b.append(a.run()); } catch (Exception e) { b.append(ex(e)); }
        b.append(';');
    }

    /** Null arguments: the JDK's explicit and implicit (helpful message) NullPointerExceptions. */
    public static String nullArgs(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        LinkedBlockingDeque<Integer> d = new LinkedBlockingDeque<>();
        d.add(small(n));
        tr(b, () -> new CyclicBarrier(1).await(1, null));
        tr(b, () -> new Exchanger<Object>().exchange(1, 1, null));
        tr(b, () -> d.offerFirst(1, 1, null));
        tr(b, () -> d.offer(1, 1, null));
        tr(b, () -> d.pollLast(1, null));
        tr(b, () -> d.poll(1, null));
        tr(b, () -> d.offer(null, 1, null));
        tr(b, () -> d.toArray((Integer[]) null));
        tr(b, () -> d.addAll(null));
        tr(b, () -> new LinkedBlockingDeque<Integer>(null));
        tr(b, () -> d.drainTo(null));
        tr(b, () -> { d.forEach(null); return 0; });
        tr(b, () -> d.removeIf(null));
        tr(b, () -> d.retainAll(null));
        tr(b, () -> { d.iterator().forEachRemaining(null); return 0; });
        tr(b, () -> new Phaser(1).awaitAdvanceInterruptibly(0, 1, null));
        tr(b, () -> new ReentrantReadWriteLock().readLock().tryLock(1, null));
        tr(b, () -> new ReentrantReadWriteLock().writeLock().tryLock(1, null));
        ReentrantReadWriteLock rw = new ReentrantReadWriteLock(n % 2 == 0);
        rw.writeLock().lock();
        Condition c = rw.writeLock().newCondition();
        tr(b, () -> c.await(1, null));
        tr(b, () -> c.awaitUntil(null));
        rw.writeLock().unlock();
        tr(b, () -> c.awaitUntil(null));
        ReentrantLock rl = new ReentrantLock();
        tr(b, () -> rl.newCondition().awaitUntil(null));
        ExecutorService es = Executors.newFixedThreadPool(1, named("e"));
        tr(b, () -> es.invokeAll(new ArrayList<Callable<Integer>>(), 1, null));
        tr(b, () -> es.invokeAll(null, 1, null));
        tr(b, () -> es.invokeAny(Collections.singletonList(() -> 1), 1, null));
        es.shutdown();
        tr(b, () -> new ExecutorCompletionService<Object>(null));
        tr(b, () -> LockSupport.getBlocker(null));
        tr(b, () -> new Date(5).before(null));
        tr(b, () -> new Date(5).compareTo(null));
        tr(b, () -> new Date(5).after(new Date(3)) + "" + new Date(7).equals(new Date(7)) + new Date(7).hashCode() + new Date(-1L << 33).hashCode() + new Date(4).compareTo(new Date(9)) + ((Date) new Date(8).clone()).getTime());
        return b + " " + es.awaitTermination(1, TimeUnit.MINUTES);
    }
}

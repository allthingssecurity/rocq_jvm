// ThreadPoolExecutor, its rejection policies and hooks, ScheduledThreadPoolExecutor as a
// ThreadPoolExecutor, blocking queues, fair ReentrantLock and uncaught-exception handlers under
// the thread layer. Results do not depend on the schedule.
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;

public class PoolTests {
    static int small(int n) { return Math.floorMod(n, 10); }

    /** Bounded queue: what runs, what is rejected, with each rejection policy. */
    public static String rejection(int n) throws Exception {
        int policy = small(n) % 4;
        RejectedExecutionHandler h = policy == 0 ? new ThreadPoolExecutor.AbortPolicy()
            : policy == 1 ? new ThreadPoolExecutor.CallerRunsPolicy()
            : policy == 2 ? new ThreadPoolExecutor.DiscardPolicy() : new ThreadPoolExecutor.DiscardOldestPolicy();
        CountDownLatch gate = new CountDownLatch(1);
        ThreadPoolExecutor ex = new ThreadPoolExecutor(1, 2, 1, TimeUnit.SECONDS, new ArrayBlockingQueue<>(2), h);
        List<Integer> ran = Collections.synchronizedList(new ArrayList<>());
        AtomicInteger callerRan = new AtomicInteger();
        Thread me = Thread.currentThread();
        int rejected = 0;
        for (int i = 0; i < 6; i++) {
            int id = i;
            try {
                ex.execute(() -> {
                    if (Thread.currentThread() == me) { callerRan.incrementAndGet(); return; }
                    try { gate.await(); } catch (InterruptedException e) { }
                    ran.add(id);
                });
            } catch (RejectedExecutionException e) {
                rejected++;
            }
        }
        int pool = ex.getPoolSize(), queued = ex.getQueue().size();
        gate.countDown();
        ex.shutdown();
        boolean term = ex.awaitTermination(5, TimeUnit.SECONDS);
        List<Integer> sorted = new ArrayList<>(ran);
        Collections.sort(sorted);
        return policy + " " + rejected + " " + callerRan.get() + " " + pool + " " + queued + " " + sorted + " " + term
            + " " + ex.getCompletedTaskCount() + " " + ex.getLargestPoolSize() + " " + ex.isTerminated();
    }

    /** Hooks: beforeExecute/afterExecute (with the task's exception) and terminated. */
    static final class Hooked extends ThreadPoolExecutor {
        final AtomicInteger before = new AtomicInteger(), after = new AtomicInteger(), failed = new AtomicInteger();
        volatile boolean terminatedCalled;
        Hooked() { super(2, 2, 0, TimeUnit.MILLISECONDS, new LinkedBlockingQueue<>()); }
        protected void beforeExecute(Thread t, Runnable r) { before.incrementAndGet(); }
        protected void afterExecute(Runnable r, Throwable t) { after.incrementAndGet(); if (t != null) failed.incrementAndGet(); }
        protected void terminated() { terminatedCalled = true; }
    }

    public static String hooks(int n) throws Exception {
        int k = 2 + small(n);
        Hooked ex = new Hooked();
        AtomicInteger sum = new AtomicInteger();
        List<Future<Integer>> fs = new ArrayList<>();
        for (int i = 0; i < k; i++) {
            int v = i;
            if (i % 3 == 2) ex.execute(() -> { throw new IllegalStateException("t" + v); });   // kills its worker
            else fs.add(ex.submit(() -> { sum.addAndGet(v); return v * v; }));
        }
        int total = 0;
        for (Future<Integer> f : fs) total += f.get();
        ex.shutdown();
        ex.awaitTermination(5, TimeUnit.SECONDS);
        return sum.get() + " " + total + " " + ex.before.get() + " " + ex.after.get() + " " + ex.failed.get() + " "
            + ex.terminatedCalled + " " + ex.getCompletedTaskCount() + " " + ex.getPoolSize();
    }

    /** Cached pool over a SynchronousQueue; keep-alive shrinks it; invokeAll. */
    public static String cached(int n) throws Exception {
        int k = 1 + small(n) % 4;
        ThreadPoolExecutor ex = (ThreadPoolExecutor) Executors.newCachedThreadPool();
        CountDownLatch started = new CountDownLatch(k), release = new CountDownLatch(1);
        for (int i = 0; i < k; i++) ex.execute(() -> { started.countDown(); try { release.await(); } catch (InterruptedException e) { } });
        started.await();
        int busy = ex.getPoolSize();
        release.countDown();
        ex.setKeepAliveTime(100, TimeUnit.MILLISECONDS);
        Thread.sleep(400);
        int idle = ex.getPoolSize();
        List<Callable<Integer>> cs = new ArrayList<>();
        for (int i = 0; i < 3; i++) { int v = i; cs.add(() -> v + 10); }
        int s = 0;
        for (Future<Integer> f : ex.invokeAll(cs)) s += f.get();
        ex.shutdownNow();
        return busy + " " + idle + " " + s + " " + ex.awaitTermination(1, TimeUnit.SECONDS);
    }

    /** Fixed pool: core threads, shutdownNow returns the queued tasks, interrupts the running ones. */
    public static String fixedShutdownNow(int n) throws Exception {
        int k = 3 + small(n);
        ThreadPoolExecutor ex = (ThreadPoolExecutor) Executors.newFixedThreadPool(2);
        AtomicInteger interrupted = new AtomicInteger();
        CountDownLatch running = new CountDownLatch(2);
        for (int i = 0; i < k; i++) {
            ex.execute(() -> {
                running.countDown();
                try { Thread.sleep(10000); } catch (InterruptedException e) { interrupted.incrementAndGet(); }
            });
        }
        running.await();
        List<Runnable> rest = ex.shutdownNow();
        boolean t = ex.awaitTermination(1, TimeUnit.SECONDS);
        String r;
        try { ex.execute(() -> { }); r = "accepted"; } catch (RejectedExecutionException e) { r = "rejected"; }
        return rest.size() + " " + interrupted.get() + " " + t + " " + r + " " + ex.isShutdown() + ex.isTerminating() + ex.isTerminated()
            + " " + ex.getCorePoolSize() + " " + ex.getMaximumPoolSize();
    }

    /** Configuration errors, prestart, setCorePoolSize, allowCoreThreadTimeOut. */
    public static String config(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        try { new ThreadPoolExecutor(2, 1, 0, TimeUnit.SECONDS, new LinkedBlockingQueue<>()); } catch (IllegalArgumentException e) { b.append("iae "); }
        try { new ThreadPoolExecutor(1, 1, 0, TimeUnit.SECONDS, null); } catch (NullPointerException e) { b.append("npe "); }
        ThreadPoolExecutor ex = new ThreadPoolExecutor(1 + small(n) % 3, 4, 50, TimeUnit.MILLISECONDS, new LinkedBlockingQueue<>());
        b.append(ex.prestartAllCoreThreads()).append(' ').append(ex.getPoolSize()).append(' ');
        try { ex.allowCoreThreadTimeOut(true); } catch (IllegalArgumentException e) { b.append("x"); }
        Thread.sleep(300);
        b.append(ex.getPoolSize()).append(' ').append(ex.allowsCoreThreadTimeOut()).append(' ');
        try { ex.setCorePoolSize(5); } catch (IllegalArgumentException e) { b.append("iae2 "); }
        ex.setMaximumPoolSize(6);
        ex.setCorePoolSize(5);
        b.append(ex.getCorePoolSize()).append(ex.getMaximumPoolSize()).append(' ').append(ex.prestartCoreThread());
        ex.shutdown();
        b.append(' ').append(ex.awaitTermination(1, TimeUnit.SECONDS)).append(' ').append(ex.getKeepAliveTime(TimeUnit.MILLISECONDS));
        return b.toString();
    }

    /** The scheduled executor is a ThreadPoolExecutor; queue contents and removal on cancel. */
    public static String scheduledAsPool(int n) throws Exception {
        ScheduledThreadPoolExecutor ex = new ScheduledThreadPoolExecutor(1);
        ex.setRemoveOnCancelPolicy((n & 1) == 0);
        ScheduledFuture<?> a = ex.schedule(() -> { }, 10, TimeUnit.SECONDS);
        ScheduledFuture<?> b = ex.schedule(() -> { }, 20, TimeUnit.SECONDS);
        int q0 = ex.getQueue().size();
        a.cancel(false);
        int q1 = ex.getQueue().size();
        ex.purge();
        int q2 = ex.getQueue().size();
        boolean isTpe = ex instanceof ThreadPoolExecutor;
        ex.setExecuteExistingDelayedTasksAfterShutdownPolicy(false);
        ex.shutdown();
        return isTpe + " " + q0 + " " + q1 + " " + q2 + " " + ex.awaitTermination(1, TimeUnit.SECONDS) + " " + b.isCancelled()
            + " " + ex.getRemoveOnCancelPolicy() + " " + ex.getPoolSize();
    }

    /** LinkedBlockingQueue / ArrayBlockingQueue / SynchronousQueue between two threads. */
    public static String queues(int n) throws Exception {
        int k = 3 + small(n);
        BlockingQueue<Integer> q = (n & 1) == 0 ? new LinkedBlockingQueue<>(2) : new ArrayBlockingQueue<>(2);
        SynchronousQueue<Integer> sq = new SynchronousQueue<>((n & 2) == 0);
        AtomicInteger got = new AtomicInteger(), gotSq = new AtomicInteger();
        Thread c = new Thread(() -> {
            try {
                for (int i = 0; i < k; i++) got.addAndGet(q.take());
                for (int i = 0; i < k; i++) gotSq.addAndGet(sq.take());
            } catch (InterruptedException e) { }
        });
        c.start();
        for (int i = 1; i <= k; i++) q.put(i);
        for (int i = 1; i <= k; i++) sq.put(i * 10);
        c.join();
        StringBuilder b = new StringBuilder();
        b.append(got.get()).append(' ').append(gotSq.get()).append(' ');
        b.append(q.offer(1)).append(q.offer(2)).append(q.offer(3)).append(' ').append(q.remainingCapacity()).append(' ').append(q);
        b.append(' ').append(q.poll(50, TimeUnit.MILLISECONDS)).append(q.poll()).append(q.poll()).append(' ');
        b.append(sq.offer(5)).append(sq.poll()).append(sq.size()).append(sq.isEmpty()).append(sq.poll(30, TimeUnit.MILLISECONDS));
        try { q.add(null); } catch (NullPointerException e) { b.append(" npe"); }
        q.add(7); q.add(8);
        try { q.add(9); } catch (IllegalStateException e) { b.append(" ").append(e.getMessage()); }
        List<Integer> drained = new ArrayList<>();
        b.append(' ').append(q.drainTo(drained)).append(drained);
        return b.toString();
    }

    /** Fair lock: arrival order is kept; tryLock barges; queue inspection. */
    public static String fairLock(int n) throws Exception {
        ReentrantLock l = new ReentrantLock(true);
        List<String> order = Collections.synchronizedList(new ArrayList<>());
        l.lock();
        Thread[] ts = new Thread[3];
        for (int i = 0; i < 3; i++) {
            String name = "t" + i;
            ts[i] = new Thread(() -> { l.lock(); try { order.add(name); } finally { l.unlock(); } });
            ts[i].start();
            Thread.sleep(50);   // the threads queue in this order
        }
        int ql = l.getQueueLength();
        boolean hq = l.hasQueuedThreads(), h1 = l.hasQueuedThread(ts[1]);
        boolean barge = l.tryLock();   // reentrant: held already
        l.unlock();
        l.unlock();
        for (Thread t : ts) t.join();
        return l.isFair() + " " + ql + " " + hq + h1 + barge + " " + order + " " + l.isLocked();
    }

    /** Uncaught exceptions reach the thread's handler, else the default one. */
    public static String uncaught(int n) throws Exception {
        List<String> seen = Collections.synchronizedList(new ArrayList<>());
        Thread a = new Thread(() -> { throw new IllegalStateException("a" + small(n)); });
        a.setUncaughtExceptionHandler((t, e) -> seen.add("own:" + e.getMessage()));
        a.start();
        a.join();
        Thread.setDefaultUncaughtExceptionHandler((t, e) -> seen.add("default:" + e.getMessage()));
        Thread b = new Thread(() -> { throw new RuntimeException("b"); });
        b.start();
        b.join();
        Thread.setDefaultUncaughtExceptionHandler(null);
        return seen + " " + a.isAlive() + b.isAlive();
    }
}

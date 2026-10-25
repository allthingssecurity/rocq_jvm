// Semaphore, Timer/TimerTask and ScheduledThreadPoolExecutor under the thread layer. Results do not
// depend on the schedule or on HotSpot's timing jitter: delays are far apart (>= 100 ms), counts are
// checked against ranges.
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;

public class SchedTests {
    static int small(int n) { return Math.floorMod(n, 10); }

    /** Two threads take and give back permits; the count is conserved. */
    public static String semaphoreCount(int n) throws Exception {
        int k = 1 + small(n);
        Semaphore s = new Semaphore(2, (n & 1) == 0);
        AtomicInteger inside = new AtomicInteger(), max = new AtomicInteger();
        Runnable r = () -> {
            for (int i = 0; i < k; i++) {
                try { s.acquire(); } catch (InterruptedException e) { return; }
                int v = inside.incrementAndGet();
                max.accumulateAndGet(v, Math::max);
                inside.decrementAndGet();
                s.release();
            }
        };
        Thread a = new Thread(r), b = new Thread(r), c = new Thread(r);
        a.start(); b.start(); c.start(); a.join(); b.join(); c.join();
        return s.availablePermits() + " " + (max.get() <= 2) + " " + s.hasQueuedThreads() + " " + s.isFair();
    }

    /** tryAcquire, timed tryAcquire that times out, release(n), drain, reduce (subclass). */
    static final class Reducible extends Semaphore {
        Reducible(int p) { super(p); }
        void reduce(int r) { reducePermits(r); }
    }
    public static String semaphoreOps(int n) throws Exception {
        int p = small(n);
        Reducible s = new Reducible(p);
        StringBuilder b = new StringBuilder();
        b.append(s.tryAcquire()).append(s.tryAcquire(2)).append(s.availablePermits()).append(' ');
        b.append(s.tryAcquire(p + 5, 100, TimeUnit.MILLISECONDS)).append(' ');
        s.release(3);
        s.reduce(1);
        b.append(s.availablePermits()).append(' ').append(s.drainPermits()).append(s.availablePermits());
        s.reduce(2);
        b.append(' ').append(s.drainPermits()).append(s.availablePermits());
        try { s.acquire(-1); } catch (IllegalArgumentException e) { b.append(" IAE"); }
        Thread.currentThread().interrupt();
        try { s.acquire(); } catch (InterruptedException e) { b.append(" IE"); }
        s.release();
        s.acquireUninterruptibly();
        b.append(' ').append(s.availablePermits());
        return b.toString();
    }

    /** A thread blocked in acquire is woken by release from another thread. */
    public static String semaphoreHandoff(int n) throws Exception {
        Semaphore s = new Semaphore(0, (n & 1) == 0);
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        Thread w = new Thread(() -> { try { s.acquire(2); log.add("got"); } catch (InterruptedException e) { log.add("ie"); } });
        w.start();
        Thread.sleep(100);
        log.add("q" + s.getQueueLength());
        s.release();
        Thread.sleep(100);
        log.add("still" + s.availablePermits());
        s.release();
        w.join();
        return log + " " + s.availablePermits();
    }

    /** Timer: tasks run in order of their delay; cancel; scheduledExecutionTime; exceptions kill it. */
    public static String timerOrder(int n) throws Exception {
        Timer t = new Timer();
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        int[] ds = { 300, 100, 200 };
        int rot = small(n) % 3;
        for (int i = 0; i < 3; i++) {
            int d = ds[(i + rot) % 3];
            t.schedule(new TimerTask() { public void run() { log.add("d" + d); } }, d);
        }
        TimerTask c = new TimerTask() { public void run() { log.add("cancelled-ran"); } };
        t.schedule(c, 150);
        boolean cc = c.cancel();
        Thread.sleep(500);
        String r = log + " " + cc + " " + c.cancel() + " " + t.purge();
        try { t.schedule(c, 10); } catch (IllegalStateException e) { r += " ISE"; }
        t.schedule(new TimerTask() { public void run() { throw new RuntimeException("x"); } }, 10);
        Thread.sleep(200);
        try { t.schedule(new TimerTask() { public void run() { } }, 10); r += " ok"; } catch (IllegalStateException e) { r += " dead:" + e.getMessage(); }
        t.cancel();
        return r;
    }

    /** Timer fixed-rate task: about one run per period. */
    public static String timerPeriodic(int n) throws Exception {
        Timer t = new Timer(true);
        AtomicInteger count = new AtomicInteger();
        TimerTask task = new TimerTask() { public void run() { count.incrementAndGet(); } };
        if ((n & 1) == 0) t.scheduleAtFixedRate(task, 0, 100);
        else t.schedule(task, 0, 100);
        Thread.sleep(450);
        task.cancel();
        int c = count.get();
        Thread.sleep(300);
        t.cancel();
        return (c >= 3 && c <= 6) + " " + (count.get() == c);
    }

    /** Scheduled executor: order by delay, Callable results, getDelay sign, cancel, errors. */
    public static String scheduledOrder(int n) throws Exception {
        ScheduledExecutorService ex = (n & 1) == 0 ? Executors.newScheduledThreadPool(2) : Executors.newSingleThreadScheduledExecutor();
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        int rot = small(n) % 3;
        int[] ds = { 300, 100, 200 };
        List<ScheduledFuture<?>> fs = new ArrayList<>();
        for (int i = 0; i < 3; i++) {
            int d = ds[(i + rot) % 3];
            fs.add(ex.schedule(() -> { log.add("d" + d); }, d, TimeUnit.MILLISECONDS));
        }
        ScheduledFuture<Integer> v = ex.schedule(() -> 42, 50, TimeUnit.MILLISECONDS);
        ScheduledFuture<?> bad = ex.schedule(() -> { throw new IllegalStateException("boom"); }, 10, TimeUnit.MILLISECONDS);
        ScheduledFuture<?> c = ex.schedule(() -> { log.add("cancelled-ran"); }, 250, TimeUnit.MILLISECONDS);
        boolean pos = c.getDelay(TimeUnit.MILLISECONDS) > 0;
        boolean cc = c.cancel(false);
        String r = v.get() + " " + pos + " " + cc + " " + c.isCancelled();
        try { bad.get(); } catch (ExecutionException e) { r += " EE:" + e.getCause().getMessage(); }
        for (ScheduledFuture<?> f : fs) f.get();
        r += " " + log;
        try { c.get(); } catch (CancellationException e) { r += " CE"; }
        try { ex.scheduleAtFixedRate(() -> { }, 0, 0, TimeUnit.MILLISECONDS); } catch (IllegalArgumentException e) { r += " IAE"; }
        ex.shutdown();
        r += " " + ex.awaitTermination(1, TimeUnit.SECONDS) + ex.isShutdown();
        return r;
    }

    /** Fixed-rate and fixed-delay tasks; an exception stops a periodic task; shutdown cancels them. */
    public static String scheduledPeriodic(int n) throws Exception {
        ScheduledExecutorService ex = Executors.newScheduledThreadPool(1);
        AtomicInteger a = new AtomicInteger(), b = new AtomicInteger(), c = new AtomicInteger();
        ScheduledFuture<?> fa = ex.scheduleAtFixedRate(a::incrementAndGet, 0, 100, TimeUnit.MILLISECONDS);
        ScheduledFuture<?> fb = ex.scheduleWithFixedDelay(b::incrementAndGet, 50, 100, TimeUnit.MILLISECONDS);
        ScheduledFuture<?> fc = ex.scheduleAtFixedRate(() -> { if (c.incrementAndGet() == 2) throw new RuntimeException("stop"); }, 0, 100, TimeUnit.MILLISECONDS);
        Thread.sleep(450);
        int ca = a.get(), cb = b.get();
        String r = (ca >= 3 && ca <= 6) + " " + (cb >= 2 && cb <= 6) + " " + c.get() + " " + fc.isDone();
        try { fc.get(); } catch (ExecutionException e) { r += " " + e.getCause().getMessage(); }
        boolean periodicDone = !fa.isDone();
        ex.shutdown();
        Thread.sleep(250);
        r += " " + periodicDone + " " + fa.isCancelled() + " " + fb.isCancelled() + " " + ex.awaitTermination(1, TimeUnit.SECONDS);
        return r;
    }

    static final class D implements Delayed {
        final long at; final String name;
        D(long ms, String name) { this.at = System.nanoTime() + ms * 1000000L; this.name = name; }
        public long getDelay(TimeUnit u) { return u.convert(at - System.nanoTime(), TimeUnit.NANOSECONDS); }
        public int compareTo(Delayed o) { return Long.compare(at, ((D) o).at); }
        public String toString() { return name; }
    }

    /** DelayQueue: poll before expiry, take in delay order, timed poll, peek, remove. */
    public static String delayQueue(int n) throws Exception {
        DelayQueue<D> q = new DelayQueue<>();
        int rot = small(n) % 3;
        int[] ds = { 300, 100, 200 };
        for (int i = 0; i < 3; i++) { int d = ds[(i + rot) % 3]; q.put(new D(d, "d" + d)); }
        D gone = new D(150, "gone");
        q.add(gone);
        StringBuilder b = new StringBuilder();
        b.append(q.poll()).append(' ').append(q.peek()).append(' ').append(q.size()).append(' ').append(q.remove(gone)).append(' ');
        b.append(q.poll(10, TimeUnit.MILLISECONDS)).append(' ');
        Thread t = new Thread(() -> { try { b.append(q.take()).append(' '); } catch (InterruptedException e) { } });
        t.start();
        t.join();
        b.append(q.take()).append(' ').append(q.take()).append(' ').append(q.size()).append(' ').append(q.poll());
        try { q.put(null); } catch (NullPointerException e) { b.append(" NPE"); }
        return b.toString();
    }
}

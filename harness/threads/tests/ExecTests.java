// Differential tests of the executor / timed-operation model classes (classes/threadmodel) under the
// thread layer: results independent of the schedule.
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;

public class ExecTests {
    static int small(int n) { return Math.floorMod(n, 20); }

    public static long fixedPool(int n) throws Exception {
        int k = small(n);
        ExecutorService es = Executors.newFixedThreadPool(3);
        List<Future<Long>> fs = new ArrayList<>();
        for (int i = 0; i < k; i++) { long x = i; fs.add(es.submit(() -> x * x + 1)); }
        long sum = 0;
        for (Future<Long> f : fs) sum += f.get();
        es.shutdown();
        boolean t = es.awaitTermination(1, TimeUnit.MINUTES);
        return sum * 10 + (t ? 1 : 0) + (es.isShutdown() ? 100000 : 0);
    }

    public static String singleOrder(int n) throws Exception {
        ExecutorService es = Executors.newSingleThreadExecutor();
        StringBuilder log = new StringBuilder();
        for (int i = 0; i < 1 + small(n) % 6; i++) { int j = i; es.execute(() -> log.append(j)); }
        Future<?> last = es.submit(() -> log.append('!'));
        Object r = last.get();
        es.shutdown();
        es.awaitTermination(1, TimeUnit.MINUTES);
        return log + " " + r + " " + last.isDone() + " " + es.isTerminated();
    }

    public static String futureErrors(int n) throws Exception {
        ExecutorService es = Executors.newCachedThreadPool();
        Future<Integer> f = es.submit(() -> { if (n % 2 == 0) throw new IllegalStateException("bad " + small(n)); return 1; });
        String out;
        try { out = "ok " + f.get(); }
        catch (ExecutionException e) { out = "EE " + e.getCause().getClass().getName() + " " + e.getCause().getMessage() + " | " + e.getMessage(); }
        es.shutdown();
        return out + " " + es.awaitTermination(1, TimeUnit.MINUTES);
    }

    public static String timeouts(int n) throws Exception {
        CountDownLatch never = new CountDownLatch(1);
        boolean a = never.await(1, TimeUnit.MILLISECONDS);
        CountDownLatch gate = new CountDownLatch(1);
        ReentrantLock lock = new ReentrantLock();
        CountDownLatch held = new CountDownLatch(1);
        Thread holder = new Thread(() -> { lock.lock(); try { held.countDown(); gate.await(); } catch (InterruptedException e) { } finally { lock.unlock(); } });
        holder.start();
        held.await();
        boolean b = lock.tryLock(2, TimeUnit.MILLISECONDS);
        holder.join(5);
        boolean alive = holder.isAlive();
        gate.countDown();
        holder.join();
        boolean c = lock.tryLock(1, TimeUnit.SECONDS);
        lock.unlock();
        long t1 = System.nanoTime(), t2 = System.nanoTime();
        return a + " " + b + " " + alive + " " + c + " " + (t2 >= t1) + " " + small(n);
    }

    public static String futureTimeout(int n) throws Exception {
        CountDownLatch gate = new CountDownLatch(1);
        ExecutorService es = Executors.newFixedThreadPool(1);
        Future<String> f = es.submit(() -> { gate.await(); return "done"; });
        String r;
        try { r = f.get(3, TimeUnit.MILLISECONDS); } catch (TimeoutException e) { r = "timeout"; }
        gate.countDown();
        r += " " + f.get(1, TimeUnit.MINUTES);
        es.shutdown();
        return r + " " + es.awaitTermination(1, TimeUnit.MINUTES) + " " + small(n);
    }

    public static String conditionTimed(int n) throws Exception {
        ReentrantLock lock = new ReentrantLock();
        Condition c = lock.newCondition();
        lock.lock();
        boolean t;
        try { t = c.await(1, TimeUnit.MILLISECONDS); } finally { lock.unlock(); }
        boolean[] ready = new boolean[1];
        Thread s = new Thread(() -> { lock.lock(); try { ready[0] = true; c.signalAll(); } finally { lock.unlock(); } });
        lock.lock();
        boolean u;
        try { s.start(); while (!ready[0]) c.await(); u = ready[0]; } finally { lock.unlock(); }
        s.join();
        return t + " " + u + " " + TimeUnit.SECONDS.toMillis(small(n)) + " " + TimeUnit.MILLISECONDS.toSeconds(1999) + " "
            + TimeUnit.DAYS.toNanos(Long.MAX_VALUE / 2) + " " + TimeUnit.NANOSECONDS.convert(3, TimeUnit.MINUTES);
    }
}

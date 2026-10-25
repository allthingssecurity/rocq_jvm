// Differential tests of the java.util.concurrent and ThreadLocal model classes (classes/threadmodel)
// under the thread layer: schedule-independent results.
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;

public class ConcTests {
    static int small(int n) { return Math.floorMod(n, 30); }

    public static int atomicCounter(int n) throws Exception {
        int k = small(n);
        AtomicInteger c = new AtomicInteger();
        Runnable r = () -> { for (int i = 0; i < k; i++) c.incrementAndGet(); };
        Thread a = new Thread(r), b = new Thread(r);
        a.start(); b.start(); r.run(); a.join(); b.join();
        return c.get() * 1000 + c.getAndAdd(5) + c.addAndGet(-2);
    }

    public static long atomicCas(int n) throws Exception {
        int k = small(n);
        AtomicLong c = new AtomicLong(n);
        Runnable r = () -> { for (int i = 0; i < k; i++) { long v; do { v = c.get(); } while (!c.compareAndSet(v, v * 3 + 1)); } };
        Thread a = new Thread(r);
        a.start(); r.run(); a.join();
        return c.get() + c.updateAndGet(x -> x ^ 0x5555) + c.accumulateAndGet(7, Long::sum);
    }

    public static String atomicMisc(int n) {
        AtomicBoolean b = new AtomicBoolean();
        boolean x = b.compareAndSet(false, true), y = b.compareAndSet(false, true);
        AtomicReference<String> s = new AtomicReference<>("a" + small(n));
        String old = s.getAndUpdate(v -> v + "!");
        AtomicInteger i = new AtomicInteger(n);
        int prev = i.getAndUpdate(v -> v * 2);
        return x + " " + y + " " + b + " " + old + " " + s.get() + " " + prev + " " + i + " " + i.longValue();
    }

    public static int latch(int n) throws Exception {
        int k = 1 + small(n) % 5;
        CountDownLatch start = new CountDownLatch(1), done = new CountDownLatch(k);
        AtomicInteger sum = new AtomicInteger();
        for (int j = 0; j < k; j++) {
            int w = j;
            new Thread(() -> {
                try { start.await(); } catch (InterruptedException e) { return; }
                sum.addAndGet(w * 10 + 1); done.countDown();
            }).start();
        }
        int before = sum.get();
        start.countDown();
        done.await();
        return before * 100000 + sum.get() * 10 + (int) done.getCount();
    }

    public static int lockCounter(int n) throws Exception {
        int k = small(n);
        ReentrantLock lock = new ReentrantLock();
        int[] c = new int[1];
        Runnable r = () -> { for (int i = 0; i < k; i++) { lock.lock(); try { lock.lock(); c[0]++; lock.unlock(); } finally { lock.unlock(); } } };
        Thread a = new Thread(r), b = new Thread(r);
        a.start(); b.start(); r.run(); a.join(); b.join();
        return c[0] * 10 + (lock.isLocked() ? 1 : 0) + lock.getHoldCount();
    }

    public static String lockErrors(int n) {
        ReentrantLock lock = new ReentrantLock();
        String r;
        try { lock.unlock(); r = "no"; } catch (IllegalMonitorStateException e) { r = "IMSE"; }
        boolean t1 = lock.tryLock(), t2 = lock.tryLock();
        int h = lock.getHoldCount();
        lock.unlock(); lock.unlock();
        Condition c = lock.newCondition();
        try { c.signal(); r += " no"; } catch (IllegalMonitorStateException e) { r += " IMSE2"; }
        return r + " " + t1 + " " + t2 + " " + h + " " + lock.isLocked() + " " + small(n);
    }

    static final class Buffer {
        final ReentrantLock lock = new ReentrantLock();
        final Condition notEmpty = lock.newCondition(), notFull = lock.newCondition();
        final int[] items = new int[2]; int putI, takeI, count;
        void put(int x) throws InterruptedException {
            lock.lock();
            try { while (count == items.length) notFull.await(); items[putI] = x; putI = (putI + 1) % items.length; count++; notEmpty.signal(); }
            finally { lock.unlock(); }
        }
        int take() throws InterruptedException {
            lock.lock();
            try { while (count == 0) notEmpty.await(); int x = items[takeI]; takeI = (takeI + 1) % items.length; count--; notFull.signal(); return x; }
            finally { lock.unlock(); }
        }
    }

    public static int conditionBuffer(int n) throws Exception {
        int k = small(n);
        Buffer buf = new Buffer();
        Thread p1 = new Thread(() -> { try { for (int i = 0; i < k; i++) buf.put(i); } catch (InterruptedException e) { } });
        Thread p2 = new Thread(() -> { try { for (int i = 0; i < k; i++) buf.put(1000 + i); } catch (InterruptedException e) { } });
        p1.start(); p2.start();
        int sum = 0;
        for (int i = 0; i < 2 * k; i++) sum += buf.take();
        p1.join(); p2.join();
        return sum;
    }

    static final ThreadLocal<Integer> TL = ThreadLocal.withInitial(() -> 7);
    static final ThreadLocal<String> TS = new ThreadLocal<>();

    public static String threadLocals(int n) throws Exception {
        String[] other = new String[1];
        TL.set(small(n));
        TS.set("main");
        Thread t = new Thread(() -> { int a = TL.get(); TL.set(a + 1); other[0] = a + "," + TL.get() + "," + TS.get(); });
        t.start(); t.join();
        int mine = TL.get();
        TL.remove();
        return mine + " " + other[0] + " " + TL.get() + " " + TS.get();
    }

    public static String interruptLock(int n) throws Exception {
        ReentrantLock lock = new ReentrantLock();
        String[] out = new String[1];
        lock.lock();
        Thread t = new Thread(() -> {
            try { lock.lockInterruptibly(); out[0] = "locked"; lock.unlock(); }
            catch (InterruptedException e) { out[0] = "IE"; }
        });
        t.start();
        t.interrupt();
        t.join();
        lock.unlock();
        return out[0] + " " + small(n);
    }
}

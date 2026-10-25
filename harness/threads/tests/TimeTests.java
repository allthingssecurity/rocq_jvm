// Timeouts under the thread layer: the earliest deadline ends first, whether a sleep or a timed
// wait, and a sleep never ends early. Delays are 100 ms apart, so HotSpot's jitter does not matter.
import java.util.*;
import java.util.concurrent.*;

public class TimeTests {
    /** A sleep of 500 ms ends near 500 ms although another thread waits until 1000 ms. */
    public static String sleepVsTimedWait(int n) throws Exception {
        Object lock = new Object();
        Thread t = new Thread(() -> { synchronized (lock) { try { lock.wait(1000); } catch (InterruptedException e) { } } });
        t.start();
        long t0 = System.currentTimeMillis();
        Thread.sleep(500);
        long el = System.currentTimeMillis() - t0;
        t.join();
        long all = System.currentTimeMillis() - t0;
        return (el >= 500 && el < 900) + " " + (all >= 1000 && all < 1400);
    }

    /** Three timed waits started in the reverse order of their deadlines wake in deadline order. */
    public static String deadlineOrder(int n) throws Exception {
        List<String> order = Collections.synchronizedList(new ArrayList<>());
        int[] ds = { 300, 200, 100 };
        Thread[] ts = new Thread[3];
        for (int i = 0; i < 3; i++) {
            int d = ds[(i + (n & 1)) % 3];
            Object m = new Object();
            ts[i] = new Thread(() -> { synchronized (m) { try { m.wait(d); } catch (InterruptedException e) { } } order.add("w" + d); });
            ts[i].start();
        }
        Thread.sleep(150 + 100 * Math.floorMod(n, 2));
        String mid = order.toString();
        for (Thread t : ts) t.join();
        return mid + " " + order;
    }

    /** Timed acquire, poll and await against sleeps of other threads. */
    public static String mixed(int n) throws Exception {
        Semaphore s = new Semaphore(0);
        CountDownLatch l = new CountDownLatch(1);
        BlockingQueue<Integer> q = new LinkedBlockingQueue<>();
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        Thread a = new Thread(() -> { try { log.add("a" + s.tryAcquire(300, TimeUnit.MILLISECONDS)); } catch (InterruptedException e) { } });
        Thread b = new Thread(() -> { try { log.add("b" + q.poll(100, TimeUnit.MILLISECONDS)); } catch (InterruptedException e) { } });
        Thread c = new Thread(() -> { try { log.add("c" + l.await(500, TimeUnit.MILLISECONDS)); } catch (InterruptedException e) { } });
        a.start(); b.start(); c.start();
        Thread.sleep(200);
        log.add("m");
        s.release();
        a.join(); b.join(); c.join();
        return log.toString();
    }
}

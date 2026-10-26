// Differential tests of the thread layer (theories/Core/Threads.v): race-free programs whose
// result does not depend on the schedule. The machine runs each input under several schedulers
// and all of them must agree with HotSpot.
public class ThreadTests {
    static int small(int n) { return Math.floorMod(n, 40); }

    // ---- monitors ----
    static final class Counter { int n; synchronized void inc() { n++; } static int sn; static synchronized void sinc() { sn++; } }

    public static int syncBlock(int n) throws Exception {
        int k = small(n);
        Object lock = new Object();
        int[] c = new int[1];
        Runnable r = () -> { for (int i = 0; i < k; i++) synchronized (lock) { c[0]++; } };
        Thread a = new Thread(r), b = new Thread(r);
        a.start(); b.start(); r.run(); a.join(); b.join();
        return c[0];
    }

    public static int syncMethod(int n) throws Exception {
        int k = small(n);
        Counter c = new Counter();
        Thread a = new Thread(() -> { for (int i = 0; i < k; i++) c.inc(); });
        Thread b = new Thread(() -> { for (int i = 0; i < k; i++) c.inc(); });
        a.start(); b.start(); a.join(); b.join();
        return c.n;
    }

    public static int staticSync(int n) throws Exception {
        int k = small(n);
        Counter.sn = 0;
        Thread[] ts = new Thread[3];
        for (int j = 0; j < 3; j++) { ts[j] = new Thread(() -> { for (int i = 0; i < k; i++) Counter.sinc(); }); ts[j].start(); }
        for (Thread t : ts) t.join();
        return Counter.sn;
    }

    public static int reentrant(int n) throws Exception {
        int k = small(n);
        Object lock = new Object();
        int[] c = new int[1];
        Thread a = new Thread(() -> { for (int i = 0; i < k; i++) synchronized (lock) { synchronized (lock) { c[0] += 2; } c[0]--; } });
        a.start();
        for (int i = 0; i < k; i++) synchronized (lock) { c[0]++; }
        a.join();
        return c[0];
    }

    // ---- join and visibility ----
    public static long joinResult(int n) throws Exception {
        long[] out = new long[1];
        Thread t = new Thread(() -> { long s = 0; for (int i = 0; i <= small(n); i++) s += (long) i * i; out[0] = s; });
        t.start(); t.join();
        return out[0];
    }

    public static int aliveStates(int n) throws Exception {
        Object go = new Object();
        boolean[] flag = new boolean[1];
        Thread t = new Thread(() -> { synchronized (go) { while (!flag[0]) { try { go.wait(); } catch (InterruptedException e) { } } } });
        int r = t.isAlive() ? 1 : 0;
        t.start();
        boolean during = t.isAlive();
        synchronized (go) { flag[0] = true; go.notifyAll(); }
        t.join();
        return r * 100 + (during ? 10 : 0) + (t.isAlive() ? 1 : 0) + small(n) * 1000;
    }

    // ---- wait / notify ----
    static final class Slot {
        int value; boolean full;
        synchronized void put(int v) throws InterruptedException { while (full) wait(); value = v; full = true; notifyAll(); }
        synchronized int take() throws InterruptedException { while (!full) wait(); full = false; notifyAll(); return value; }
    }

    public static int producerConsumer(int n) throws Exception {
        int k = small(n);
        Slot s = new Slot();
        Thread p = new Thread(() -> { try { for (int i = 1; i <= k; i++) s.put(i * 3); } catch (InterruptedException e) { } });
        p.start();
        int sum = 0;
        for (int i = 0; i < k; i++) sum += s.take();
        p.join();
        return sum;
    }

    public static int pingPong(int n) throws Exception {
        int k = small(n);
        Object lock = new Object();
        int[] turn = new int[1];
        int[] log = new int[1];
        Thread b = new Thread(() -> {
            try {
                for (int i = 0; i < k; i++) synchronized (lock) {
                    while (turn[0] != 1) lock.wait();
                    log[0] = log[0] * 3 % 1000003 + 2; turn[0] = 0; lock.notify();
                }
            } catch (InterruptedException e) { }
        });
        b.start();
        for (int i = 0; i < k; i++) synchronized (lock) {
            while (turn[0] != 0) lock.wait();
            log[0] = log[0] * 7 % 1000003 + 1; turn[0] = 1; lock.notify();
        }
        b.join();
        return log[0];
    }

    // wait restores a reentrant entry count
    public static int waitReentrant(int n) throws Exception {
        Object lock = new Object();
        int[] st = new int[1];
        Thread w = new Thread(() -> {
            synchronized (lock) { synchronized (lock) {
                st[0] = 1; lock.notifyAll();
                while (st[0] != 2) { try { lock.wait(); } catch (InterruptedException e) { } }
                st[0] = 3;
            } st[0] += 10; }
        });
        w.start();
        synchronized (lock) {
            while (st[0] != 1) lock.wait();
            st[0] = 2; lock.notifyAll();
        }
        w.join();
        return st[0] + small(n);
    }

    // ---- exceptions ----
    public static String notOwner(int n) {
        Object o = new Object();
        try { if (n % 2 == 0) o.notify(); else o.wait(); return "none"; }
        catch (IllegalMonitorStateException e) { return "IMSE " + e.getMessage(); }
        catch (InterruptedException e) { return "IE"; }
    }

    public static String negativeWait(int n) throws Exception {
        Object o = new Object();
        synchronized (o) {
            try { o.wait(-1 - small(n)); return "none"; } catch (IllegalArgumentException e) { return "IAE " + e.getMessage(); }
        }
    }

    public static int doubleStart(int n) throws Exception {
        Thread t = new Thread(() -> { });
        t.start();
        try { t.start(); return 0; } catch (IllegalThreadStateException e) { t.join(); return 1 + small(n); }
    }

    static final class Res { int v; synchronized void boom(int x) { v += x; if (x % 2 == 1) throw new IllegalStateException("odd"); } }

    // an exception leaving a synchronized method exits its monitor
    public static int syncThrows(int n) throws Exception {
        int k = small(n);
        Res r = new Res();
        Runnable job = () -> { for (int i = 0; i < k; i++) { try { r.boom(i); } catch (IllegalStateException e) { } } };
        Thread a = new Thread(job);
        a.start(); job.run(); a.join();
        return r.v;
    }

    // an exception that kills a thread does not affect the joiner
    public static int deadThread(int n) throws Exception {
        int[] c = new int[1];
        Thread t = new Thread(() -> { c[0] = 5; if (c[0] == 5) throw new ArithmeticException("boom"); });
        t.start(); t.join();
        return c[0] * 10 + (t.isAlive() ? 1 : 0) + small(n) * 100;
    }

    // ---- threads and names ----
    public static String names(int n) throws Exception {
        String[] got = new String[1];
        Thread t = new Thread(() -> got[0] = Thread.currentThread().getName(), "worker-" + small(n));
        t.start(); t.join();
        return Thread.currentThread().getName() + "/" + got[0] + "/" + (Thread.currentThread() == t ? "same" : "other");
    }

    /** A new thread takes its creator's daemon status and priority. */
    public static String inherit(int n) throws Exception {
        StringBuilder out = new StringBuilder();
        boolean d = (n & 1) != 0;
        int pr = 1 + Math.floorMod(n, 10);
        Thread t = new Thread(() -> {
            Thread c = new Thread(() -> { });
            Thread c2 = new Thread(() -> { }, "c2");
            synchronized (out) { out.append(c.isDaemon()).append(c.getPriority()).append(c2.isDaemon()).append(c2.getPriority()); }
        }, "p");
        t.setDaemon(d);
        t.setPriority(pr);
        Thread m = new Thread(() -> { });
        out.append(m.isDaemon()).append(m.getPriority()).append(';');
        t.start();
        t.join();
        return out.toString();
    }

    static final class Sub extends Thread {
        final int[] out; final int k;
        Sub(int[] out, int k) { super("sub"); this.out = out; this.k = k; }
        @Override public void run() { for (int i = 0; i < k; i++) out[0] += i; }
    }

    public static int subclass(int n) throws Exception {
        int[] out = new int[1];
        Sub s = new Sub(out, small(n));
        s.start(); s.join();
        return out[0];
    }

    // ---- class initialisation from two threads (JLS 12.4.2) ----
    static final class Lazy {
        static final int[] TABLE;
        static { TABLE = new int[50]; for (int i = 0; i < 50; i++) TABLE[i] = i * i + 1; }
    }

    public static int initRace(int n) throws Exception {
        int[] r = new int[2];
        Thread a = new Thread(() -> r[0] = Lazy.TABLE[small(n)]);
        a.start();
        r[1] = Lazy.TABLE[49 - small(n)];
        a.join();
        return r[0] * 10000 + r[1];
    }

    // ---- sleep / yield ----
    public static int sleepYield(int n) throws Exception {
        int[] c = new int[1];
        Object lock = new Object();
        Thread a = new Thread(() -> { for (int i = 0; i < 3; i++) { Thread.yield(); synchronized (lock) { c[0]++; } } });
        a.start();
        Thread.sleep(1);
        synchronized (lock) { c[0] += 10; }
        a.join();
        return c[0] + small(n);
    }

    // ---- interrupts (JLS 17.2.3) ----
    public static String interruptWait(int n) throws Exception {
        Object lock = new Object();
        String[] out = new String[1];
        boolean[] ready = new boolean[1];
        Thread t = new Thread(() -> {
            synchronized (lock) {
                ready[0] = true; lock.notifyAll();
                try { while (true) lock.wait(); }
                catch (InterruptedException e) { out[0] = "IE " + e.getMessage() + " " + Thread.currentThread().isInterrupted(); }
            }
        });
        t.start();
        synchronized (lock) { while (!ready[0]) lock.wait(); }
        t.interrupt();
        t.join();
        return out[0] + " " + small(n);
    }

    public static String interruptSleep(int n) throws Exception {
        String[] out = new String[1];
        Thread t = new Thread(() -> {
            try { Thread.sleep(100000); out[0] = "slept"; }
            catch (InterruptedException e) { out[0] = "IE " + e.getMessage() + " " + Thread.currentThread().isInterrupted(); }
        });
        t.start();
        t.interrupt();
        t.join();
        return out[0] + " " + small(n);
    }

    public static String interruptedClears(int n) {
        Thread.currentThread().interrupt();
        boolean a = Thread.currentThread().isInterrupted();
        boolean b = Thread.interrupted();
        boolean c = Thread.interrupted();
        return a + " " + b + " " + c + " " + small(n);
    }

    public static String selfInterruptWait(int n) {
        Object o = new Object();
        Thread.currentThread().interrupt();
        synchronized (o) {
            try { o.wait(); return "returned"; }
            catch (InterruptedException e) { return "IE " + e.getMessage() + " " + Thread.currentThread().isInterrupted() + " " + small(n); }
        }
    }

    public static String interruptJoin(int n) throws Exception {
        Object lock = new Object();
        boolean[] go = new boolean[1];
        Thread t = new Thread(() -> { synchronized (lock) { while (!go[0]) { try { lock.wait(); } catch (InterruptedException e) { } } } });
        t.start();
        Thread.currentThread().interrupt();
        String r;
        try { t.join(); r = "joined"; } catch (InterruptedException e) { r = "IE " + e.getMessage(); }
        synchronized (lock) { go[0] = true; lock.notifyAll(); }
        t.join();
        return r + " " + Thread.interrupted() + " " + small(n);
    }

    public static String interruptBeforeStart(int n) throws Exception {
        String[] out = new String[1];
        Thread t = new Thread(() -> out[0] = "flag " + Thread.currentThread().isInterrupted());
        t.interrupt();
        boolean before = t.isInterrupted();
        t.start(); t.join();
        return before + " " + out[0] + " " + small(n);
    }

    // ---- monitors held by synchronized methods, one thread (also run on the single-thread machine) ----
    static final class Mon {
        int n;
        synchronized int bump() { n++; notify(); notifyAll(); return n; }
        static synchronized int sbump(int k) { ThreadTests.Mon.class.notifyAll(); return k + 1; }
        int outside() { try { notify(); return 0; } catch (IllegalMonitorStateException e) { return -1; } }
        synchronized int nested() { synchronized (this) { notify(); } notify(); return 7; }
    }

    public static int syncNotify(int n) {
        Mon m = new Mon();
        return m.bump() * 1000 + Mon.sbump(small(n)) * 10 + m.outside() + m.nested() * 100000;
    }
}

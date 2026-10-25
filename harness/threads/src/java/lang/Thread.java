/*
 * Clean-room model of java.lang.Thread for the Rocq JVM machine (theories/Core/Threads.v).
 * Loaded only by the machine, never by HotSpot. The thread layer implements the private
 * natives start0, join0, isAlive0, currentThread, sleep0 and yield0. Everything the model
 * does not cover (thread groups, toString) is a native without a model, so a run that uses it is STUCK (no claim).
 * Written from the JDK 21 javadoc and source of java.lang.Thread.
 */
package java.lang;

public class Thread implements Runnable {
    public static final int MIN_PRIORITY = 1;
    public static final int NORM_PRIORITY = 5;
    public static final int MAX_PRIORITY = 10;

    private static int threadNumber;        // "Thread-" + n, as ThreadNumbering in JDK 21

    private Runnable target;
    private String name;
    private boolean daemon;
    private int priority = NORM_PRIORITY;
    private boolean started;

    private static synchronized int nextThreadNum() { return threadNumber++; }

    public Thread() { this.name = "Thread-" + nextThreadNum(); }
    public Thread(Runnable task) { this.target = task; this.name = "Thread-" + nextThreadNum(); }
    public Thread(String name) { this.name = checkName(name); }
    public Thread(Runnable task, String name) { this.target = task; this.name = checkName(name); }

    private static String checkName(String name) {
        if (name == null) throw new NullPointerException("'name' is null");
        return name;
    }

    @Override
    public void run() {
        Runnable task = target;
        if (task != null) task.run();
    }

    // Uncaught exceptions (JDK 21 Thread.dispatchUncaughtException): the thread's handler, else
    // the default handler, else the thread group's, which prints to System.err (not modelled:
    // nothing observable on stdout). The thread layer starts every thread here.
    @FunctionalInterface
    public interface UncaughtExceptionHandler {
        void uncaughtException(Thread t, Throwable e);
    }
    private volatile UncaughtExceptionHandler uncaughtExceptionHandler;
    private static volatile UncaughtExceptionHandler defaultUncaughtExceptionHandler;
    public void setUncaughtExceptionHandler(UncaughtExceptionHandler ueh) { uncaughtExceptionHandler = ueh; }
    public UncaughtExceptionHandler getUncaughtExceptionHandler() { return uncaughtExceptionHandler; }
    public static void setDefaultUncaughtExceptionHandler(UncaughtExceptionHandler ueh) { defaultUncaughtExceptionHandler = ueh; }
    public static UncaughtExceptionHandler getDefaultUncaughtExceptionHandler() { return defaultUncaughtExceptionHandler; }
    private void runEntry() {
        try {
            run();
        } catch (Throwable e) {
            UncaughtExceptionHandler h = uncaughtExceptionHandler;
            if (h == null) h = defaultUncaughtExceptionHandler;
            if (h != null) h.uncaughtException(this, e);
        }
    }

    public void start() {
        synchronized (this) {
            if (started) throw new IllegalThreadStateException();
            started = true;
        }
        start0();
    }
    private native void start0();

    public final void join() throws InterruptedException { join0(); }
    public final void join(long millis) throws InterruptedException {
        if (millis < 0) throw new IllegalArgumentException("timeout value is negative");
        if (millis == 0) { join0(); return; }
        // as the JDK: wait on this Thread object, which the VM notifies when the thread ends
        synchronized (this) {
            long deadline = System.nanoTime() + millis * 1000000L;
            while (isAlive()) {
                long rem = deadline - System.nanoTime();
                if (rem <= 0) return;
                wait(Math.max(1, rem / 1000000L));
            }
        }
    }
    private native void join0();

    public final boolean isAlive() { return isAlive0(); }
    private native boolean isAlive0();

    public static native Thread currentThread();

    public static void sleep(long millis) throws InterruptedException {
        if (millis < 0) throw new IllegalArgumentException("timeout value is negative");
        sleep0(millis);
    }
    private static native void sleep0(long millis);

    public static void yield() { yield0(); }
    private static native void yield0();

    public static void onSpinWait() { }

    public final String getName() { return name; }
    public final synchronized void setName(String name) { this.name = checkName(name); }
    public final boolean isDaemon() { return daemon; }
    public final void setDaemon(boolean on) {
        if (started) throw new IllegalThreadStateException();
        daemon = on;
    }
    public final int getPriority() { return priority; }
    public final void setPriority(int p) {
        if (p > MAX_PRIORITY || p < MIN_PRIORITY) throw new IllegalArgumentException();
        priority = p;
    }

    // The interrupt status, as in JDK 21 (a field of the Thread object). interrupt0 tells the
    // thread layer, which wakes the thread from wait or sleep with an InterruptedException.
    private volatile boolean interrupted;
    public void interrupt() { interrupted = true; interrupt0(); }
    private native void interrupt0();
    public boolean isInterrupted() { return interrupted; }
    public static boolean interrupted() {
        Thread t = currentThread();
        boolean b = t.interrupted;
        if (b) t.interrupted = false;
        return b;
    }

    public long threadId() { return threadId0(); }
    @Deprecated public long getId() { return threadId0(); }
    private native long threadId0();
    @Override public String toString() { return toString0(); }

    // ThreadLocal values of this thread (ThreadLocal.java)
    Object[] tlKeys;     // allocated on first use (the main thread's object is made by the VM)
    Object[] tlVals;
    int tlSize;
    int tlIndex(Object key) {
        for (int i = 0; i < tlSize; i++) if (tlKeys[i] == key) return i;
        return -1;
    }
    void tlPut(Object key, Object value) {
        int i = tlIndex(key);
        if (i >= 0) { tlVals[i] = value; return; }
        if (tlKeys == null) { tlKeys = new Object[4]; tlVals = new Object[4]; }
        if (tlSize == tlKeys.length) {
            Object[] k = new Object[tlSize * 2], v = new Object[tlSize * 2];
            System.arraycopy(tlKeys, 0, k, 0, tlSize); System.arraycopy(tlVals, 0, v, 0, tlSize);
            tlKeys = k; tlVals = v;
        }
        tlKeys[tlSize] = key; tlVals[tlSize] = value; tlSize++;
    }
    void tlRemove(Object key) {
        int i = tlIndex(key);
        if (i < 0) return;
        tlSize--;
        tlKeys[i] = tlKeys[tlSize]; tlVals[i] = tlVals[tlSize];
        tlKeys[tlSize] = null; tlVals[tlSize] = null;
    }
    private native String toString0();
}

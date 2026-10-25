/*
 * Clean-room model of FutureTask over a monitor. States as in the JDK: NEW, COMPLETING (not
 * observable here), NORMAL, EXCEPTIONAL, CANCELLED, INTERRUPTED. get() waits; a timed get may
 * time out at any point (the thread layer's timed wait), as in the JDK.
 */
package java.util.concurrent;

public class FutureTask<V> implements Runnable, Future<V> {
    private static final int NEW = 0, NORMAL = 2, EXCEPTIONAL = 3, CANCELLED = 4, INTERRUPTED = 6;
    private int state = NEW;
    private Callable<V> callable;
    private Object outcome;
    private Thread runner;

    public FutureTask(Callable<V> callable) {
        if (callable == null) throw new NullPointerException();
        this.callable = callable;
    }
    public FutureTask(Runnable runnable, V result) {
        if (runnable == null) throw new NullPointerException();
        this.callable = () -> { runnable.run(); return result; };
    }

    public void run() {
        Callable<V> c;
        synchronized (this) {
            if (state != NEW || runner != null) return;
            runner = Thread.currentThread();
            c = callable;
        }
        V result = null; Throwable ex = null; boolean ok;
        try { result = c.call(); ok = true; }
        catch (Throwable t) { ex = t; ok = false; }
        synchronized (this) {
            runner = null;
            if (state == NEW) {
                if (ok) { outcome = result; state = NORMAL; } else { outcome = ex; state = EXCEPTIONAL; }
                callable = null;
                notifyAll();
            }
        }
        done();
    }
    protected void done() { }

    public synchronized boolean cancel(boolean mayInterruptIfRunning) {
        if (state != NEW) return false;
        state = mayInterruptIfRunning ? INTERRUPTED : CANCELLED;
        if (mayInterruptIfRunning && runner != null) runner.interrupt();
        notifyAll();
        return true;
    }
    public synchronized boolean isCancelled() { return state >= CANCELLED; }
    public synchronized boolean isDone() { return state != NEW; }

    @SuppressWarnings("unchecked")
    private V report() throws ExecutionException {
        if (state == NORMAL) return (V) outcome;
        if (state >= CANCELLED) throw new CancellationException();
        throw new ExecutionException((Throwable) outcome);
    }
    public synchronized V get() throws InterruptedException, ExecutionException {
        while (state == NEW) wait();
        return report();
    }
    public synchronized V get(long timeout, TimeUnit unit) throws InterruptedException, ExecutionException, TimeoutException {
        if (unit == null) throw new NullPointerException();
        long nanos = unit.toNanos(timeout);
        long deadline = System.nanoTime() + nanos;
        while (state == NEW) {
            if (nanos <= 0) throw new TimeoutException();
            wait(Math.max(1, nanos / 1000000L));
            nanos = deadline - System.nanoTime();
        }
        return report();
    }
}

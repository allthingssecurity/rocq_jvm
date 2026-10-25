/*
 * Clean-room model of the executors of Executors.newFixedThreadPool / newSingleThreadExecutor /
 * newCachedThreadPool: worker threads take tasks from a FIFO queue. Started lazily, one worker per
 * submitted task up to the core size (fixed) or one per task when none is idle (cached), as
 * ThreadPoolExecutor does. Thread names, keep-alive and rejection after shutdown are not modelled
 * (rejection is STUCK). Package-private: reached through Executors.
 */
package java.util.concurrent;

import java.util.ArrayList;
import java.util.List;

class ThreadPool implements ExecutorService {
    private final int max;          // Integer.MAX_VALUE: cached
    private Runnable[] queue = new Runnable[8];
    private int head, count;
    private int workers, idle;
    private boolean shutdown;

    ThreadPool(int max) {
        if (max <= 0) throw new IllegalArgumentException();
        this.max = max;
    }

    public void execute(Runnable command) {
        if (command == null) throw new NullPointerException();
        boolean start;
        synchronized (this) {
            if (shutdown) rejected0();
            if (count == queue.length) {
                Runnable[] q = new Runnable[queue.length * 2];
                for (int i = 0; i < count; i++) q[i] = queue[(head + i) % queue.length];
                queue = q; head = 0;
            }
            queue[(head + count) % queue.length] = command; count++;
            start = workers < max && idle < count;
            if (start) workers++;
            else notifyAll();
        }
        if (start) new Thread(this::work).start();
    }
    private native void rejected0();

    private void work() {
        for (;;) {
            Runnable task;
            synchronized (this) {
                while (count == 0 && !shutdown) {
                    idle++;
                    try { wait(); } catch (InterruptedException e) { }
                    idle--;
                }
                if (count == 0) { workers--; notifyAll(); return; }
                task = queue[head]; queue[head] = null; head = (head + 1) % queue.length; count--;
            }
            try { task.run(); } catch (Throwable t) { }
        }
    }

    public <T> Future<T> submit(Callable<T> task) { FutureTask<T> f = new FutureTask<>(task); execute(f); return f; }
    public <T> Future<T> submit(Runnable task, T result) { FutureTask<T> f = new FutureTask<>(task, result); execute(f); return f; }
    public Future<?> submit(Runnable task) { FutureTask<Object> f = new FutureTask<>(task, null); execute(f); return f; }

    public synchronized void shutdown() { shutdown = true; notifyAll(); }
    public synchronized List<Runnable> shutdownNow() {
        shutdown = true;
        List<Runnable> rest = new ArrayList<>();
        for (int i = 0; i < count; i++) rest.add(queue[(head + i) % queue.length]);
        count = 0; notifyAll();
        return rest;
    }
    public synchronized boolean isShutdown() { return shutdown; }
    public synchronized boolean isTerminated() { return shutdown && workers == 0 && count == 0; }
    public synchronized boolean awaitTermination(long timeout, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(timeout);
        long deadline = System.nanoTime() + nanos;
        while (!isTerminated()) {
            if (nanos <= 0) return false;
            wait(Math.max(1, nanos / 1000000L));
            nanos = deadline - System.nanoTime();
        }
        return true;
    }
}

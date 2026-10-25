/*
 * Clean-room model of java.util.concurrent.ThreadPoolExecutor, for the thread layer, written
 * from the class Javadoc ("Core and maximum pool sizes", "Queuing", "Rejected tasks", "Hook
 * methods", "Keep-alive times", "Finalization") and the documented behaviour of execute:
 *   1. fewer than corePoolSize threads: start a new thread with the task as its first task;
 *   2. else queue the task (offer); if the pool has no thread then, start one;
 *   3. else start a new thread if fewer than maximumPoolSize, otherwise reject.
 * Workers take tasks with take() (or poll(keepAlive) when they may time out: more than core
 * threads, or allowCoreThreadTimeOut). A task that throws ends its worker (the exception reaches
 * the thread's uncaught-exception handler) and a replacement is started if needed. shutdown()
 * lets queued tasks finish and interrupts idle workers; shutdownNow() interrupts all workers
 * and returns the queued tasks. The pool state is guarded by this object's monitor.
 *
 * Differences: the run state and worker count are plain fields under the monitor (the JDK packs
 * them in one atomic int); the message of the AbortPolicy exception is computed when it is
 * read (it contains Object.toString of the pool, which needs an identity hash code: reading it
 * is STUCK unless the pool's class overrides toString).
 */
package java.util.concurrent;

import java.util.ArrayList;
import java.util.List;

public class ThreadPoolExecutor extends AbstractExecutorService {
    private static final int RUNNING = 0, SHUTDOWN = 1, STOP = 2, TIDYING = 3, TERMINATED = 4;

    private int runState = RUNNING;
    private int workerCount;
    private final BlockingQueue<Runnable> workQueue;
    private final ArrayList<Worker> workers = new ArrayList<>();
    private int largestPoolSize;
    private long completedTaskCount;
    private volatile ThreadFactory threadFactory;
    private volatile RejectedExecutionHandler handler;
    private volatile long keepAliveTime;
    private volatile boolean allowCoreThreadTimeOut;
    private volatile int corePoolSize;
    private volatile int maximumPoolSize;
    private static final RejectedExecutionHandler defaultHandler = new AbortPolicy();

    private final class Worker implements Runnable {
        final Thread thread;
        Runnable firstTask;
        boolean running;
        long completedTasks;

        Worker(Runnable firstTask) {
            this.firstTask = firstTask;
            this.thread = getThreadFactory().newThread(this);
        }

        public void run() {
            runWorker(this);
        }
    }

    public ThreadPoolExecutor(int corePoolSize, int maximumPoolSize, long keepAliveTime, TimeUnit unit,
                              BlockingQueue<Runnable> workQueue) {
        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue, Executors.defaultThreadFactory(), defaultHandler);
    }

    public ThreadPoolExecutor(int corePoolSize, int maximumPoolSize, long keepAliveTime, TimeUnit unit,
                              BlockingQueue<Runnable> workQueue, ThreadFactory threadFactory) {
        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue, threadFactory, defaultHandler);
    }

    public ThreadPoolExecutor(int corePoolSize, int maximumPoolSize, long keepAliveTime, TimeUnit unit,
                              BlockingQueue<Runnable> workQueue, RejectedExecutionHandler handler) {
        this(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue, Executors.defaultThreadFactory(), handler);
    }

    public ThreadPoolExecutor(int corePoolSize, int maximumPoolSize, long keepAliveTime, TimeUnit unit,
                              BlockingQueue<Runnable> workQueue, ThreadFactory threadFactory, RejectedExecutionHandler handler) {
        if (corePoolSize < 0 || maximumPoolSize <= 0 || maximumPoolSize < corePoolSize || keepAliveTime < 0)
            throw new IllegalArgumentException();
        if (workQueue == null || threadFactory == null || handler == null) throw new NullPointerException();
        this.corePoolSize = corePoolSize;
        this.maximumPoolSize = maximumPoolSize;
        this.workQueue = workQueue;
        this.keepAliveTime = unit.toNanos(keepAliveTime);
        this.threadFactory = threadFactory;
        this.handler = handler;
    }

    // ---- workers ----

    private boolean addWorker(Runnable firstTask, boolean core) {
        synchronized (this) {
            if (runState >= SHUTDOWN && (runState >= STOP || firstTask != null || workQueue.isEmpty())) return false;
            if (workerCount >= (core ? corePoolSize : maximumPoolSize)) return false;
            workerCount++;
        }
        Worker w = null;
        boolean started = false;
        try {
            w = new Worker(firstTask);
            Thread t = w.thread;
            if (t != null) {
                synchronized (this) {
                    if (runState < SHUTDOWN || (runState < STOP && firstTask == null)) {
                        workers.add(w);
                        if (workers.size() > largestPoolSize) largestPoolSize = workers.size();
                    } else {
                        t = null;
                    }
                }
                if (t != null) {
                    t.start();
                    started = true;
                }
            }
        } finally {
            if (!started) addWorkerFailed(w);
        }
        return started;
    }

    private void addWorkerFailed(Worker w) {
        synchronized (this) {
            if (w != null) workers.remove(w);
            workerCount--;
        }
        tryTerminate();
    }

    private void processWorkerExit(Worker w, boolean completedAbruptly) {
        synchronized (this) {
            if (completedAbruptly) workerCount--;
            completedTaskCount += w.completedTasks;
            workers.remove(w);
        }
        tryTerminate();
        boolean replace;
        synchronized (this) {
            replace = runState < STOP;
            if (replace && !completedAbruptly) {
                int min = allowCoreThreadTimeOut ? 0 : corePoolSize;
                if (min == 0 && !workQueue.isEmpty()) min = 1;
                if (workerCount >= min) replace = false;
            }
        }
        if (replace) addWorker(null, false);
    }

    private Runnable getTask() {
        boolean timedOut = false;
        for (;;) {
            boolean timed;
            synchronized (this) {
                if (runState >= SHUTDOWN && (runState >= STOP || workQueue.isEmpty())) {
                    workerCount--;
                    return null;
                }
                int wc = workerCount;
                timed = allowCoreThreadTimeOut || wc > corePoolSize;
                if ((wc > maximumPoolSize || (timed && timedOut)) && (wc > 1 || workQueue.isEmpty())) {
                    workerCount--;
                    return null;
                }
            }
            try {
                Runnable r = timed ? workQueue.poll(keepAliveTime, TimeUnit.NANOSECONDS) : workQueue.take();
                if (r != null) return r;
                timedOut = true;
            } catch (InterruptedException retry) {
                timedOut = false;
            }
        }
    }

    private void runWorker(Worker w) {
        Thread wt = Thread.currentThread();
        Runnable task = w.firstTask;
        w.firstTask = null;
        boolean completedAbruptly = true;
        try {
            while (task != null || (task = getTask()) != null) {
                boolean stopping;
                synchronized (this) {
                    w.running = true;
                    stopping = runState >= STOP;
                }
                // a stopping pool interrupts the task's thread; otherwise a leftover interrupt
                // (from an idle-worker interrupt) is cleared
                if (stopping) {
                    if (!wt.isInterrupted()) wt.interrupt();
                } else if (Thread.interrupted()) {
                    synchronized (this) {
                        stopping = runState >= STOP;
                    }
                    if (stopping) wt.interrupt();
                }
                try {
                    beforeExecute(wt, task);
                    try {
                        task.run();
                        afterExecute(task, null);
                    } catch (Throwable ex) {
                        afterExecute(task, ex);
                        throw ex;
                    }
                } finally {
                    task = null;
                    synchronized (this) {
                        w.completedTasks++;
                        w.running = false;
                    }
                }
            }
            completedAbruptly = false;
        } finally {
            processWorkerExit(w, completedAbruptly);
        }
    }

    private void interruptIdleWorkers(boolean onlyOne) {
        List<Thread> ts = new ArrayList<>();
        synchronized (this) {
            for (Worker w : workers) {
                if (!w.running && !w.thread.isInterrupted()) {
                    ts.add(w.thread);
                    if (onlyOne) break;
                }
            }
        }
        for (Thread t : ts) t.interrupt();
    }

    private void interruptWorkers() {
        List<Thread> ts = new ArrayList<>();
        synchronized (this) {
            for (Worker w : workers) ts.add(w.thread);
        }
        for (Thread t : ts) {
            if (!t.isInterrupted()) t.interrupt();
        }
    }

    final void tryTerminate() {
        synchronized (this) {
            if (runState == RUNNING || runState >= TIDYING || (runState == SHUTDOWN && !workQueue.isEmpty())) return;
            if (workerCount != 0) {
                interruptIdleWorkers(true);
                return;
            }
            runState = TIDYING;
        }
        try {
            terminated();
        } finally {
            synchronized (this) {
                runState = TERMINATED;
                notifyAll();
            }
        }
    }

    final void reject(Runnable command) {
        handler.rejectedExecution(command, this);
    }

    void onShutdown() {
    }

    final synchronized boolean isRunningState() {
        return runState == RUNNING;
    }

    final synchronized boolean isStopped() {
        return runState >= STOP;
    }

    final synchronized int workerCountNow() {
        return workerCount;
    }

    /** STPE: make sure a thread will run the delayed task (core thread, or one if core is 0). */
    void ensurePrestart() {
        int wc = workerCountNow();
        if (wc < corePoolSize) addWorker(null, true);
        else if (wc == 0) addWorker(null, false);
    }

    // ---- the Executor ----

    public void execute(Runnable command) {
        if (command == null) throw new NullPointerException();
        if (workerCountNow() < corePoolSize) {
            if (addWorker(command, true)) return;
        }
        if (isRunningState() && workQueue.offer(command)) {
            if (!isRunningState() && remove(command)) reject(command);
            else if (workerCountNow() == 0) addWorker(null, false);
        } else if (!addWorker(command, false)) {
            reject(command);
        }
    }

    public void shutdown() {
        synchronized (this) {
            if (runState < SHUTDOWN) runState = SHUTDOWN;
        }
        interruptIdleWorkers(false);
        onShutdown();
        tryTerminate();
    }

    public List<Runnable> shutdownNow() {
        synchronized (this) {
            if (runState < STOP) runState = STOP;
        }
        interruptWorkers();
        ArrayList<Runnable> taskList = new ArrayList<>();
        workQueue.drainTo(taskList);
        if (!workQueue.isEmpty()) {
            for (Object r : workQueue.toArray()) {
                if (workQueue.remove(r)) taskList.add((Runnable) r);
            }
        }
        tryTerminate();
        return taskList;
    }

    public synchronized boolean isShutdown() {
        return runState >= SHUTDOWN;
    }

    public synchronized boolean isTerminating() {
        return runState >= SHUTDOWN && runState < TERMINATED;
    }

    public synchronized boolean isTerminated() {
        return runState == TERMINATED;
    }

    public synchronized boolean awaitTermination(long timeout, TimeUnit unit) throws InterruptedException {
        long nanos = unit.toNanos(timeout);
        long deadline = System.nanoTime() + nanos;
        while (runState < TERMINATED) {
            if (nanos <= 0L) return false;
            wait(Math.max(1L, nanos / 1000000L));
            nanos = deadline - System.nanoTime();
        }
        return true;
    }

    // ---- configuration and statistics ----

    public void setThreadFactory(ThreadFactory threadFactory) {
        if (threadFactory == null) throw new NullPointerException();
        this.threadFactory = threadFactory;
    }

    public ThreadFactory getThreadFactory() {
        return threadFactory;
    }

    public void setRejectedExecutionHandler(RejectedExecutionHandler handler) {
        if (handler == null) throw new NullPointerException();
        this.handler = handler;
    }

    public RejectedExecutionHandler getRejectedExecutionHandler() {
        return handler;
    }

    public void setCorePoolSize(int corePoolSize) {
        if (corePoolSize < 0 || maximumPoolSize < corePoolSize) throw new IllegalArgumentException();
        int delta = corePoolSize - this.corePoolSize;
        this.corePoolSize = corePoolSize;
        if (workerCountNow() > corePoolSize) {
            interruptIdleWorkers(false);
        } else if (delta > 0) {
            int k = Math.min(delta, workQueue.size());
            while (k-- > 0 && addWorker(null, true)) {
                if (workQueue.isEmpty()) break;
            }
        }
    }

    public int getCorePoolSize() {
        return corePoolSize;
    }

    public boolean prestartCoreThread() {
        return workerCountNow() < corePoolSize && addWorker(null, true);
    }

    public int prestartAllCoreThreads() {
        int n = 0;
        while (addWorker(null, true)) ++n;
        return n;
    }

    public boolean allowsCoreThreadTimeOut() {
        return allowCoreThreadTimeOut;
    }

    public void allowCoreThreadTimeOut(boolean value) {
        if (value && keepAliveTime <= 0) throw new IllegalArgumentException("Core threads must have nonzero keep alive times");
        if (value != allowCoreThreadTimeOut) {
            allowCoreThreadTimeOut = value;
            if (value) interruptIdleWorkers(false);
        }
    }

    public void setMaximumPoolSize(int maximumPoolSize) {
        if (maximumPoolSize <= 0 || maximumPoolSize < corePoolSize) throw new IllegalArgumentException();
        this.maximumPoolSize = maximumPoolSize;
        if (workerCountNow() > maximumPoolSize) interruptIdleWorkers(false);
    }

    public int getMaximumPoolSize() {
        return maximumPoolSize;
    }

    public void setKeepAliveTime(long time, TimeUnit unit) {
        if (time < 0) throw new IllegalArgumentException();
        if (time == 0 && allowsCoreThreadTimeOut()) throw new IllegalArgumentException("Core threads must have nonzero keep alive times");
        long keepAliveTime = unit.toNanos(time);
        long delta = keepAliveTime - this.keepAliveTime;
        this.keepAliveTime = keepAliveTime;
        if (delta < 0) interruptIdleWorkers(false);
    }

    public long getKeepAliveTime(TimeUnit unit) {
        return unit.convert(keepAliveTime, TimeUnit.NANOSECONDS);
    }

    public BlockingQueue<Runnable> getQueue() {
        return workQueue;
    }

    public boolean remove(Runnable task) {
        boolean removed = workQueue.remove(task);
        tryTerminate();
        return removed;
    }

    public void purge() {
        for (Object r : workQueue.toArray()) {
            if (r instanceof Future<?> && ((Future<?>) r).isCancelled()) workQueue.remove(r);
        }
        tryTerminate();
    }

    public synchronized int getPoolSize() {
        return runState >= TIDYING ? 0 : workers.size();
    }

    public synchronized int getActiveCount() {
        int n = 0;
        for (Worker w : workers) if (w.running) ++n;
        return n;
    }

    public synchronized int getLargestPoolSize() {
        return largestPoolSize;
    }

    public synchronized long getTaskCount() {
        long n = completedTaskCount;
        for (Worker w : workers) {
            n += w.completedTasks;
            if (w.running) ++n;
        }
        return n + workQueue.size();
    }

    public synchronized long getCompletedTaskCount() {
        long n = completedTaskCount;
        for (Worker w : workers) n += w.completedTasks;
        return n;
    }

    public String toString() {
        long ncompleted;
        int nworkers, nactive, rs;
        synchronized (this) {
            ncompleted = completedTaskCount;
            nactive = 0;
            nworkers = workers.size();
            for (Worker w : workers) {
                ncompleted += w.completedTasks;
                if (w.running) ++nactive;
            }
            rs = runState;
        }
        String runStateName = (rs == RUNNING) ? "Running" : (rs >= TERMINATED) ? "Terminated" : "Shutting down";
        return super.toString() + "[" + runStateName + ", pool size = " + nworkers + ", active threads = " + nactive
            + ", queued tasks = " + workQueue.size() + ", completed tasks = " + ncompleted + "]";
    }

    protected void beforeExecute(Thread t, Runnable r) {
    }

    protected void afterExecute(Runnable r, Throwable t) {
    }

    protected void terminated() {
    }

    // ---- rejection policies ----

    public static class CallerRunsPolicy implements RejectedExecutionHandler {
        public CallerRunsPolicy() {
        }

        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
            if (!e.isShutdown()) r.run();
        }
    }

    public static class AbortPolicy implements RejectedExecutionHandler {
        public AbortPolicy() {
        }

        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
            throw new RejectedExecutionException(r, e);
        }
    }

    public static class DiscardPolicy implements RejectedExecutionHandler {
        public DiscardPolicy() {
        }

        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
        }
    }

    public static class DiscardOldestPolicy implements RejectedExecutionHandler {
        public DiscardOldestPolicy() {
        }

        public void rejectedExecution(Runnable r, ThreadPoolExecutor e) {
            if (!e.isShutdown()) {
                e.getQueue().poll();
                e.execute(r);
            }
        }
    }
}

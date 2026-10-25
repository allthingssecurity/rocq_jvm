/*
 * Clean-room model of java.util.concurrent.ScheduledThreadPoolExecutor (from the Javadoc), for
 * the thread layer. Tasks wait in a queue ordered by trigger time (System.nanoTime of the model
 * clock), ties in submission order; up to corePoolSize worker threads (at least one) are started
 * as tasks arrive and run the due tasks. Fixed-rate tasks are re-triggered at the previous
 * trigger plus the period, fixed-delay tasks at the end of the run plus the delay; an exception
 * stops a periodic task (its future then reports it). After shutdown(), delayed one-shot tasks
 * still run and periodic tasks are cancelled (the JDK's default policies). Rejection after
 * shutdown is STUCK. The class does not extend ThreadPoolExecutor here: methods inherited from
 * it in the JDK (getQueue, setCorePoolSize, ...) are STUCK.
 */
package java.util.concurrent;

import java.util.ArrayList;
import java.util.List;

public class ScheduledThreadPoolExecutor implements ScheduledExecutorService {
    private final int corePoolSize;
    private final ThreadFactory factory;
    private Task<?>[] queue = new Task<?>[8];
    private int size;
    private long sequencer;
    private int workers;
    private boolean shutdown;
    private final List<Thread> threads = new ArrayList<>();

    public ScheduledThreadPoolExecutor(int corePoolSize) {
        this(corePoolSize, null);
    }

    public ScheduledThreadPoolExecutor(int corePoolSize, ThreadFactory threadFactory) {
        if (corePoolSize < 0) throw new IllegalArgumentException();
        this.corePoolSize = corePoolSize;
        this.factory = threadFactory;
    }

    final class Task<V> implements ScheduledFuture<V>, Runnable {
        private final Callable<V> callable;
        long time;              // trigger, model nanoseconds
        final long period;      // 0 one-shot, > 0 fixed rate, < 0 fixed delay
        final long seq;
        private int state;      // 0 new/waiting, 1 running, 2 normal, 3 exceptional, 4 cancelled
        private Object outcome;
        private Thread runner;

        Task(Callable<V> c, long time, long period) {
            this.callable = c;
            this.time = time;
            this.period = period;
            this.seq = sequencer++;
        }

        public long getDelay(TimeUnit unit) {
            return unit.convert(time - System.nanoTime(), TimeUnit.NANOSECONDS);
        }

        public int compareTo(Delayed other) {
            if (other == this) return 0;
            if (other instanceof ScheduledThreadPoolExecutor.Task) {
                Task<?> x = (Task<?>) other;
                long diff = time - x.time;
                if (diff < 0) return -1;
                else if (diff > 0) return 1;
                else if (seq < x.seq) return -1;
                else return 1;
            }
            long diff = getDelay(TimeUnit.NANOSECONDS) - other.getDelay(TimeUnit.NANOSECONDS);
            return (diff < 0) ? -1 : (diff > 0) ? 1 : 0;
        }

        public boolean isPeriodic() {
            return period != 0;
        }

        public void run() {
            V r = null;
            Throwable ex = null;
            synchronized (this) {
                if (state != 0) return;
                state = 1;
                runner = Thread.currentThread();
            }
            try {
                r = callable.call();
            } catch (Throwable t) {
                ex = t;
            }
            boolean again = false;
            synchronized (this) {
                runner = null;
                if (state == 1) {
                    if (ex != null) {
                        outcome = ex;
                        state = 3;
                    } else if (period != 0) {
                        state = 0;
                        again = true;
                    } else {
                        outcome = r;
                        state = 2;
                    }
                }
                notifyAll();
            }
            if (again) {
                time = (period > 0) ? time + period : System.nanoTime() - period;
                reschedule(this);
            }
        }

        public boolean cancel(boolean mayInterruptIfRunning) {
            synchronized (this) {
                if (state >= 2) return false;
                if (state == 1 && mayInterruptIfRunning && runner != null) runner.interrupt();
                state = 4;
                notifyAll();
            }
            remove(this);
            return true;
        }

        public synchronized boolean isCancelled() {
            return state == 4;
        }

        public synchronized boolean isDone() {
            return state >= 2;
        }

        @SuppressWarnings("unchecked")
        private V report() throws ExecutionException {
            if (state == 2) return (V) outcome;
            if (state == 4) throw new CancellationException();
            throw new ExecutionException((Throwable) outcome);
        }

        public synchronized V get() throws InterruptedException, ExecutionException {
            while (state < 2) wait();
            return report();
        }

        public synchronized V get(long timeout, TimeUnit unit) throws InterruptedException, ExecutionException, TimeoutException {
            long nanos = unit.toNanos(timeout);
            long deadline = System.nanoTime() + nanos;
            while (state < 2) {
                if (nanos <= 0L) throw new TimeoutException();
                wait(Math.max(1L, nanos / 1000000L));
                nanos = deadline - System.nanoTime();
            }
            return report();
        }
    }

    private static long triggerTime(long delay, TimeUnit unit) {
        long d = unit.toNanos(delay < 0 ? 0 : delay);
        return System.nanoTime() + d;
    }

    private native void rejected0();

    private <V> Task<V> enqueue(Task<V> t) {
        boolean start = false;
        synchronized (this) {
            if (shutdown) rejected0();
            add(t);
            if (workers < Math.max(1, corePoolSize)) {
                workers++;
                start = true;
            }
            notifyAll();
        }
        if (start) {
            Runnable w = this::work;
            Thread th = (factory == null) ? new Thread(w) : factory.newThread(w);
            synchronized (this) {
                threads.add(th);
            }
            th.start();
        }
        return t;
    }

    private void add(Task<?> t) {
        if (size == queue.length) {
            Task<?>[] q = new Task<?>[size * 2];
            for (int i = 0; i < size; i++) q[i] = queue[i];
            queue = q;
        }
        queue[size++] = t;
    }

    private int first() {
        int best = 0;
        for (int i = 1; i < size; i++) {
            if (queue[i].compareTo(queue[best]) < 0) best = i;
        }
        return best;
    }

    private void removeAt(int i) {
        for (int j = i; j + 1 < size; j++) queue[j] = queue[j + 1];
        queue[--size] = null;
    }

    synchronized void remove(Task<?> t) {
        for (int i = 0; i < size; i++) {
            if (queue[i] == t) {
                removeAt(i);
                notifyAll();
                return;
            }
        }
    }

    void reschedule(Task<?> t) {
        synchronized (this) {
            if (shutdown) {
                t.cancel(false);   // periodic tasks stop at shutdown
                return;
            }
            add(t);
            notifyAll();
        }
    }

    private void work() {
        for (;;) {
            Task<?> task;
            synchronized (this) {
                for (;;) {
                    if (size == 0) {
                        if (shutdown) {
                            workers--;
                            notifyAll();
                            return;
                        }
                        try {
                            wait();
                        } catch (InterruptedException e) {
                            // shutdownNow: the loop re-checks
                        }
                        continue;
                    }
                    int i = first();
                    long delay = queue[i].time - System.nanoTime();
                    if (delay <= 0) {
                        task = queue[i];
                        removeAt(i);
                        break;
                    }
                    try {
                        wait(Math.max(1L, (delay + 999999L) / 1000000L));
                    } catch (InterruptedException e) {
                        // re-check
                    }
                }
            }
            task.run();
        }
    }

    public ScheduledFuture<?> schedule(Runnable command, long delay, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        return enqueue(new Task<Object>(Executors.callable(command, null), triggerTime(delay, unit), 0));
    }

    public <V> ScheduledFuture<V> schedule(Callable<V> callable, long delay, TimeUnit unit) {
        if (callable == null || unit == null) throw new NullPointerException();
        return enqueue(new Task<V>(callable, triggerTime(delay, unit), 0));
    }

    public ScheduledFuture<?> scheduleAtFixedRate(Runnable command, long initialDelay, long period, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        if (period <= 0L) throw new IllegalArgumentException();
        return enqueue(new Task<Object>(Executors.callable(command, null), triggerTime(initialDelay, unit), unit.toNanos(period)));
    }

    public ScheduledFuture<?> scheduleWithFixedDelay(Runnable command, long initialDelay, long delay, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        if (delay <= 0L) throw new IllegalArgumentException();
        return enqueue(new Task<Object>(Executors.callable(command, null), triggerTime(initialDelay, unit), -unit.toNanos(delay)));
    }

    public void execute(Runnable command) {
        schedule(command, 0, TimeUnit.NANOSECONDS);
    }

    public Future<?> submit(Runnable task) {
        return schedule(task, 0, TimeUnit.NANOSECONDS);
    }

    public <T> Future<T> submit(Runnable task, T result) {
        if (task == null) throw new NullPointerException();
        return schedule(Executors.callable(task, result), 0, TimeUnit.NANOSECONDS);
    }

    public <T> Future<T> submit(Callable<T> task) {
        return schedule(task, 0, TimeUnit.NANOSECONDS);
    }

    public void shutdown() {
        List<Task<?>> periodic = new ArrayList<>();
        synchronized (this) {
            shutdown = true;
            for (int i = size - 1; i >= 0; i--) {
                if (queue[i].isPeriodic()) {
                    periodic.add(queue[i]);
                    removeAt(i);
                }
            }
            notifyAll();
        }
        for (Task<?> t : periodic) t.cancel(false);
    }

    public List<Runnable> shutdownNow() {
        List<Runnable> rest = new ArrayList<>();
        List<Thread> ts;
        synchronized (this) {
            shutdown = true;
            Task<?>[] q = new Task<?>[size];
            for (int i = 0; i < size; i++) q[i] = queue[i];
            // in queue order (the JDK drains its heap; the order there is unspecified)
            for (Task<?> t : q) rest.add(t);
            size = 0;
            ts = new ArrayList<>(threads);
            notifyAll();
        }
        for (Thread t : ts) t.interrupt();
        return rest;
    }

    public synchronized boolean isShutdown() {
        return shutdown;
    }

    public synchronized boolean isTerminated() {
        return shutdown && workers == 0 && size == 0;
    }

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

    public int getCorePoolSize() {
        return corePoolSize;
    }
}

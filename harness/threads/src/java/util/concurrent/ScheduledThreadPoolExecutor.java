/*
 * Clean-room model of java.util.concurrent.ScheduledThreadPoolExecutor, for the thread layer,
 * from its Javadoc: a ThreadPoolExecutor with corePoolSize threads (the maximum is unused) whose
 * queue orders tasks by trigger time (System.nanoTime of the model clock), ties in submission
 * order. Fixed-rate tasks are re-triggered at the previous trigger plus the period, fixed-delay
 * tasks at the end of the run plus the delay; an exception stops a periodic task and its future
 * reports it. After shutdown(), delayed one-shot tasks still run and periodic tasks are
 * cancelled (the defaults of the two policies, which can be changed); cancelled tasks stay
 * queued until their time unless setRemoveOnCancelPolicy(true).
 */
package java.util.concurrent;

import java.util.List;

public class ScheduledThreadPoolExecutor extends ThreadPoolExecutor implements ScheduledExecutorService {
    private volatile boolean continueExistingPeriodicTasksAfterShutdown;
    private volatile boolean executeExistingDelayedTasksAfterShutdown = true;
    volatile boolean removeOnCancel;
    private static long sequencer;
    private static final long DEFAULT_KEEPALIVE_MILLIS = 10L;

    private class ScheduledFutureTask<V> extends FutureTask<V> implements RunnableScheduledFuture<V> {
        private final long sequenceNumber;
        private volatile long time;
        private final long period;
        RunnableScheduledFuture<V> outerTask = this;

        ScheduledFutureTask(Runnable r, V result, long triggerTime, long period) {
            super(r, result);
            this.time = triggerTime;
            this.period = period;
            this.sequenceNumber = nextSeq();
        }

        ScheduledFutureTask(Callable<V> callable, long triggerTime) {
            super(callable);
            this.time = triggerTime;
            this.period = 0;
            this.sequenceNumber = nextSeq();
        }

        public long getDelay(TimeUnit unit) {
            return unit.convert(time - System.nanoTime(), TimeUnit.NANOSECONDS);
        }

        public int compareTo(Delayed other) {
            if (other == this) return 0;
            if (other instanceof ScheduledThreadPoolExecutor.ScheduledFutureTask) {
                ScheduledFutureTask<?> x = (ScheduledFutureTask<?>) other;
                long diff = time - x.time;
                if (diff < 0) return -1;
                else if (diff > 0) return 1;
                else if (sequenceNumber < x.sequenceNumber) return -1;
                else return 1;
            }
            long diff = getDelay(TimeUnit.NANOSECONDS) - other.getDelay(TimeUnit.NANOSECONDS);
            return (diff < 0) ? -1 : (diff > 0) ? 1 : 0;
        }

        public boolean isPeriodic() {
            return period != 0;
        }

        private void setNextRunTime() {
            long p = period;
            if (p > 0) time += p;
            else time = triggerTime(-p);
        }

        public boolean cancel(boolean mayInterruptIfRunning) {
            boolean cancelled = super.cancel(mayInterruptIfRunning);
            if (cancelled && removeOnCancel) remove(this);
            return cancelled;
        }

        public void run() {
            if (!canRunInCurrentRunState(this)) {
                cancel(false);
            } else if (!isPeriodic()) {
                super.run();
            } else if (super.runAndReset()) {
                setNextRunTime();
                reExecutePeriodic(outerTask);
            }
        }
    }

    private static synchronized long nextSeq() {
        return sequencer++;
    }

    boolean canRunInCurrentRunState(RunnableScheduledFuture<?> task) {
        if (!isShutdown()) return true;
        if (isStopped()) return false;
        return task.isPeriodic() ? continueExistingPeriodicTasksAfterShutdown
            : (executeExistingDelayedTasksAfterShutdown || task.getDelay(TimeUnit.NANOSECONDS) <= 0);
    }

    private void delayedExecute(RunnableScheduledFuture<?> task) {
        if (isShutdown()) {
            reject(task);
        } else {
            super.getQueue().add(task);
            if (!canRunInCurrentRunState(task) && remove(task)) task.cancel(false);
            else ensurePrestart();
        }
    }

    void reExecutePeriodic(RunnableScheduledFuture<?> task) {
        if (canRunInCurrentRunState(task)) {
            super.getQueue().add(task);
            if (canRunInCurrentRunState(task) || !remove(task)) {
                ensurePrestart();
                return;
            }
        }
        task.cancel(false);
    }

    @Override
    void onShutdown() {
        BlockingQueue<Runnable> q = super.getQueue();
        boolean keepDelayed = getExecuteExistingDelayedTasksAfterShutdownPolicy();
        boolean keepPeriodic = getContinueExistingPeriodicTasksAfterShutdownPolicy();
        for (Object e : q.toArray()) {
            if (e instanceof RunnableScheduledFuture) {
                RunnableScheduledFuture<?> t = (RunnableScheduledFuture<?>) e;
                if ((t.isPeriodic() ? !keepPeriodic : (!keepDelayed && t.getDelay(TimeUnit.NANOSECONDS) > 0))
                    || t.isCancelled()) {
                    if (q.remove(t)) t.cancel(false);
                }
            }
        }
        tryTerminate();
    }

    protected <V> RunnableScheduledFuture<V> decorateTask(Runnable runnable, RunnableScheduledFuture<V> task) {
        return task;
    }

    protected <V> RunnableScheduledFuture<V> decorateTask(Callable<V> callable, RunnableScheduledFuture<V> task) {
        return task;
    }

    public ScheduledThreadPoolExecutor(int corePoolSize) {
        super(corePoolSize, Integer.MAX_VALUE, DEFAULT_KEEPALIVE_MILLIS, TimeUnit.MILLISECONDS, new DelayedWorkQueue());
    }

    public ScheduledThreadPoolExecutor(int corePoolSize, ThreadFactory threadFactory) {
        super(corePoolSize, Integer.MAX_VALUE, DEFAULT_KEEPALIVE_MILLIS, TimeUnit.MILLISECONDS, new DelayedWorkQueue(), threadFactory);
    }

    public ScheduledThreadPoolExecutor(int corePoolSize, RejectedExecutionHandler handler) {
        super(corePoolSize, Integer.MAX_VALUE, DEFAULT_KEEPALIVE_MILLIS, TimeUnit.MILLISECONDS, new DelayedWorkQueue(), handler);
    }

    public ScheduledThreadPoolExecutor(int corePoolSize, ThreadFactory threadFactory, RejectedExecutionHandler handler) {
        super(corePoolSize, Integer.MAX_VALUE, DEFAULT_KEEPALIVE_MILLIS, TimeUnit.MILLISECONDS, new DelayedWorkQueue(), threadFactory, handler);
    }

    private long triggerTime(long delay, TimeUnit unit) {
        return triggerTime(unit.toNanos((delay < 0) ? 0 : delay));
    }

    long triggerTime(long delay) {
        return System.nanoTime() + ((delay < (Long.MAX_VALUE >> 1)) ? delay : overflowFree(delay));
    }

    private long overflowFree(long delay) {
        Object head = super.getQueue().peek();
        if (head != null) {
            long headDelay = ((Delayed) head).getDelay(TimeUnit.NANOSECONDS);
            if (headDelay < 0 && (delay - headDelay < 0)) delay = Long.MAX_VALUE + headDelay;
        }
        return delay;
    }

    public ScheduledFuture<?> schedule(Runnable command, long delay, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        RunnableScheduledFuture<Void> t = decorateTask(command, new ScheduledFutureTask<Void>(command, null, triggerTime(delay, unit), 0));
        delayedExecute(t);
        return t;
    }

    public <V> ScheduledFuture<V> schedule(Callable<V> callable, long delay, TimeUnit unit) {
        if (callable == null || unit == null) throw new NullPointerException();
        RunnableScheduledFuture<V> t = decorateTask(callable, new ScheduledFutureTask<V>(callable, triggerTime(delay, unit)));
        delayedExecute(t);
        return t;
    }

    public ScheduledFuture<?> scheduleAtFixedRate(Runnable command, long initialDelay, long period, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        if (period <= 0L) throw new IllegalArgumentException();
        ScheduledFutureTask<Void> sft = new ScheduledFutureTask<Void>(command, null, triggerTime(initialDelay, unit), unit.toNanos(period));
        RunnableScheduledFuture<Void> t = decorateTask(command, sft);
        sft.outerTask = t;
        delayedExecute(t);
        return t;
    }

    public ScheduledFuture<?> scheduleWithFixedDelay(Runnable command, long initialDelay, long delay, TimeUnit unit) {
        if (command == null || unit == null) throw new NullPointerException();
        if (delay <= 0L) throw new IllegalArgumentException();
        ScheduledFutureTask<Void> sft = new ScheduledFutureTask<Void>(command, null, triggerTime(initialDelay, unit), -unit.toNanos(delay));
        RunnableScheduledFuture<Void> t = decorateTask(command, sft);
        sft.outerTask = t;
        delayedExecute(t);
        return t;
    }

    public void execute(Runnable command) {
        schedule(command, 0, TimeUnit.NANOSECONDS);
    }

    public Future<?> submit(Runnable task) {
        return schedule(task, 0, TimeUnit.NANOSECONDS);
    }

    public <T> Future<T> submit(Runnable task, T result) {
        return schedule(Executors.callable(task, result), 0, TimeUnit.NANOSECONDS);
    }

    public <T> Future<T> submit(Callable<T> task) {
        return schedule(task, 0, TimeUnit.NANOSECONDS);
    }

    public void setContinueExistingPeriodicTasksAfterShutdownPolicy(boolean value) {
        continueExistingPeriodicTasksAfterShutdown = value;
        if (!value && isShutdown()) onShutdown();
    }

    public boolean getContinueExistingPeriodicTasksAfterShutdownPolicy() {
        return continueExistingPeriodicTasksAfterShutdown;
    }

    public void setExecuteExistingDelayedTasksAfterShutdownPolicy(boolean value) {
        executeExistingDelayedTasksAfterShutdown = value;
        if (!value && isShutdown()) onShutdown();
    }

    public boolean getExecuteExistingDelayedTasksAfterShutdownPolicy() {
        return executeExistingDelayedTasksAfterShutdown;
    }

    public void setRemoveOnCancelPolicy(boolean value) {
        removeOnCancel = value;
    }

    public boolean getRemoveOnCancelPolicy() {
        return removeOnCancel;
    }

    public void shutdown() {
        super.shutdown();
    }

    public List<Runnable> shutdownNow() {
        return super.shutdownNow();
    }

    public BlockingQueue<Runnable> getQueue() {
        return super.getQueue();
    }

    /** The queue of delayed tasks: a binary heap by compareTo, take() waits for the head's time. */
    static class DelayedWorkQueue extends java.util.AbstractQueue<Runnable> implements BlockingQueue<Runnable> {
        private RunnableScheduledFuture<?>[] queue = new RunnableScheduledFuture<?>[16];
        private int size;

        private void siftUp(int k, RunnableScheduledFuture<?> key) {
            while (k > 0) {
                int parent = (k - 1) >>> 1;
                RunnableScheduledFuture<?> e = queue[parent];
                if (key.compareTo(e) >= 0) break;
                queue[k] = e;
                k = parent;
            }
            queue[k] = key;
        }

        private void siftDown(int k, RunnableScheduledFuture<?> key) {
            int half = size >>> 1;
            while (k < half) {
                int child = (k << 1) + 1;
                RunnableScheduledFuture<?> c = queue[child];
                int right = child + 1;
                if (right < size && c.compareTo(queue[right]) > 0) c = queue[child = right];
                if (key.compareTo(c) <= 0) break;
                queue[k] = c;
                k = child;
            }
            queue[k] = key;
        }

        private int indexOf(Object x) {
            for (int i = 0; i < size; i++) {
                if (x.equals(queue[i])) return i;
            }
            return -1;
        }

        private RunnableScheduledFuture<?> finishPoll() {
            RunnableScheduledFuture<?> f = queue[0];
            int s = --size;
            RunnableScheduledFuture<?> x = queue[s];
            queue[s] = null;
            if (s != 0) siftDown(0, x);
            notifyAll();
            return f;
        }

        public synchronized boolean contains(Object x) {
            return x != null && indexOf(x) != -1;
        }

        public synchronized boolean remove(Object x) {
            if (x == null) return false;
            int i = indexOf(x);
            if (i < 0) return false;
            int s = --size;
            RunnableScheduledFuture<?> replacement = queue[s];
            queue[s] = null;
            if (s != i) {
                siftDown(i, replacement);
                if (queue[i] == replacement) siftUp(i, replacement);
            }
            notifyAll();
            return true;
        }

        public synchronized int size() {
            return size;
        }

        public synchronized boolean isEmpty() {
            return size == 0;
        }

        public int remainingCapacity() {
            return Integer.MAX_VALUE;
        }

        public synchronized RunnableScheduledFuture<?> peek() {
            return queue[0];
        }

        public synchronized boolean offer(Runnable x) {
            if (x == null) throw new NullPointerException();
            RunnableScheduledFuture<?> e = (RunnableScheduledFuture<?>) x;
            if (size >= queue.length) {
                RunnableScheduledFuture<?>[] n = new RunnableScheduledFuture<?>[queue.length * 2];
                for (int i = 0; i < size; i++) n[i] = queue[i];
                queue = n;
            }
            siftUp(size++, e);
            notifyAll();
            return true;
        }

        public void put(Runnable e) {
            offer(e);
        }

        public boolean add(Runnable e) {
            return offer(e);
        }

        public boolean offer(Runnable e, long timeout, TimeUnit unit) {
            return offer(e);
        }

        public synchronized RunnableScheduledFuture<?> poll() {
            RunnableScheduledFuture<?> first = queue[0];
            return (first == null || first.getDelay(TimeUnit.NANOSECONDS) > 0) ? null : finishPoll();
        }

        public synchronized RunnableScheduledFuture<?> take() throws InterruptedException {
            if (Thread.interrupted()) throw new InterruptedException();
            for (;;) {
                RunnableScheduledFuture<?> first = queue[0];
                if (first == null) {
                    wait();
                } else {
                    long delay = first.getDelay(TimeUnit.NANOSECONDS);
                    if (delay <= 0L) return finishPoll();
                    wait(Math.max(1L, (delay + 999999L) / 1000000L));
                }
            }
        }

        public synchronized RunnableScheduledFuture<?> poll(long timeout, TimeUnit unit) throws InterruptedException {
            long nanos = unit.toNanos(timeout);
            if (Thread.interrupted()) throw new InterruptedException();
            long deadline = System.nanoTime() + nanos;
            for (;;) {
                RunnableScheduledFuture<?> first = queue[0];
                if (first == null) {
                    if (nanos <= 0L) return null;
                    wait(Math.max(1L, nanos / 1000000L));
                } else {
                    long delay = first.getDelay(TimeUnit.NANOSECONDS);
                    if (delay <= 0L) return finishPoll();
                    if (nanos <= 0L) return null;
                    wait(Math.max(1L, (Math.min(delay, nanos) + 999999L) / 1000000L));
                }
                nanos = deadline - System.nanoTime();
            }
        }

        public synchronized void clear() {
            for (int i = 0; i < size; i++) queue[i] = null;
            size = 0;
        }

        public synchronized int drainTo(java.util.Collection<? super Runnable> c) {
            return drainTo(c, Integer.MAX_VALUE);
        }

        public synchronized int drainTo(java.util.Collection<? super Runnable> c, int maxElements) {
            if (c == null) throw new NullPointerException();
            if (c == this) throw new IllegalArgumentException();
            int n = 0;
            for (RunnableScheduledFuture<?> first; n < maxElements && (first = queue[0]) != null
                    && first.getDelay(TimeUnit.NANOSECONDS) <= 0; ) {
                c.add(first);
                finishPoll();
                ++n;
            }
            return n;
        }

        public synchronized Object[] toArray() {
            Object[] r = new Object[size];
            for (int i = 0; i < size; i++) r[i] = queue[i];
            return r;
        }

        public java.util.Iterator<Runnable> iterator() {
            final Object[] snap = toArray();
            return new java.util.Iterator<Runnable>() {
                int i;
                Object last;

                public boolean hasNext() {
                    return i < snap.length;
                }

                public Runnable next() {
                    if (i >= snap.length) throw new java.util.NoSuchElementException();
                    last = snap[i++];
                    return (Runnable) last;
                }

                public void remove() {
                    if (last == null) throw new IllegalStateException();
                    DelayedWorkQueue.this.remove(last);
                    last = null;
                }
            };
        }
    }
}

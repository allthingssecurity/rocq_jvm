/*
 * Clean-room model of java.util.Timer (from the Javadoc), for the thread layer: one background
 * thread runs the tasks in order of their execution time (ties in scheduling order), waiting
 * on the model clock (System.currentTimeMillis) in between. A task that throws kills the timer
 * thread; the timer is then cancelled and later schedule calls throw IllegalStateException.
 * Thread names and daemon status are not observable in the model.
 */
package java.util;

public class Timer {
    private TimerTask[] queue = new TimerTask[8];
    private long[] seq = new long[8];
    private int size;
    private long nextSeq;
    private boolean newTasksMayBeScheduled = true;
    private boolean threadStarted;

    public Timer() {
        start();
    }

    public Timer(boolean isDaemon) {
        start();
    }

    public Timer(String name) {
        if (name == null) throw new NullPointerException();
        start();
    }

    public Timer(String name, boolean isDaemon) {
        if (name == null) throw new NullPointerException();
        start();
    }

    private void start() {
        Thread t = new Thread(this::mainLoop);
        t.start();
    }

    public void schedule(TimerTask task, long delay) {
        if (delay < 0) throw new IllegalArgumentException("Negative delay.");
        sched(task, System.currentTimeMillis() + delay, 0);
    }

    public void schedule(TimerTask task, Date time) {
        throw ModelStuckTimer.unsupported("Timer.schedule(TimerTask, Date)");
    }

    public void schedule(TimerTask task, long delay, long period) {
        if (delay < 0) throw new IllegalArgumentException("Negative delay.");
        if (period <= 0) throw new IllegalArgumentException("Non-positive period.");
        sched(task, System.currentTimeMillis() + delay, -period);
    }

    public void scheduleAtFixedRate(TimerTask task, long delay, long period) {
        if (delay < 0) throw new IllegalArgumentException("Negative delay.");
        if (period <= 0) throw new IllegalArgumentException("Non-positive period.");
        sched(task, System.currentTimeMillis() + delay, period);
    }

    private void sched(TimerTask task, long time, long period) {
        if (time < 0) throw new IllegalArgumentException("Illegal execution time.");
        // as the JDK: keep the period from overflowing
        if (Math.abs(period) > (Long.MAX_VALUE >> 1)) period >>= 1;
        synchronized (this) {
            if (!newTasksMayBeScheduled) throw new IllegalStateException("Timer already cancelled.");
            synchronized (task.lock) {
                if (task.state != TimerTask.VIRGIN) throw new IllegalStateException("Task already scheduled or cancelled");
                task.nextExecutionTime = time;
                task.period = period;
                task.state = TimerTask.SCHEDULED;
            }
            add(task);
            notifyAll();
        }
    }

    private void add(TimerTask t) {
        if (size == queue.length) {
            TimerTask[] q = new TimerTask[size * 2];
            long[] s = new long[size * 2];
            for (int i = 0; i < size; i++) { q[i] = queue[i]; s[i] = seq[i]; }
            queue = q;
            seq = s;
        }
        queue[size] = t;
        seq[size] = nextSeq++;
        size++;
    }

    /** Index of the task to run next: earliest time, then earliest scheduled. */
    private int min() {
        int best = 0;
        for (int i = 1; i < size; i++) {
            long a = queue[i].nextExecutionTime, b = queue[best].nextExecutionTime;
            if (a < b || (a == b && seq[i] < seq[best])) best = i;
        }
        return best;
    }

    private void removeAt(int i) {
        for (int j = i; j + 1 < size; j++) { queue[j] = queue[j + 1]; seq[j] = seq[j + 1]; }
        size--;
        queue[size] = null;
    }

    public void cancel() {
        synchronized (this) {
            newTasksMayBeScheduled = false;
            for (int i = 0; i < size; i++) queue[i] = null;
            size = 0;
            notifyAll();
        }
    }

    public int purge() {
        int result = 0;
        synchronized (this) {
            for (int i = size - 1; i >= 0; i--) {
                if (queue[i].state == TimerTask.CANCELLED) {
                    removeAt(i);
                    result++;
                }
            }
        }
        return result;
    }

    private void mainLoop() {
        try {
            for (;;) {
                TimerTask task;
                boolean fire;
                synchronized (this) {
                    while (size == 0 && newTasksMayBeScheduled) wait();
                    if (size == 0) break;   // cancelled and empty
                    int i = min();
                    task = queue[i];
                    long now, when;
                    synchronized (task.lock) {
                        if (task.state == TimerTask.CANCELLED) {
                            removeAt(i);
                            continue;
                        }
                        now = System.currentTimeMillis();
                        when = task.nextExecutionTime;
                        fire = when <= now;
                        if (fire) {
                            if (task.period == 0) {
                                removeAt(i);
                                task.state = TimerTask.EXECUTED;
                            } else {
                                task.nextExecutionTime = task.period < 0 ? now - task.period : when + task.period;
                            }
                        }
                    }
                    if (!fire) wait(when - now);
                }
                if (fire) task.run();
            }
        } catch (InterruptedException e) {
            // ignored, as the JDK's timer thread
        } finally {
            synchronized (this) {
                newTasksMayBeScheduled = false;
                for (int i = 0; i < size; i++) queue[i] = null;
                size = 0;
            }
        }
    }
}

final class ModelStuckTimer {
    private ModelStuckTimer() {
    }

    static native RuntimeException unsupported(String what);
}

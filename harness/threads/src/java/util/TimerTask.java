/*
 * Clean-room model of java.util.TimerTask (from the Javadoc), for the thread layer.
 */
package java.util;

public abstract class TimerTask implements Runnable {
    final Object lock = new Object();
    static final int VIRGIN = 0, SCHEDULED = 1, EXECUTED = 2, CANCELLED = 3;
    int state = VIRGIN;
    /** Next execution time (milliseconds of the model clock). */
    long nextExecutionTime;
    /** 0: one-shot; > 0: fixed rate; < 0: fixed delay (as -period). */
    long period;

    protected TimerTask() {
    }

    public abstract void run();

    public boolean cancel() {
        synchronized (lock) {
            boolean result = (state == SCHEDULED);
            state = CANCELLED;
            return result;
        }
    }

    public long scheduledExecutionTime() {
        synchronized (lock) {
            return (period < 0 ? nextExecutionTime + period : nextExecutionTime - period);
        }
    }
}

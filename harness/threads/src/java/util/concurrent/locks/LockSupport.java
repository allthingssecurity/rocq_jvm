/*
 * rocq-jvm model of java.util.concurrent.locks.LockSupport (clean-room, Apache-2.0), for the
 * thread layer, over monitors (no new thread natives): each thread has a binary permit and a
 * monitor in a table of this class. park consumes the permit or waits on the thread's monitor
 * until unpark, an interrupt (the interrupt status stays set: the InterruptedException of the
 * wait is caught and the status re-asserted) or the timeout (parkNanos: nanoTime; parkUntil: an
 * absolute currentTimeMillis deadline; both use the model clock, at millisecond resolution).
 * park returns at once when the permit is available or the thread is interrupted. Spurious
 * returns, which the JDK allows, do not happen here (a subset of the JDK's behaviours).
 * Blockers: park(blocker) records the blocker for getBlocker while the thread is parked;
 * setCurrentBlocker as the JDK.
 */
package java.util.concurrent.locks;

import java.util.ArrayList;

public class LockSupport {
    private LockSupport() { }

    /** A thread's permit and blocker; its monitor is the one the thread parks on. */
    private static final class Entry {
        final Thread thread;
        boolean permit;
        volatile Object blocker;
        Entry(Thread thread) { this.thread = thread; }
    }

    private static final ArrayList<Entry> entries = new ArrayList<>();

    private static Entry entry(Thread t) {
        synchronized (entries) {
            for (int i = 0; i < entries.size(); i++) {
                Entry e = entries.get(i);
                if (e.thread == t) return e;
            }
            Entry e = new Entry(t);
            entries.add(e);
            return e;
        }
    }

    private static void setBlocker(Thread t, Object arg) {
        entry(t).blocker = arg;
    }

    public static void setCurrentBlocker(Object blocker) {
        entry(Thread.currentThread()).blocker = blocker;
    }

    public static void unpark(Thread thread) {
        if (thread != null) {
            Entry e = entry(thread);
            synchronized (e) {
                e.permit = true;
                e.notifyAll();
            }
        }
    }

    /** mode 0: untimed; 1: relative nanos; 2: absolute millis. */
    private static void park0(int mode, long time) {
        Thread me = Thread.currentThread();
        Entry e = entry(me);
        synchronized (e) {
            if (e.permit) {
                e.permit = false;
                return;
            }
            if (me.isInterrupted()) return;
            long ms;
            if (mode == 0) {
                ms = 0L;
            } else if (mode == 1) {
                ms = Math.max(1L, time / 1000000L);
            } else {
                long now = System.currentTimeMillis();
                if (time <= now) return;
                ms = time - now;
            }
            try {
                if (mode == 0) e.wait();
                else e.wait(ms);
            } catch (InterruptedException ie) {
                me.interrupt();
            }
            e.permit = false;
        }
    }

    public static void park(Object blocker) {
        Thread t = Thread.currentThread();
        setBlocker(t, blocker);
        try {
            park0(0, 0L);
        } finally {
            setBlocker(t, null);
        }
    }

    public static void parkNanos(Object blocker, long nanos) {
        if (nanos > 0) {
            Thread t = Thread.currentThread();
            setBlocker(t, blocker);
            try {
                park0(1, nanos);
            } finally {
                setBlocker(t, null);
            }
        }
    }

    public static void parkUntil(Object blocker, long deadline) {
        Thread t = Thread.currentThread();
        setBlocker(t, blocker);
        try {
            park0(2, deadline);
        } finally {
            setBlocker(t, null);
        }
    }

    public static Object getBlocker(Thread t) {
        if (t == null) throw new NullPointerException();
        return entry(t).blocker;
    }

    public static void park() {
        park0(0, 0L);
    }

    public static void parkNanos(long nanos) {
        if (nanos > 0) park0(1, nanos);
    }

    public static void parkUntil(long deadline) {
        park0(2, deadline);
    }
}

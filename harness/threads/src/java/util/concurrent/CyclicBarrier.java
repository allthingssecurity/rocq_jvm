/*
 * rocq-jvm model of java.util.concurrent.CyclicBarrier (clean-room, Apache-2.0), for the thread
 * layer, over a private monitor. As the JDK: each trip starts a new generation; the last arriving
 * thread runs the barrier action (holding the barrier's lock) and gets index 0, the others get
 * their arrival index (parties - 1 for the first). A party that is interrupted while waiting, or
 * whose timed await times out, or a barrier action that throws, breaks the barrier: the other
 * waiters get BrokenBarrierException, the interrupted one InterruptedException, the timed-out one
 * TimeoutException. An interrupt after the trip is re-asserted instead. reset() breaks the
 * current generation and starts a new one. Timed awaits use the model clock.
 */
package java.util.concurrent;

public class CyclicBarrier {
    private static class Generation {
        Generation() { }
        boolean broken;
    }

    private final Object lock = new Object();
    private final int parties;
    private final Runnable barrierCommand;
    private Generation generation = new Generation();
    private int count;

    private void nextGeneration() {
        lock.notifyAll();
        count = parties;
        generation = new Generation();
    }

    private void breakBarrier() {
        generation.broken = true;
        count = parties;
        lock.notifyAll();
    }

    private int dowait(boolean timed, long nanos) throws InterruptedException, BrokenBarrierException, TimeoutException {
        synchronized (lock) {
            final Generation g = generation;
            if (g.broken) throw new BrokenBarrierException();
            if (Thread.interrupted()) {
                breakBarrier();
                throw new InterruptedException();
            }
            int index = --count;
            if (index == 0) {
                Runnable command = barrierCommand;
                if (command != null) {
                    try {
                        command.run();
                    } catch (Throwable ex) {
                        breakBarrier();
                        throw ex;
                    }
                }
                nextGeneration();
                return 0;
            }
            long deadline = timed ? System.nanoTime() + nanos : 0L;
            for (;;) {
                try {
                    if (!timed) {
                        lock.wait();
                    } else if (nanos > 0L) {
                        lock.wait(Math.max(1L, nanos / 1000000L));
                        nanos = deadline - System.nanoTime();
                    }
                } catch (InterruptedException ie) {
                    if (g == generation && !g.broken) {
                        breakBarrier();
                        throw ie;
                    } else {
                        Thread.currentThread().interrupt();
                    }
                }
                if (g.broken) throw new BrokenBarrierException();
                if (g != generation) return index;
                if (timed && nanos <= 0L) {
                    breakBarrier();
                    throw new TimeoutException();
                }
            }
        }
    }

    public CyclicBarrier(int parties, Runnable barrierAction) {
        if (parties <= 0) throw new IllegalArgumentException();
        this.parties = parties;
        this.count = parties;
        this.barrierCommand = barrierAction;
    }

    public CyclicBarrier(int parties) {
        this(parties, null);
    }

    public int getParties() {
        return parties;
    }

    public int await() throws InterruptedException, BrokenBarrierException {
        try {
            return dowait(false, 0L);
        } catch (TimeoutException toe) {
            throw new Error(toe);
        }
    }

    public int await(long timeout, TimeUnit unit) throws InterruptedException, BrokenBarrierException, TimeoutException {
        if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
        return dowait(true, unit.toNanos(timeout));
    }

    public boolean isBroken() {
        synchronized (lock) {
            return generation.broken;
        }
    }

    public void reset() {
        synchronized (lock) {
            breakBarrier();
            nextGeneration();
        }
    }

    public int getNumberWaiting() {
        synchronized (lock) {
            return parties - count;
        }
    }
}

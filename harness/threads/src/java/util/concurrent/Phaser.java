/*
 * rocq-jvm model of java.util.concurrent.Phaser (clean-room, Apache-2.0), for the thread layer.
 *
 * The state word of every phaser is the JDK's (phase in the high 32 bits with the termination
 * bit as the sign, registered parties in bits 16-31, unarrived parties in bits 0-15, the value 1
 * for "no parties"), and so are its transitions: arrival, registration, the root's advance (it
 * calls onAdvance, which may terminate the tree), the propagation of a sub-phaser's last arrival
 * (or last deregistration) to its parent, and the lazy reconciliation of a sub-phaser's phase
 * with the root's. Atomicity: each compare-and-set of the JDK is a region synchronized on one
 * monitor shared by the whole tree (the root's); onAdvance runs outside it, as in the JDK, where
 * other threads see the phase's last arrival before the advance. Waiting threads wait on that
 * monitor for the root's phase to change: arriveAndAwaitAdvance / awaitAdvance remember an
 * interrupt and re-assert it; awaitAdvanceInterruptibly throws InterruptedException (unless the
 * phase advanced first) and its timed form TimeoutException (model clock).
 *
 * Messages: the IllegalStateExceptions of an unregistered arrival and of too many parties, and
 * toString, contain Object.toString of the phaser (identity hash: STUCK in the machine).
 */
package java.util.concurrent;

public class Phaser {
    private long state;

    private static final int MAX_PARTIES = 0xffff;
    private static final int MAX_PHASE = Integer.MAX_VALUE;
    private static final int PARTIES_SHIFT = 16;
    private static final int PHASE_SHIFT = 32;
    private static final int UNARRIVED_MASK = 0xffff;
    private static final long PARTIES_MASK = 0xffff0000L;
    private static final long COUNTS_MASK = 0xffffffffL;
    private static final long TERMINATION_BIT = 1L << 63;
    private static final int ONE_ARRIVAL = 1;
    private static final int ONE_PARTY = 1 << PARTIES_SHIFT;
    private static final int ONE_DEREGISTER = ONE_ARRIVAL | ONE_PARTY;
    private static final int EMPTY = 1;

    private static int unarrivedOf(long s) {
        int counts = (int) s;
        return (counts == EMPTY) ? 0 : (counts & UNARRIVED_MASK);
    }

    private static int partiesOf(long s) {
        return (int) s >>> PARTIES_SHIFT;
    }

    private static int phaseOf(long s) {
        return (int) (s >>> PHASE_SHIFT);
    }

    private static int arrivedOf(long s) {
        int counts = (int) s;
        return (counts == EMPTY) ? 0 : (counts >>> PARTIES_SHIFT) - (counts & UNARRIVED_MASK);
    }

    private final Phaser parent;
    private final Phaser root;
    /** The monitor of the whole tree (created by the root). */
    private final Object lock;

    private String badArrive(long s) {
        return "Attempted arrival of unregistered party for " + stateToString(s);
    }

    private String badRegister(long s) {
        return "Attempt to register more than " + MAX_PARTIES + " parties for " + stateToString(s);
    }

    /** The root's next state after the last arrival of a phase (s: the state after it). */
    private long advanceState(int phase, long s, boolean terminate) {
        long n = s & PARTIES_MASK;
        int nextUnarrived = (int) n >>> PARTIES_SHIFT;
        if (terminate) n |= TERMINATION_BIT;
        else if (nextUnarrived == 0) n |= EMPTY;
        else n |= nextUnarrived;
        int nextPhase = (phase + 1) & MAX_PHASE;
        n |= (long) nextPhase << PHASE_SHIFT;
        return n;
    }

    private int doArrive(int adjust) {
        final Phaser root = this.root;
        long s;
        int phase;
        synchronized (lock) {
            s = (root == this) ? state : reconcileState();
            phase = (int) (s >>> PHASE_SHIFT);
            if (phase < 0) return phase;
            int counts = (int) s;
            int unarrived = (counts == EMPTY) ? 0 : (counts & UNARRIVED_MASK);
            if (unarrived <= 0) throw new IllegalStateException(badArrive(s));
            state = s -= adjust;
            if (unarrived != 1) return phase;
        }
        int nextUnarrived = (int) (s & PARTIES_MASK) >>> PARTIES_SHIFT;
        if (root == this) {
            boolean terminate = onAdvance(phase, nextUnarrived);
            synchronized (lock) {
                if (state == s) state = advanceState(phase, s, terminate);
                lock.notifyAll();
            }
        } else if (nextUnarrived == 0) {
            phase = parent.doArrive(ONE_DEREGISTER);
            synchronized (lock) {
                if (state == s) state = s | EMPTY;
            }
        } else {
            phase = parent.doArrive(ONE_ARRIVAL);
        }
        return phase;
    }

    private int doRegister(int registrations) {
        long adjust = ((long) registrations << PARTIES_SHIFT) | registrations;
        final Phaser parent = this.parent;
        int phase;
        for (;;) {
            long s;
            synchronized (lock) {
                s = (parent == null) ? state : reconcileState();
                int counts = (int) s;
                int parties = counts >>> PARTIES_SHIFT;
                int unarrived = counts & UNARRIVED_MASK;
                if (registrations > MAX_PARTIES - parties) throw new IllegalStateException(badRegister(s));
                phase = (int) (s >>> PHASE_SHIFT);
                if (phase < 0) break;
                if (counts != EMPTY) {
                    if (unarrived == 0) {
                        root.internalAwaitAdvance(phase, 0, 0L);   // wait out the advance
                        continue;
                    }
                    state = s + adjust;
                    break;
                } else if (parent == null) {
                    state = ((long) phase << PHASE_SHIFT) | adjust;
                    break;
                }
            }
            // first registration of a sub-phaser: register it with its parent (not holding the
            // tree's monitor, which the parent's own first registration takes after its phaser's)
            synchronized (this) {
                boolean same;
                synchronized (lock) {
                    same = state == s;
                }
                if (same) {
                    phase = parent.doRegister(1);
                    if (phase < 0) break;
                    synchronized (lock) {
                        if (state != s) phase = (int) (root.state >>> PHASE_SHIFT);
                        state = ((long) phase << PHASE_SHIFT) | adjust;
                    }
                    break;
                }
            }
        }
        return phase;
    }

    /** A sub-phaser's state with the root's phase (lock held). */
    private long reconcileState() {
        final Phaser root = this.root;
        long s = state;
        if (root != this) {
            int phase, p;
            if ((phase = (int) (root.state >>> PHASE_SHIFT)) != (int) (s >>> PHASE_SHIFT)) {
                s = (((long) phase << PHASE_SHIFT)
                     | ((phase < 0) ? (s & COUNTS_MASK)
                        : (((p = (int) s >>> PARTIES_SHIFT) == 0) ? EMPTY : ((s & PARTIES_MASK) | p))));
                state = s;
            }
        }
        return s;
    }

    public Phaser() {
        this(null, 0);
    }

    public Phaser(int parties) {
        this(null, parties);
    }

    public Phaser(Phaser parent) {
        this(parent, 0);
    }

    public Phaser(Phaser parent, int parties) {
        if (parties >>> PARTIES_SHIFT != 0) throw new IllegalArgumentException("Illegal number of parties");
        int phase = 0;
        this.parent = parent;
        if (parent != null) {
            final Phaser root = parent.root;
            this.root = root;
            this.lock = root.lock;
            if (parties != 0) phase = parent.doRegister(1);
        } else {
            this.root = this;
            this.lock = new Object();
        }
        long st = (parties == 0) ? (long) EMPTY
            : ((long) phase << PHASE_SHIFT) | ((long) parties << PARTIES_SHIFT) | ((long) parties);
        synchronized (lock) {
            this.state = st;
        }
    }

    public int register() {
        return doRegister(1);
    }

    public int bulkRegister(int parties) {
        if (parties < 0) throw new IllegalArgumentException();
        if (parties == 0) return getPhase();
        return doRegister(parties);
    }

    public int arrive() {
        return doArrive(ONE_ARRIVAL);
    }

    public int arriveAndDeregister() {
        return doArrive(ONE_DEREGISTER);
    }

    public int arriveAndAwaitAdvance() {
        final Phaser root = this.root;
        long s;
        int phase;
        synchronized (lock) {
            s = (root == this) ? state : reconcileState();
            phase = (int) (s >>> PHASE_SHIFT);
            if (phase < 0) return phase;
            int counts = (int) s;
            int unarrived = (counts == EMPTY) ? 0 : (counts & UNARRIVED_MASK);
            if (unarrived <= 0) throw new IllegalStateException(badArrive(s));
            state = s -= ONE_ARRIVAL;
            if (unarrived > 1) return root.internalAwaitAdvance(phase, 0, 0L);
        }
        if (root != this) return parent.arriveAndAwaitAdvance();
        int nextUnarrived = (int) (s & PARTIES_MASK) >>> PARTIES_SHIFT;
        boolean terminate = onAdvance(phase, nextUnarrived);
        synchronized (lock) {
            long n = advanceState(phase, s, terminate);
            if (state != s) return (int) (state >>> PHASE_SHIFT);   // terminated
            state = n;
            lock.notifyAll();
            return (int) (n >>> PHASE_SHIFT) & MAX_PHASE;
        }
    }

    public int awaitAdvance(int phase) {
        final Phaser root = this.root;
        synchronized (lock) {
            long s = (root == this) ? state : reconcileState();
            int p = (int) (s >>> PHASE_SHIFT);
            if (phase < 0) return phase;
            if (p == phase) return root.internalAwaitAdvance(phase, 0, 0L);
            return p;
        }
    }

    public int awaitAdvanceInterruptibly(int phase) throws InterruptedException {
        final Phaser root = this.root;
        synchronized (lock) {
            long s = (root == this) ? state : reconcileState();
            int p = (int) (s >>> PHASE_SHIFT);
            if (phase < 0) return phase;
            if (p == phase) {
                long r = root.awaitAdvance0(phase, 1, 0L);
                if (r == INTERRUPTED) throw new InterruptedException();
                p = (int) r;
            }
            return p;
        }
    }

    public int awaitAdvanceInterruptibly(int phase, long timeout, TimeUnit unit) throws InterruptedException, TimeoutException {
        if (unit == null) throw new NullPointerException("Cannot invoke \"java.util.concurrent.TimeUnit.toNanos(long)\" because \"unit\" is null");
        long nanos = unit.toNanos(timeout);
        final Phaser root = this.root;
        synchronized (lock) {
            long s = (root == this) ? state : reconcileState();
            int p = (int) (s >>> PHASE_SHIFT);
            if (phase < 0) return phase;
            if (p == phase) {
                long r = root.awaitAdvance0(phase, 2, nanos);
                if (r == INTERRUPTED) throw new InterruptedException();
                p = (int) r;
                if (p == phase) throw new TimeoutException();
            }
            return p;
        }
    }

    public void forceTermination() {
        final Phaser root = this.root;
        synchronized (lock) {
            long s = root.state;
            if (s >= 0) {
                root.state = s | TERMINATION_BIT;
                lock.notifyAll();
            }
        }
    }

    public final int getPhase() {
        synchronized (lock) {
            return (int) (root.state >>> PHASE_SHIFT);
        }
    }

    public int getRegisteredParties() {
        synchronized (lock) {
            return partiesOf(state);
        }
    }

    public int getArrivedParties() {
        synchronized (lock) {
            return arrivedOf(reconcileState());
        }
    }

    public int getUnarrivedParties() {
        synchronized (lock) {
            return unarrivedOf(reconcileState());
        }
    }

    public Phaser getParent() {
        return parent;
    }

    public Phaser getRoot() {
        return root;
    }

    public boolean isTerminated() {
        synchronized (lock) {
            return root.state < 0L;
        }
    }

    protected boolean onAdvance(int phase, int registeredParties) {
        return registeredParties == 0;
    }

    public String toString() {
        long s;
        synchronized (lock) {
            s = reconcileState();
        }
        return stateToString(s);
    }

    private String stateToString(long s) {
        return super.toString() + "[phase = " + phaseOf(s) + " parties = " + partiesOf(s) + " arrived = " + arrivedOf(s) + "]";
    }

    /**
     * Waits (lock held; this is the root) until the phase is no longer the given one. mode 0:
     * not interruptible (an interrupt is re-asserted at the end); 1: interruptible; 2:
     * interruptible and timed. Returns the new phase, the phase itself on a timeout, or
     * INTERRUPTED (the phase had not advanced; the interrupt status is cleared).
     */
    private int internalAwaitAdvance(int phase, int mode, long nanos) {
        return (int) awaitAdvance0(phase, mode, nanos);
    }

    /** Not a phase: awaitAdvance0's result for an interrupted interruptible wait. */
    private static final long INTERRUPTED = Long.MIN_VALUE;

    private long awaitAdvance0(int phase, int mode, long nanos) {
        boolean interrupted = false;
        long deadline = (mode == 2) ? System.nanoTime() + nanos : 0L;
        int p;
        while ((p = (int) (state >>> PHASE_SHIFT)) == phase) {
            if (interrupted && mode != 0) return INTERRUPTED;
            try {
                if (mode == 2) {
                    if (nanos <= 0L || (nanos = deadline - System.nanoTime()) <= 0L) return p;
                    lock.wait(Math.max(1L, nanos / 1000000L));
                } else {
                    lock.wait();
                }
            } catch (InterruptedException e) {
                interrupted = true;
            }
        }
        if (interrupted) Thread.currentThread().interrupt();   // the phase advanced first: kept
        return p;
    }
}

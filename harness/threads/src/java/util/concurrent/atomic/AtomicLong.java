/*
 * Clean-room model of AtomicLong for the Rocq machine. Every operation is one synchronized
 * method: in the sequentially consistent thread layer (theories/Core/Threads.v) this gives the
 * same behaviours as the JDK's volatile field and CAS (each operation is atomic and totally
 * ordered). Weak CAS never fails spuriously here; the JDK allows it to (TRUST.md).
 * Behaviour from the JDK 21 javadoc and source.
 */
package java.util.concurrent.atomic;

import java.util.function.LongBinaryOperator;
import java.util.function.LongUnaryOperator;

public class AtomicLong extends Number implements java.io.Serializable {
    private long value;

    public AtomicLong(long initialValue) { value = initialValue; }
    public AtomicLong() { }

    public final synchronized long get() { return value; }
    public final synchronized void set(long newValue) { value = newValue; }
    public final void lazySet(long newValue) { set(newValue); }
    public final synchronized long getAndSet(long newValue) { long v = value; value = newValue; return v; }
    public final synchronized boolean compareAndSet(long expectedValue, long newValue) {
        if (value == expectedValue) { value = newValue; return true; }
        return false;
    }
    public final boolean weakCompareAndSetPlain(long e, long n) { return compareAndSet(e, n); }
    public final boolean weakCompareAndSetVolatile(long e, long n) { return compareAndSet(e, n); }
    public final synchronized long getAndIncrement() { return value++; }
    public final synchronized long getAndDecrement() { return value--; }
    public final synchronized long getAndAdd(long delta) { long v = value; value = v + delta; return v; }
    public final synchronized long incrementAndGet() { return ++value; }
    public final synchronized long decrementAndGet() { return --value; }
    public final synchronized long addAndGet(long delta) { value += delta; return value; }

    // The JDK's update functions retry on contention and may call the function more than once;
    // here the CAS loop is the JDK's, over the synchronized get/compareAndSet.
    public final long getAndUpdate(LongUnaryOperator f) {
        long prev = get(), next = 0;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.applyAsLong(prev);
            if (compareAndSet(prev, next)) return prev;
            haveNext = (prev == (prev = get()));
        }
    }
    public final long updateAndGet(LongUnaryOperator f) {
        long prev = get(), next = 0;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.applyAsLong(prev);
            if (compareAndSet(prev, next)) return next;
            haveNext = (prev == (prev = get()));
        }
    }
    public final long getAndAccumulate(long x, LongBinaryOperator f) {
        long prev = get(), next = 0;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.applyAsLong(prev, x);
            if (compareAndSet(prev, next)) return prev;
            haveNext = (prev == (prev = get()));
        }
    }
    public final long accumulateAndGet(long x, LongBinaryOperator f) {
        long prev = get(), next = 0;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.applyAsLong(prev, x);
            if (compareAndSet(prev, next)) return next;
            haveNext = (prev == (prev = get()));
        }
    }
    public String toString() { return Long.toString(get()); }
    public int intValue() { return (int) get(); }
    public long longValue() { return get(); }
    public float floatValue() { return (float) get(); }
    public double doubleValue() { return (double) get(); }
    public final long getPlain() { return get(); }
    public final void setPlain(long v) { set(v); }
    public final long getOpaque() { return get(); }
    public final void setOpaque(long v) { set(v); }
    public final long getAcquire() { return get(); }
    public final void setRelease(long v) { set(v); }
}


/*
 * Clean-room model of AtomicInteger for the Rocq machine. Every operation is one synchronized
 * method: in the sequentially consistent thread layer (theories/Core/Threads.v) this gives the
 * same behaviours as the JDK's volatile field and CAS (each operation is atomic and totally
 * ordered). Weak CAS never fails spuriously here; the JDK allows it to (TRUST.md).
 * Behaviour from the JDK 21 javadoc and source.
 */
package java.util.concurrent.atomic;

import java.util.function.IntBinaryOperator;
import java.util.function.IntUnaryOperator;

public class AtomicInteger extends Number implements java.io.Serializable {
    private int value;

    public AtomicInteger(int initialValue) { value = initialValue; }
    public AtomicInteger() { }

    public final synchronized int get() { return value; }
    public final synchronized void set(int newValue) { value = newValue; }
    public final void lazySet(int newValue) { set(newValue); }
    public final synchronized int getAndSet(int newValue) { int v = value; value = newValue; return v; }
    public final synchronized boolean compareAndSet(int expectedValue, int newValue) {
        if (value == expectedValue) { value = newValue; return true; }
        return false;
    }
    public final boolean weakCompareAndSetPlain(int e, int n) { return compareAndSet(e, n); }
    public final boolean weakCompareAndSetVolatile(int e, int n) { return compareAndSet(e, n); }
    public final synchronized int getAndIncrement() { return value++; }
    public final synchronized int getAndDecrement() { return value--; }
    public final synchronized int getAndAdd(int delta) { int v = value; value = v + delta; return v; }
    public final synchronized int incrementAndGet() { return ++value; }
    public final synchronized int decrementAndGet() { return --value; }
    public final synchronized int addAndGet(int delta) { value += delta; return value; }

    // The JDK's update functions retry on contention and may call the function more than once;
    // here the CAS loop is the JDK's, over the synchronized get/compareAndSet.
    public final int getAndUpdate(IntUnaryOperator f) {
        int prev = get(), next = 0;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.applyAsInt(prev);
            if (compareAndSet(prev, next)) return prev;
            haveNext = (prev == (prev = get()));
        }
    }
    public final int updateAndGet(IntUnaryOperator f) {
        int prev = get(), next = 0;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.applyAsInt(prev);
            if (compareAndSet(prev, next)) return next;
            haveNext = (prev == (prev = get()));
        }
    }
    public final int getAndAccumulate(int x, IntBinaryOperator f) {
        int prev = get(), next = 0;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.applyAsInt(prev, x);
            if (compareAndSet(prev, next)) return prev;
            haveNext = (prev == (prev = get()));
        }
    }
    public final int accumulateAndGet(int x, IntBinaryOperator f) {
        int prev = get(), next = 0;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.applyAsInt(prev, x);
            if (compareAndSet(prev, next)) return next;
            haveNext = (prev == (prev = get()));
        }
    }
    public String toString() { return Integer.toString(get()); }
    public int intValue() { return get(); }
    public long longValue() { return (long) get(); }
    public float floatValue() { return (float) get(); }
    public double doubleValue() { return (double) get(); }
    public final int getPlain() { return get(); }
    public final void setPlain(int v) { set(v); }
    public final int getOpaque() { return get(); }
    public final void setOpaque(int v) { set(v); }
    public final int getAcquire() { return get(); }
    public final void setRelease(int v) { set(v); }
}

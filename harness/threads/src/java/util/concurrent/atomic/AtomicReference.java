/* Clean-room model of AtomicReference (see AtomicInteger.java). compareAndSet compares references (==). */
package java.util.concurrent.atomic;

import java.util.function.BinaryOperator;
import java.util.function.UnaryOperator;

public class AtomicReference<V> implements java.io.Serializable {
    private V value;
    public AtomicReference(V initialValue) { value = initialValue; }
    public AtomicReference() { }
    public final synchronized V get() { return value; }
    public final synchronized void set(V newValue) { value = newValue; }
    public final void lazySet(V newValue) { set(newValue); }
    public final synchronized V getAndSet(V newValue) { V v = value; value = newValue; return v; }
    public final synchronized boolean compareAndSet(V expectedValue, V newValue) {
        if (value == expectedValue) { value = newValue; return true; }
        return false;
    }
    public final boolean weakCompareAndSetPlain(V e, V n) { return compareAndSet(e, n); }
    public final boolean weakCompareAndSetVolatile(V e, V n) { return compareAndSet(e, n); }
    public final V getAndUpdate(UnaryOperator<V> f) {
        V prev = get(), next = null;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.apply(prev);
            if (compareAndSet(prev, next)) return prev;
            haveNext = (prev == (prev = get()));
        }
    }
    public final V updateAndGet(UnaryOperator<V> f) {
        V prev = get(), next = null;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.apply(prev);
            if (compareAndSet(prev, next)) return next;
            haveNext = (prev == (prev = get()));
        }
    }
    public final V getAndAccumulate(V x, BinaryOperator<V> f) {
        V prev = get(), next = null;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.apply(prev, x);
            if (compareAndSet(prev, next)) return prev;
            haveNext = (prev == (prev = get()));
        }
    }
    public final V accumulateAndGet(V x, BinaryOperator<V> f) {
        V prev = get(), next = null;
        for (boolean haveNext = false;;) {
            if (!haveNext) next = f.apply(prev, x);
            if (compareAndSet(prev, next)) return next;
            haveNext = (prev == (prev = get()));
        }
    }
    public String toString() { return String.valueOf(get()); }
    public final V getPlain() { return get(); }
    public final void setPlain(V v) { set(v); }
    public final V getAcquire() { return get(); }
    public final void setRelease(V v) { set(v); }
}

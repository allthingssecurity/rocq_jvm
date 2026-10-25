/*
 * Clean-room model of ThreadLocal for the Rocq machine: each Thread object keeps its values in
 * two parallel arrays (fields of the Thread model), keyed by the ThreadLocal object (==).
 */
package java.lang;

import java.util.function.Supplier;

public class ThreadLocal<T> {
    public ThreadLocal() { }
    protected T initialValue() { return null; }
    public static <S> ThreadLocal<S> withInitial(Supplier<? extends S> supplier) {
        if (supplier == null) throw new NullPointerException();
        return new SuppliedThreadLocal<>(supplier);
    }
    @SuppressWarnings("unchecked")
    public T get() {
        Thread t = Thread.currentThread();
        int i = t.tlIndex(this);
        if (i >= 0) return (T) t.tlVals[i];
        T v = initialValue();
        t.tlPut(this, v);
        return v;
    }
    public void set(T value) { Thread.currentThread().tlPut(this, value); }
    public void remove() { Thread.currentThread().tlRemove(this); }

    static final class SuppliedThreadLocal<T> extends ThreadLocal<T> {
        private final Supplier<? extends T> supplier;
        SuppliedThreadLocal(Supplier<? extends T> supplier) { this.supplier = supplier; }
        @Override protected T initialValue() { return supplier.get(); }
    }
}

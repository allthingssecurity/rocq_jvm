/* Clean-room model of AtomicBoolean (see AtomicInteger.java). */
package java.util.concurrent.atomic;

public class AtomicBoolean implements java.io.Serializable {
    private boolean value;
    public AtomicBoolean(boolean initialValue) { value = initialValue; }
    public AtomicBoolean() { }
    public final synchronized boolean get() { return value; }
    public final synchronized void set(boolean newValue) { value = newValue; }
    public final void lazySet(boolean newValue) { set(newValue); }
    public final synchronized boolean getAndSet(boolean newValue) { boolean v = value; value = newValue; return v; }
    public final synchronized boolean compareAndSet(boolean expectedValue, boolean newValue) {
        if (value == expectedValue) { value = newValue; return true; }
        return false;
    }
    public boolean weakCompareAndSetPlain(boolean e, boolean n) { return compareAndSet(e, n); }
    public boolean weakCompareAndSetVolatile(boolean e, boolean n) { return compareAndSet(e, n); }
    public String toString() { return get() ? "true" : "false"; }
    public final boolean getPlain() { return get(); }
    public final void setPlain(boolean v) { set(v); }
    public final boolean getAcquire() { return get(); }
    public final void setRelease(boolean v) { set(v); }
}

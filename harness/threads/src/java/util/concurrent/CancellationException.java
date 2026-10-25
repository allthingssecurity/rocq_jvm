/* Clean-room model of CancellationException. */
package java.util.concurrent;
public class CancellationException extends IllegalStateException {
    public CancellationException() { super(); }
    public CancellationException(String message) { super(message); }
    // Throwable.toString (the machine's covers only classes it does not load)
    @Override public String toString() { String m = getLocalizedMessage(); return m != null ? getClass().getName() + ": " + m : getClass().getName(); }
}

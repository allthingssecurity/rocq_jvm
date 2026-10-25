/* Clean-room model of TimeoutException. */
package java.util.concurrent;
public class TimeoutException extends Exception {
    public TimeoutException() { super(); }
    public TimeoutException(String message) { super(message); }
    // Throwable.toString (the machine's covers only classes it does not load)
    @Override public String toString() { String m = getLocalizedMessage(); return m != null ? getClass().getName() + ": " + m : getClass().getName(); }
}

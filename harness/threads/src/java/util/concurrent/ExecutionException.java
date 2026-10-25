/* Clean-room model of ExecutionException: the message is cause.toString(), as Throwable(Throwable). */
package java.util.concurrent;
public class ExecutionException extends Exception {
    private final Throwable cause;
    public ExecutionException(Throwable cause) { super(cause == null ? null : cause.toString()); this.cause = cause; }
    public ExecutionException(String message, Throwable cause) { super(message); this.cause = cause; }
    @Override public synchronized Throwable getCause() { return cause; }
    // Throwable.toString (the machine's covers only classes it does not load)
    @Override public String toString() { String m = getLocalizedMessage(); return m != null ? getClass().getName() + ": " + m : getClass().getName(); }
}

/*
 * rocq-jvm model of java.util.concurrent.CompletionException (clean-room, Apache-2.0).
 * As Throwable: CompletionException(cause) has the message cause.toString() (computed when the
 * exception is made, as the JDK does); the cause is kept here, because the machine's Throwable
 * model keeps only the message. The protected constructors leave the cause unset, so initCause
 * may set it once. toString/getLocalizedMessage are those of Throwable, written out because the
 * machine's Throwable.toString covers only classes it does not load.
 */
package java.util.concurrent;

public class CompletionException extends RuntimeException {
    private static final long serialVersionUID = 7830266012832686185L;
    private Throwable cause;
    private boolean causeSet;

    protected CompletionException() { super(); }
    protected CompletionException(String message) { super(message); }
    public CompletionException(String message, Throwable cause) {
        super(message);
        this.cause = cause;
        this.causeSet = true;
    }
    public CompletionException(Throwable cause) {
        super(cause == null ? null : cause.toString());
        this.cause = cause;
        this.causeSet = true;
    }

    @Override public synchronized Throwable getCause() { return cause; }

    @Override public synchronized Throwable initCause(Throwable c) {
        if (causeSet) throw new IllegalStateException("Can't overwrite cause with " + (c == null ? "a null" : c.toString()), this);
        if (c == this) throw new IllegalArgumentException("Self-causation not permitted", this);
        cause = c;
        causeSet = true;
        return this;
    }

    @Override public String getLocalizedMessage() { return getMessage(); }

    @Override public String toString() {
        String s = getClass().getName();
        String message = getLocalizedMessage();
        return (message != null) ? (s + ": " + message) : s;
    }
}

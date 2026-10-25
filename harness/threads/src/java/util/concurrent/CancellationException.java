/* Clean-room model of CancellationException. */
package java.util.concurrent;
public class CancellationException extends IllegalStateException {
    public CancellationException() { super(); }
    public CancellationException(String message) { super(message); }
}

/* Clean-room model of TimeoutException. */
package java.util.concurrent;
public class TimeoutException extends Exception {
    public TimeoutException() { super(); }
    public TimeoutException(String message) { super(message); }
}

/* The java.util.concurrent.locks.Condition interface (declarations only), for the Rocq machine. */
package java.util.concurrent.locks;
import java.util.concurrent.TimeUnit;
public interface Condition {
    void await() throws InterruptedException;
    void awaitUninterruptibly();
    long awaitNanos(long nanosTimeout) throws InterruptedException;
    boolean await(long time, TimeUnit unit) throws InterruptedException;
    boolean awaitUntil(java.util.Date deadline) throws InterruptedException;
    void signal();
    void signalAll();
}

/* The java.util.concurrent.locks.Lock interface (declarations only), for the Rocq machine. */
package java.util.concurrent.locks;
import java.util.concurrent.TimeUnit;
public interface Lock {
    void lock();
    void lockInterruptibly() throws InterruptedException;
    boolean tryLock();
    boolean tryLock(long time, TimeUnit unit) throws InterruptedException;
    void unlock();
    Condition newCondition();
}

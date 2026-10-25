/* Clean-room model of CountDownLatch over a monitor (wait/notifyAll); timed await not modelled (STUCK). */
package java.util.concurrent;

public class CountDownLatch {
    private long count;
    public CountDownLatch(int count) {
        if (count < 0) throw new IllegalArgumentException("count < 0");
        this.count = count;
    }
    public void await() throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        synchronized (this) { while (count > 0) wait(); }
    }
    public boolean await(long timeout, TimeUnit unit) throws InterruptedException {
        if (Thread.interrupted()) throw new InterruptedException();
        long nanos = unit.toNanos(timeout);
        synchronized (this) {
            long deadline = System.nanoTime() + nanos;
            while (count > 0) {
                if (nanos <= 0) return false;
                wait(Math.max(1, nanos / 1000000L));
                nanos = deadline - System.nanoTime();
            }
            return true;
        }
    }
    public void countDown() {
        synchronized (this) {
            if (count > 0) { count--; if (count == 0) notifyAll(); }
        }
    }
    public long getCount() { synchronized (this) { return count; } }
    public String toString() { return super.toString() + "[Count = " + getCount() + "]"; }
}

/* Clean-room model of java.util.concurrent.Delayed. */
package java.util.concurrent;

public interface Delayed extends Comparable<Delayed> {
    long getDelay(TimeUnit unit);
}

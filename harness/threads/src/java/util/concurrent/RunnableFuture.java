/* Clean-room model of java.util.concurrent.RunnableFuture. */
package java.util.concurrent;

public interface RunnableFuture<V> extends Runnable, Future<V> {
    void run();
}

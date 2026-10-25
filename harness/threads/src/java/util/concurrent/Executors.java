/* Clean-room model of the Executors factories used most (see ThreadPool.java). */
package java.util.concurrent;

public class Executors {
    private Executors() { }
    public static ExecutorService newFixedThreadPool(int nThreads) { return new ThreadPool(nThreads); }
    public static ExecutorService newSingleThreadExecutor() { return new ThreadPool(1); }
    public static ExecutorService newCachedThreadPool() { return new ThreadPool(Integer.MAX_VALUE); }
    public static ScheduledExecutorService newScheduledThreadPool(int corePoolSize) { return new ScheduledThreadPoolExecutor(corePoolSize); }
    public static ScheduledExecutorService newScheduledThreadPool(int corePoolSize, ThreadFactory threadFactory) { return new ScheduledThreadPoolExecutor(corePoolSize, threadFactory); }
    public static ScheduledExecutorService newSingleThreadScheduledExecutor() { return new ScheduledThreadPoolExecutor(1); }
    public static ScheduledExecutorService newSingleThreadScheduledExecutor(ThreadFactory threadFactory) { return new ScheduledThreadPoolExecutor(1, threadFactory); }
    public static <T> Callable<T> callable(Runnable task, T result) {
        if (task == null) throw new NullPointerException();
        return () -> { task.run(); return result; };
    }
}

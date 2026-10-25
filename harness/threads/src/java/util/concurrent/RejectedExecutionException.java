/*
 * Clean-room model of java.util.concurrent.RejectedExecutionException. The AbortPolicy message
 * ("Task " + task + " rejected from " + pool) is computed when it is first read: it contains
 * Object.toString of JDK objects, which needs identity hash codes (STUCK when read), and a
 * program that only catches the exception must not be STUCK.
 */
package java.util.concurrent;

public class RejectedExecutionException extends RuntimeException {
    private transient Runnable lazyTask;
    private transient ThreadPoolExecutor lazyPool;
    private String lazyMessage;

    public RejectedExecutionException() { super(); }
    public RejectedExecutionException(String message) { super(message); }
    public RejectedExecutionException(String message, Throwable cause) { super(message, cause); }
    public RejectedExecutionException(Throwable cause) { super(cause); }

    RejectedExecutionException(Runnable task, ThreadPoolExecutor pool) {
        super();
        this.lazyTask = task;
        this.lazyPool = pool;
    }

    public String getMessage() {
        if (lazyPool != null) {
            if (lazyMessage == null) lazyMessage = "Task " + lazyTask.toString() + " rejected from " + lazyPool.toString();
            return lazyMessage;
        }
        return super.getMessage();
    }

    public String getLocalizedMessage() {
        return getMessage();
    }

    public String toString() {
        String s = getClass().getName();
        String message = getLocalizedMessage();
        return (message != null) ? (s + ": " + message) : s;
    }
}

/* Clean-room model of java.util.concurrent.ArrayBlockingQueue (see FifoBlockingQueue); the
 * fairness flag only orders waiting threads, which the monitor-based model does not distinguish. */
package java.util.concurrent;

import java.util.Collection;

public class ArrayBlockingQueue<E> extends FifoBlockingQueue<E> {
    public ArrayBlockingQueue(int capacity) {
        super(capacity);
    }

    public ArrayBlockingQueue(int capacity, boolean fair) {
        super(capacity);
    }

    public ArrayBlockingQueue(int capacity, boolean fair, Collection<? extends E> c) {
        super(capacity);
        for (E e : c) {
            if (e == null) throw new NullPointerException();
            if (!offer(e)) throw new IllegalArgumentException();
        }
    }
}

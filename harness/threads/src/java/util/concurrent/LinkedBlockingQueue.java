/* Clean-room model of java.util.concurrent.LinkedBlockingQueue (see FifoBlockingQueue). */
package java.util.concurrent;

import java.util.Collection;

public class LinkedBlockingQueue<E> extends FifoBlockingQueue<E> {
    public LinkedBlockingQueue() {
        super(Integer.MAX_VALUE);
    }

    public LinkedBlockingQueue(int capacity) {
        super(capacity);
    }

    public LinkedBlockingQueue(Collection<? extends E> c) {
        super(Integer.MAX_VALUE);
        for (E e : c) {
            if (e == null) throw new NullPointerException();
            offer(e);
        }
    }
}

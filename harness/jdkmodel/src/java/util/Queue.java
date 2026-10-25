/* rocq-jvm model of java.util.Queue (clean-room, Apache-2.0). */
package java.util;

public interface Queue<E> extends Collection<E> {
    boolean add(E e);
    boolean offer(E e);
    E remove();
    E poll();
    E element();
    E peek();
}

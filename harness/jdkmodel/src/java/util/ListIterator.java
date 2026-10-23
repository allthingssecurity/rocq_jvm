/* rocq-jvm model of java.util.ListIterator (clean-room, Apache-2.0). */
package java.util;

public interface ListIterator<E> extends Iterator<E> {
    boolean hasNext();
    E next();
    boolean hasPrevious();
    E previous();
    int nextIndex();
    int previousIndex();
    void remove();
    void set(E e);
    void add(E e);
}

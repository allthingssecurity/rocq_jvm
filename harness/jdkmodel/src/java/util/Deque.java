/*
 * Clean-room model of java.util.Deque (from the Javadoc) for the Rocq machine; r82 hunt, adopted into harness/jdkmodel (harness/camel/hunt/jdkextra).
 * The SequencedCollection methods of JDK 21 (reversed, addFirst/getFirst as SequencedCollection) are not modelled.
 */
package java.util;

public interface Deque<E> extends Queue<E> {
    void addFirst(E e);
    void addLast(E e);
    boolean offerFirst(E e);
    boolean offerLast(E e);
    E removeFirst();
    E removeLast();
    E pollFirst();
    E pollLast();
    E getFirst();
    E getLast();
    E peekFirst();
    E peekLast();
    boolean removeFirstOccurrence(Object o);
    boolean removeLastOccurrence(Object o);
    boolean add(E e);
    boolean offer(E e);
    E remove();
    E poll();
    E element();
    E peek();
    void push(E e);
    E pop();
    boolean remove(Object o);
    boolean contains(Object o);
    int size();
    Iterator<E> iterator();
    Iterator<E> descendingIterator();
}

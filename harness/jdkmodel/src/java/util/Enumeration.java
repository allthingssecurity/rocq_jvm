/*
 * rocq-jvm model of java.util.Enumeration (clean-room, Apache-2.0).
 */
package java.util;

public interface Enumeration<E> {
    boolean hasMoreElements();

    E nextElement();

    /** Javadoc: an Iterator over the remaining elements; remove is unsupported. */
    default Iterator<E> asIterator() {
        return new Iterator<E>() {
            public boolean hasNext() {
                return hasMoreElements();
            }

            public E next() {
                return nextElement();
            }
        };
    }
}

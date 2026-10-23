/*
 * rocq-jvm model of java.util.Iterator (clean-room, Apache-2.0; written from the Javadoc,
 * not derived from OpenJDK source).
 */
package java.util;

import java.util.function.Consumer;

public interface Iterator<E> {
    boolean hasNext();

    E next();

    /** Javadoc: the default implementation throws UnsupportedOperationException. */
    default void remove() {
        throw new UnsupportedOperationException();
    }

    /** Javadoc: performs the action for each remaining element until all have been processed. */
    default void forEachRemaining(Consumer<? super E> action) {
        if (action == null) throw new NullPointerException();
        while (hasNext()) action.accept(next());
    }
}

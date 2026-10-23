/*
 * rocq-jvm model of java.util.LinkedHashSet (clean-room, Apache-2.0; from the Javadoc: a
 * HashSet backed by a LinkedHashMap, iteration in insertion order; re-adding an element does
 * not change its position).  SequencedSet methods (JDK 21) are not modelled.
 */
package java.util;

public class LinkedHashSet<E> extends HashSet<E> implements Set<E>, Cloneable, java.io.Serializable {
    public LinkedHashSet(int initialCapacity, float loadFactor) {
        super(initialCapacity, loadFactor, true);
    }

    public LinkedHashSet(int initialCapacity) {
        super(initialCapacity, .75f, true);
    }

    public LinkedHashSet() {
        super(16, .75f, true);
    }

    public LinkedHashSet(Collection<? extends E> c) {
        super(HashSet.capacityFor(Math.max(c.size(), 12)), .75f, true);
        addAll(c);
    }
}

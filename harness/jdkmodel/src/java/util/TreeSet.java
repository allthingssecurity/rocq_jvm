/*
 * rocq-jvm model of java.util.TreeSet (clean-room, Apache-2.0), from the Javadoc: a NavigableSet
 * backed by a TreeMap whose values are a shared marker object.
 * Not modelled (STUCK): subSet/headSet/tailSet, descendingSet, clone, serialization.
 */
package java.util;

public class TreeSet<E> extends AbstractSet<E> implements NavigableSet<E>, Cloneable, java.io.Serializable {
    private transient TreeMap<E, Object> m;
    private static final Object PRESENT = new Object();

    public TreeSet() {
        m = new TreeMap<>();
    }

    public TreeSet(Comparator<? super E> comparator) {
        m = new TreeMap<>(comparator);
    }

    public TreeSet(Collection<? extends E> c) {
        this();
        addAll(c);
    }

    public TreeSet(SortedSet<E> s) {
        this(s.comparator());
        addAll(s);
    }

    public Iterator<E> iterator() {
        return m.keyIterator();
    }

    public Iterator<E> descendingIterator() {
        return m.descendingKeyIterator();
    }

    public NavigableSet<E> descendingSet() {
        throw ModelStuck.unsupported("TreeSet.descendingSet");
    }

    public int size() {
        return m.size();
    }

    public boolean isEmpty() {
        return m.isEmpty();
    }

    public boolean contains(Object o) {
        return m.containsKey(o);
    }

    public boolean add(E e) {
        return m.put(e, PRESENT) == null;
    }

    public boolean remove(Object o) {
        return m.remove(o) == PRESENT;
    }

    public void clear() {
        m.clear();
    }

    public boolean addAll(Collection<? extends E> c) {
        boolean modified = false;
        for (E e : c) {
            if (add(e)) modified = true;
        }
        return modified;
    }

    public NavigableSet<E> subSet(E fromElement, boolean fromInclusive, E toElement, boolean toInclusive) {
        throw ModelStuck.unsupported("TreeSet.subSet");
    }

    public NavigableSet<E> headSet(E toElement, boolean inclusive) {
        throw ModelStuck.unsupported("TreeSet.headSet");
    }

    public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
        throw ModelStuck.unsupported("TreeSet.tailSet");
    }

    public SortedSet<E> subSet(E fromElement, E toElement) {
        throw ModelStuck.unsupported("TreeSet.subSet");
    }

    public SortedSet<E> headSet(E toElement) {
        throw ModelStuck.unsupported("TreeSet.headSet");
    }

    public SortedSet<E> tailSet(E fromElement) {
        throw ModelStuck.unsupported("TreeSet.tailSet");
    }

    public Comparator<? super E> comparator() {
        return m.comparator();
    }

    public E first() {
        return m.firstKey();
    }

    public E last() {
        return m.lastKey();
    }

    public E lower(E e) {
        return m.lowerKey(e);
    }

    public E floor(E e) {
        return m.floorKey(e);
    }

    public E ceiling(E e) {
        return m.ceilingKey(e);
    }

    public E higher(E e) {
        return m.higherKey(e);
    }

    public E pollFirst() {
        Map.Entry<E, ?> e = m.pollFirstEntry();
        return (e == null) ? null : e.getKey();
    }

    public E pollLast() {
        Map.Entry<E, ?> e = m.pollLastEntry();
        return (e == null) ? null : e.getKey();
    }

    @SuppressWarnings("unchecked")
    public Object clone() {
        TreeSet<E> clone;
        try {
            clone = (TreeSet<E>) super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e);
        }
        clone.m = new TreeMap<>(m);
        return clone;
    }
}

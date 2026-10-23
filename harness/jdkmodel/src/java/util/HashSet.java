/*
 * rocq-jvm model of java.util.HashSet (clean-room, Apache-2.0; from the Javadoc: a set backed
 * by a HashMap whose keys are the elements, so iteration order is the map's key order).
 * HashSet(Collection) sizes the map for max(c.size(), 12) elements (JDK 19+).
 */
package java.util;

public class HashSet<E> extends AbstractSet<E> implements Set<E>, Cloneable, java.io.Serializable {
    transient HashMap<E, Object> map;
    static final Object PRESENT = new Object();

    public HashSet() {
        map = new HashMap<>();
    }

    public HashSet(Collection<? extends E> c) {
        map = new HashMap<>(capacityFor(Math.max(c.size(), 12)));
        addAll(c);
    }

    public HashSet(int initialCapacity, float loadFactor) {
        map = new HashMap<>(initialCapacity, loadFactor);
    }

    public HashSet(int initialCapacity) {
        map = new HashMap<>(initialCapacity);
    }

    HashSet(int initialCapacity, float loadFactor, boolean linked) {
        map = new LinkedHashMap<>(initialCapacity, loadFactor);
    }

    /** ceil(n / 0.75): the initial capacity that holds n mappings without a resize. */
    static int capacityFor(int n) {
        double d = n / 0.75;
        int t = (int) d;
        if ((double) t < d) t++;
        return t;
    }

    public Iterator<E> iterator() {
        return map.keySet().iterator();
    }

    public int size() {
        return map.size();
    }

    public boolean isEmpty() {
        return map.isEmpty();
    }

    public boolean contains(Object o) {
        return map.containsKey(o);
    }

    public boolean add(E e) {
        return map.put(e, PRESENT) == null;
    }

    public boolean remove(Object o) {
        return map.remove(o) == PRESENT;
    }

    public void clear() {
        map.clear();
    }

    public Object clone() {
        throw ModelStuck.unsupported("HashSet.clone");
    }

    public Object[] toArray() {
        return map.keySet().toArray();
    }

    public <T> T[] toArray(T[] a) {
        return map.keySet().toArray(a);
    }
}

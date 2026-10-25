/*
 * rocq-jvm model of java.util.TreeMap (clean-room, Apache-2.0), from the Javadoc.
 *
 * The entries are kept in a sorted array (binary search) instead of a red-black tree: the
 * observable behaviour (results, exceptions, sorted iteration, fail-fast iterators) does not
 * depend on the shape of the tree. Ordering: the comparator, or the keys' compareTo. As in the
 * JDK, the first put into an empty map compares the key with itself (type and null check), and
 * with natural ordering a null key is a NullPointerException.
 *
 * Differences that only a comparator with side effects could observe: the sequence of compare
 * calls. Not modelled (STUCK): subMap/headMap/tailMap, descendingMap, clone, serialization.
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

public class TreeMap<K, V> extends AbstractMap<K, V> implements NavigableMap<K, V>, Cloneable, java.io.Serializable {
    private final Comparator<? super K> comparator;
    private Entry<K, V>[] es;
    private int size;
    private transient int modCount;
    private transient EntrySet entrySet;
    private transient KeySet<K> navigableKeySet;

    public TreeMap() {
        comparator = null;
        es = newArray(8);
    }

    public TreeMap(Comparator<? super K> comparator) {
        this.comparator = comparator;
        es = newArray(8);
    }

    public TreeMap(Map<? extends K, ? extends V> m) {
        comparator = null;
        es = newArray(8);
        putAll(m);
    }

    @SuppressWarnings("unchecked")
    public TreeMap(SortedMap<K, ? extends V> m) {
        comparator = m.comparator();
        es = newArray(8);
        for (Map.Entry<K, ? extends V> e : m.entrySet()) put(e.getKey(), e.getValue());
    }

    @SuppressWarnings("unchecked")
    private static <K, V> Entry<K, V>[] newArray(int n) {
        return (Entry<K, V>[]) new Entry<?, ?>[n];
    }

    static final class Entry<K, V> implements Map.Entry<K, V> {
        K key;
        V value;

        Entry(K key, V value) {
            this.key = key;
            this.value = value;
        }

        public K getKey() {
            return key;
        }

        public V getValue() {
            return value;
        }

        public V setValue(V value) {
            V old = this.value;
            this.value = value;
            return old;
        }

        public boolean equals(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            return eq(key, e.getKey()) && eq(value, e.getValue());
        }

        public int hashCode() {
            return hashOf(key) ^ hashOf(value);
        }

        public String toString() {
            return key + "=" + value;
        }
    }

    /** An immutable snapshot (firstEntry, floorEntry, ...: setValue is unsupported). */
    static <K, V> Map.Entry<K, V> exportEntry(Entry<K, V> e) {
        return (e == null) ? null : new AbstractMap.SimpleImmutableEntry<>(e);
    }

    static <K> K keyOrNull(Entry<K, ?> e) {
        return (e == null) ? null : e.key;
    }

    @SuppressWarnings("unchecked")
    final int compare(Object k1, Object k2) {
        return comparator == null ? ((Comparable<Object>) k1).compareTo(k2) : comparator.compare((K) k1, (K) k2);
    }

    /** Index of key, or -(insertion point) - 1. */
    private int search(Object key) {
        if (comparator == null && key == null) throw new NullPointerException();
        int lo = 0, hi = size - 1;
        while (lo <= hi) {
            int mid = (lo + hi) >>> 1;
            int c = compare(key, es[mid].key);
            if (c < 0) hi = mid - 1;
            else if (c > 0) lo = mid + 1;
            else return mid;
        }
        return -(lo + 1);
    }

    final Entry<K, V> getEntry(Object key) {
        int i = search(key);
        return i >= 0 ? es[i] : null;
    }

    private void insertAt(int i, Entry<K, V> e) {
        if (size == es.length) {
            Entry<K, V>[] n = newArray(es.length * 2);
            for (int j = 0; j < size; j++) n[j] = es[j];
            es = n;
        }
        for (int j = size; j > i; j--) es[j] = es[j - 1];
        es[i] = e;
        size++;
        modCount++;
    }

    private void removeAt(int i) {
        for (int j = i; j + 1 < size; j++) es[j] = es[j + 1];
        es[--size] = null;
        modCount++;
    }

    public int size() {
        return size;
    }

    public boolean containsKey(Object key) {
        return getEntry(key) != null;
    }

    public boolean containsValue(Object value) {
        for (int i = 0; i < size; i++) {
            if (eq(value, es[i].value)) return true;
        }
        return false;
    }

    public V get(Object key) {
        Entry<K, V> p = getEntry(key);
        return p == null ? null : p.value;
    }

    public Comparator<? super K> comparator() {
        return comparator;
    }

    public K firstKey() {
        if (size == 0) throw new NoSuchElementException();
        return es[0].key;
    }

    public K lastKey() {
        if (size == 0) throw new NoSuchElementException();
        return es[size - 1].key;
    }

    public void putAll(Map<? extends K, ? extends V> map) {
        for (Map.Entry<? extends K, ? extends V> e : map.entrySet()) put(e.getKey(), e.getValue());
    }

    private V put(K key, V value, boolean replaceOld) {
        if (size == 0) {
            compare(key, key);   // type (and possibly null) check
            insertAt(0, new Entry<>(key, value));
            return null;
        }
        int i = search(key);
        if (i >= 0) {
            Entry<K, V> e = es[i];
            V old = e.value;
            if (replaceOld || old == null) e.value = value;
            return old;
        }
        insertAt(-i - 1, new Entry<>(key, value));
        return null;
    }

    public V put(K key, V value) {
        return put(key, value, true);
    }

    public V putIfAbsent(K key, V value) {
        return put(key, value, false);
    }

    public V remove(Object key) {
        int i = search(key);
        if (i < 0) return null;
        V old = es[i].value;
        removeAt(i);
        return old;
    }

    public void clear() {
        modCount++;
        for (int i = 0; i < size; i++) es[i] = null;
        size = 0;
    }

    public Object clone() {
        throw ModelStuck.unsupported("TreeMap.clone");
    }

    // ---- navigation ----

    public Map.Entry<K, V> firstEntry() {
        return exportEntry(size == 0 ? null : es[0]);
    }

    public Map.Entry<K, V> lastEntry() {
        return exportEntry(size == 0 ? null : es[size - 1]);
    }

    public Map.Entry<K, V> pollFirstEntry() {
        if (size == 0) return null;
        Map.Entry<K, V> r = exportEntry(es[0]);
        removeAt(0);
        return r;
    }

    public Map.Entry<K, V> pollLastEntry() {
        if (size == 0) return null;
        Map.Entry<K, V> r = exportEntry(es[size - 1]);
        removeAt(size - 1);
        return r;
    }

    /** The entry of the greatest key < key (strict) or <= key. */
    private Entry<K, V> below(K key, boolean inclusive) {
        int i = search(key);
        int j = (i >= 0) ? (inclusive ? i : i - 1) : (-i - 1) - 1;
        return j >= 0 ? es[j] : null;
    }

    /** The entry of the least key > key (strict) or >= key. */
    private Entry<K, V> above(K key, boolean inclusive) {
        int i = search(key);
        int j = (i >= 0) ? (inclusive ? i : i + 1) : -i - 1;
        return j < size ? es[j] : null;
    }

    public Map.Entry<K, V> lowerEntry(K key) {
        return exportEntry(below(key, false));
    }

    public K lowerKey(K key) {
        return keyOrNull(below(key, false));
    }

    public Map.Entry<K, V> floorEntry(K key) {
        return exportEntry(below(key, true));
    }

    public K floorKey(K key) {
        return keyOrNull(below(key, true));
    }

    public Map.Entry<K, V> ceilingEntry(K key) {
        return exportEntry(above(key, true));
    }

    public K ceilingKey(K key) {
        return keyOrNull(above(key, true));
    }

    public Map.Entry<K, V> higherEntry(K key) {
        return exportEntry(above(key, false));
    }

    public K higherKey(K key) {
        return keyOrNull(above(key, false));
    }

    // ---- Map default-method overrides ----

    public boolean replace(K key, V oldValue, V newValue) {
        Entry<K, V> p = getEntry(key);
        if (p != null && eq(oldValue, p.value)) {
            p.value = newValue;
            return true;
        }
        return false;
    }

    public V replace(K key, V value) {
        Entry<K, V> p = getEntry(key);
        if (p != null) {
            V old = p.value;
            p.value = value;
            return old;
        }
        return null;
    }

    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        int mc = modCount;
        for (int i = 0; i < size; i++) {
            action.accept(es[i].key, es[i].value);
            if (mc != modCount) throw new ConcurrentModificationException();
        }
    }

    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        int mc = modCount;
        for (int i = 0; i < size; i++) {
            es[i].value = function.apply(es[i].key, es[i].value);
            if (mc != modCount) throw new ConcurrentModificationException();
        }
    }

    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null) throw new NullPointerException();
        if (size == 0) compare(key, key);
        int i = search(key);
        if (i >= 0 && es[i].value != null) return es[i].value;
        int mc = modCount;
        V v = mappingFunction.apply(key);
        if (mc != modCount) throw new ConcurrentModificationException();
        if (v == null) return null;
        if (i >= 0) es[i].value = v;
        else insertAt(-i - 1, new Entry<>(key, v));
        return v;
    }

    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        int i = search(key);
        if (i < 0 || es[i].value == null) return null;
        int mc = modCount;
        V v = remappingFunction.apply(key, es[i].value);
        if (mc != modCount) throw new ConcurrentModificationException();
        if (v == null) removeAt(i);
        else es[i].value = v;
        return v;
    }

    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        if (size == 0) compare(key, key);
        int i = search(key);
        V old = (i >= 0) ? es[i].value : null;
        int mc = modCount;
        V v = remappingFunction.apply(key, old);
        if (mc != modCount) throw new ConcurrentModificationException();
        if (i >= 0) {
            if (v == null) removeAt(i);
            else es[i].value = v;
        } else if (v != null) {
            insertAt(-i - 1, new Entry<>(key, v));
        }
        return v;
    }

    public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null || value == null) throw new NullPointerException();
        if (size == 0) compare(key, key);
        int i = search(key);
        if (i < 0) {
            insertAt(-i - 1, new Entry<>(key, value));
            return value;
        }
        V old = es[i].value;
        if (old == null) {
            es[i].value = value;
            return value;
        }
        int mc = modCount;
        V v = remappingFunction.apply(old, value);
        if (mc != modCount) throw new ConcurrentModificationException();
        if (v == null) removeAt(i);
        else es[i].value = v;
        return v;
    }

    // ---- views ----

    public Set<K> keySet() {
        return navigableKeySet();
    }

    public NavigableSet<K> navigableKeySet() {
        KeySet<K> nks = navigableKeySet;
        return (nks != null) ? nks : (navigableKeySet = new KeySet<>(this));
    }

    public NavigableSet<K> descendingKeySet() {
        throw ModelStuck.unsupported("TreeMap.descendingKeySet");
    }

    public NavigableMap<K, V> descendingMap() {
        throw ModelStuck.unsupported("TreeMap.descendingMap");
    }

    public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
        throw ModelStuck.unsupported("TreeMap.subMap");
    }

    public NavigableMap<K, V> headMap(K toKey, boolean inclusive) {
        throw ModelStuck.unsupported("TreeMap.headMap");
    }

    public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
        throw ModelStuck.unsupported("TreeMap.tailMap");
    }

    public SortedMap<K, V> subMap(K fromKey, K toKey) {
        throw ModelStuck.unsupported("TreeMap.subMap");
    }

    public SortedMap<K, V> headMap(K toKey) {
        throw ModelStuck.unsupported("TreeMap.headMap");
    }

    public SortedMap<K, V> tailMap(K fromKey) {
        throw ModelStuck.unsupported("TreeMap.tailMap");
    }

    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new Values();
            values = vs;
        }
        return vs;
    }

    public Set<Map.Entry<K, V>> entrySet() {
        EntrySet es = entrySet;
        return (es != null) ? es : (entrySet = new EntrySet());
    }

    /** Ascending iterator over the entries; [descending] walks from the last. */
    abstract class PrivateEntryIterator<T> implements Iterator<T> {
        int next;          // index of the next entry
        Entry<K, V> nextE;
        Entry<K, V> lastReturned;
        int expectedModCount;
        final boolean descending;

        PrivateEntryIterator(boolean descending) {
            this.descending = descending;
            expectedModCount = modCount;
            next = descending ? size - 1 : 0;
            nextE = (next >= 0 && next < size) ? es[next] : null;
        }

        public final boolean hasNext() {
            return nextE != null;
        }

        final Entry<K, V> nextEntry() {
            Entry<K, V> e = nextE;
            if (e == null) throw new NoSuchElementException();
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            next = descending ? next - 1 : next + 1;
            nextE = (next >= 0 && next < size) ? es[next] : null;
            lastReturned = e;
            return e;
        }

        public void remove() {
            if (lastReturned == null) throw new IllegalStateException();
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            int i = search(lastReturned.key);
            removeAt(i);
            if (!descending) next--;
            nextE = (next >= 0 && next < size) ? es[next] : null;
            expectedModCount = modCount;
            lastReturned = null;
        }
    }

    final class EntryIterator extends PrivateEntryIterator<Map.Entry<K, V>> {
        EntryIterator() {
            super(false);
        }

        public Map.Entry<K, V> next() {
            return nextEntry();
        }
    }

    final class ValueIterator extends PrivateEntryIterator<V> {
        ValueIterator() {
            super(false);
        }

        public V next() {
            return nextEntry().value;
        }
    }

    final class KeyIterator extends PrivateEntryIterator<K> {
        KeyIterator(boolean descending) {
            super(descending);
        }

        public K next() {
            return nextEntry().key;
        }
    }

    Iterator<K> keyIterator() {
        return new KeyIterator(false);
    }

    Iterator<K> descendingKeyIterator() {
        return new KeyIterator(true);
    }

    final class Values extends AbstractCollection<V> {
        public Iterator<V> iterator() {
            return new ValueIterator();
        }

        public int size() {
            return TreeMap.this.size();
        }

        public boolean contains(Object o) {
            return TreeMap.this.containsValue(o);
        }

        public boolean remove(Object o) {
            for (int i = 0; i < size; i++) {
                if (eq(es[i].value, o)) {
                    removeAt(i);
                    return true;
                }
            }
            return false;
        }

        public void clear() {
            TreeMap.this.clear();
        }
    }

    final class EntrySet extends AbstractSet<Map.Entry<K, V>> {
        public Iterator<Map.Entry<K, V>> iterator() {
            return new EntryIterator();
        }

        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
            Object value = entry.getValue();
            Entry<K, V> p = getEntry(entry.getKey());
            return p != null && eq(p.getValue(), value);
        }

        public boolean remove(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
            Object value = entry.getValue();
            int i = search(entry.getKey());
            if (i >= 0 && eq(es[i].getValue(), value)) {
                removeAt(i);
                return true;
            }
            return false;
        }

        public int size() {
            return TreeMap.this.size();
        }

        public void clear() {
            TreeMap.this.clear();
        }
    }

    static final class KeySet<E> extends AbstractSet<E> implements NavigableSet<E> {
        private final TreeMap<E, ?> m;

        KeySet(TreeMap<E, ?> map) {
            m = map;
        }

        public Iterator<E> iterator() {
            return m.keyIterator();
        }

        public Iterator<E> descendingIterator() {
            return m.descendingKeyIterator();
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

        public void clear() {
            m.clear();
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

        public E first() {
            return m.firstKey();
        }

        public E last() {
            return m.lastKey();
        }

        public Comparator<? super E> comparator() {
            return m.comparator();
        }

        public E pollFirst() {
            Map.Entry<E, ?> e = m.pollFirstEntry();
            return (e == null) ? null : e.getKey();
        }

        public E pollLast() {
            Map.Entry<E, ?> e = m.pollLastEntry();
            return (e == null) ? null : e.getKey();
        }

        public boolean remove(Object o) {
            int oldSize = size();
            m.remove(o);
            return size() != oldSize;
        }

        public NavigableSet<E> subSet(E fromElement, boolean fromInclusive, E toElement, boolean toInclusive) {
            throw ModelStuck.unsupported("TreeMap.KeySet.subSet");
        }

        public NavigableSet<E> headSet(E toElement, boolean inclusive) {
            throw ModelStuck.unsupported("TreeMap.KeySet.headSet");
        }

        public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
            throw ModelStuck.unsupported("TreeMap.KeySet.tailSet");
        }

        public SortedSet<E> subSet(E fromElement, E toElement) {
            throw ModelStuck.unsupported("TreeMap.KeySet.subSet");
        }

        public SortedSet<E> headSet(E toElement) {
            throw ModelStuck.unsupported("TreeMap.KeySet.headSet");
        }

        public SortedSet<E> tailSet(E fromElement) {
            throw ModelStuck.unsupported("TreeMap.KeySet.tailSet");
        }

        public NavigableSet<E> descendingSet() {
            throw ModelStuck.unsupported("TreeMap.KeySet.descendingSet");
        }
    }
}

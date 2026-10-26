/*
 * rocq-jvm model of java.util.TreeMap (clean-room, Apache-2.0).
 *
 * The entries are kept in a sorted array (binary search) instead of a red-black tree: the
 * observable behaviour (results, exceptions and their messages, sorted iteration, fail-fast
 * iterators, the navigable views) does not depend on the shape of the tree. Each entry knows its
 * index in the array, so iterators step to the successor / predecessor without comparisons.
 * Ordering: the comparator, or the keys' compareTo. As in the JDK, the first insertion into an
 * empty map compares the key with itself (type and null check); get/remove/containsKey and the
 * insertion into a non-empty map reject a null key with natural ordering (Objects.requireNonNull)
 * and cast the key to Comparable before searching.
 *
 * Exceptions that the JDK raises implicitly inside compareTo (a null argument, a key of another
 * class, a key that is not Comparable) are thrown explicitly with HotSpot's message; for classes
 * outside java.base (where the message names a class loader) the model is STUCK.
 *
 * Views: navigableKeySet, descendingKeySet, descendingMap and the subMap/headMap/tailMap views
 * (AscendingSubMap / DescendingSubMap) with the JDK's range checks ("fromKey > toKey", "key out of
 * range", "fromKey out of range", "toKey out of range"), fence-key iteration and fail-fast
 * iterators.
 *
 * Differences that are not modelled: the sequence of compare calls (observable only by a
 * comparator with side effects); the red-black deletion of an entry with two children, which in
 * the JDK moves the successor's key and value into the deleted node (observable only through an
 * entry object held across the removal of its predecessor: such an entry stays live here). A
 * sub-map iterator whose next entry was removed by another path is STUCK in hasNext (the JDK's
 * answer depends on the tree shape). Not modelled (STUCK): serialization, spliterators.
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

public class TreeMap<K, V> extends AbstractMap<K, V> implements NavigableMap<K, V>, Cloneable, java.io.Serializable {
    private final Comparator<? super K> comparator;
    private Entry<K, V>[] es;
    private int size;
    transient int modCount;
    private transient EntrySet entrySet;
    private transient KeySet<K> navigableKeySet;
    private transient NavigableMap<K, V> descendingMap;

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

    public TreeMap(SortedMap<K, ? extends V> m) {
        if (m == null) throw invokeOnNull("java.util.SortedMap.comparator()", "m");
        comparator = m.comparator();
        es = newArray(8);
        buildFromSorted(m.size(), m.entrySet().iterator());
    }

    @SuppressWarnings("unchecked")
    private static <K, V> Entry<K, V>[] newArray(int n) {
        return (Entry<K, V>[]) new Entry<?, ?>[n];
    }

    static NullPointerException invokeOnNull(String method, String what) {
        return new NullPointerException("Cannot invoke \"" + method + "\" because \"" + what + "\" is null");
    }

    static final class Entry<K, V> implements Map.Entry<K, V> {
        K key;
        V value;
        int idx = -1;          // index in es while in the map, else -1
        boolean deleted;       // removed from the map (not by clear)

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
            return valEquals(key, e.getKey()) && valEquals(value, e.getValue());
        }

        public int hashCode() {
            int keyHash = (key == null ? 0 : key.hashCode());
            int valueHash = (value == null ? 0 : value.hashCode());
            return keyHash ^ valueHash;
        }

        public String toString() {
            return key + "=" + value;
        }
    }

    static boolean valEquals(Object o1, Object o2) {
        return (o1 == null ? o2 == null : o1.equals(o2));
    }

    /** An immutable snapshot (firstEntry, floorEntry, ...: setValue is unsupported). */
    static <K, V> Map.Entry<K, V> exportEntry(Entry<K, V> e) {
        return (e == null) ? null : new AbstractMap.SimpleImmutableEntry<>(e);
    }

    static <K> K keyOrNull(Entry<K, ?> e) {
        return (e == null) ? null : e.key;
    }

    static <K> K key(Entry<K, ?> e) {
        if (e == null) throw new NoSuchElementException();
        return e.key;
    }

    // ---- comparisons ----

    /** The JDK's compare: comparator.compare(k1, k2), or ((Comparable) k1).compareTo(k2). */
    @SuppressWarnings("unchecked")
    final int compare(Object k1, Object k2) {
        if (comparator != null) return comparator.compare((K) k1, (K) k2);
        if (k1 == null) throw invokeOnNull("java.lang.Comparable.compareTo(Object)", "k1");
        return cmpNat(k1, k2);
    }

    /** k.compareTo(x) for a non-null k of natural ordering, with the exceptions HotSpot raises
     *  inside the JDK's code (checkcast to Comparable, the bridge method's cast, a null argument). */
    @SuppressWarnings("unchecked")
    static int cmpNat(Object k, Object x) {
        if (!(k instanceof Comparable)) throw castFail(k, "java.lang.Comparable");
        if (isJdkComparable(k)) {
            if (x == null) throw new NullPointerException("Cannot read field \"value\" because \"" + argName(k) + "\" is null");
            if (x.getClass() != k.getClass()) throw castFail(x, k.getClass().getName());
        } else if (!(k instanceof Enum) && inJavaBase(k.getClass().getName())) {
            throw ModelStuck.unsupported("TreeMap: compareTo of a JDK class other than String, the boxes and enums");
        }
        return ((Comparable<Object>) k).compareTo(x);
    }

    /** ClassCastException of a checkcast of o to class 'to' (both in java.base), else STUCK. */
    static ClassCastException castFail(Object o, String to) {
        String a = o.getClass().getName();
        if (!inJavaBase(a) || !inJavaBase(to)) throw ModelStuck.unsupported("ClassCastException message for a class outside java.base");
        return new ClassCastException("class " + a + " cannot be cast to class " + to + " (" + a + " and " + to
            + " are in module java.base of loader 'bootstrap')");
    }

    private static boolean inJavaBase(String cn) {
        return cn.startsWith("java.lang.") || cn.startsWith("java.util.");
    }

    private static String argName(Object k) {
        if (k instanceof String) return "anotherString";
        if (k instanceof Integer) return "anotherInteger";
        if (k instanceof Long) return "anotherLong";
        if (k instanceof Short) return "anotherShort";
        if (k instanceof Byte) return "anotherByte";
        if (k instanceof Character) return "anotherCharacter";
        return "b";   // Boolean.compareTo(Boolean b)
    }

    static boolean isJdkComparableX(Object x) {
        return isJdkComparable(x);
    }

    private static boolean isJdkComparable(Object x) {
        return x instanceof String || x instanceof Integer || x instanceof Long || x instanceof Short
            || x instanceof Byte || x instanceof Character || x instanceof Boolean;
    }

    /** The checks before a natural-ordering search of the JDK's getEntry/put/compute...:
     *  Objects.requireNonNull(key) and the cast to Comparable. */
    private void natKeyCheck(Object key) {
        if (comparator == null) {
            if (key == null) throw new NullPointerException();
            if (!(key instanceof Comparable)) throw castFail(key, "java.lang.Comparable");
        }
    }

    /** Index of key, or -(insertion point) - 1 (compare(key, element) as the JDK does). */
    private int find(Object key) {
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
        natKeyCheck(key);
        int i = find(key);
        return i >= 0 ? es[i] : null;
    }

    final Entry<K, V> getFirstEntry() {
        return size == 0 ? null : es[0];
    }

    final Entry<K, V> getLastEntry() {
        return size == 0 ? null : es[size - 1];
    }

    /** The successor of a live entry. */
    final Entry<K, V> successor(Entry<K, V> e) {
        int i = e.idx;
        if (i < 0) throw ModelStuck.unsupported("TreeMap: successor of a removed entry");
        return (i + 1 < size) ? es[i + 1] : null;
    }

    final Entry<K, V> predecessor(Entry<K, V> e) {
        int i = e.idx;
        if (i < 0) throw ModelStuck.unsupported("TreeMap: predecessor of a removed entry");
        return (i > 0) ? es[i - 1] : null;
    }

    final Entry<K, V> getCeilingEntry(K key) {
        if (size == 0) return null;
        int i = find(key);
        int j = (i >= 0) ? i : -i - 1;
        return j < size ? es[j] : null;
    }

    final Entry<K, V> getHigherEntry(K key) {
        if (size == 0) return null;
        int i = find(key);
        int j = (i >= 0) ? i + 1 : -i - 1;
        return j < size ? es[j] : null;
    }

    final Entry<K, V> getFloorEntry(K key) {
        if (size == 0) return null;
        int i = find(key);
        int j = (i >= 0) ? i : (-i - 1) - 1;
        return j >= 0 ? es[j] : null;
    }

    final Entry<K, V> getLowerEntry(K key) {
        if (size == 0) return null;
        int i = find(key);
        int j = (i >= 0) ? i - 1 : (-i - 1) - 1;
        return j >= 0 ? es[j] : null;
    }

    private void insertAt(int i, Entry<K, V> e) {
        if (size == es.length) {
            Entry<K, V>[] n = newArray(es.length * 2);
            for (int j = 0; j < size; j++) n[j] = es[j];
            es = n;
        }
        for (int j = size; j > i; j--) {
            es[j] = es[j - 1];
            es[j].idx = j;
        }
        es[i] = e;
        e.idx = i;
        size++;
        modCount++;
    }

    final void deleteEntry(Entry<K, V> e) {
        int i = e.idx;
        if (i < 0 || es[i] != e) throw ModelStuck.unsupported("TreeMap: deleting a removed entry");
        for (int j = i; j + 1 < size; j++) {
            es[j] = es[j + 1];
            es[j].idx = j;
        }
        es[--size] = null;
        e.idx = -1;
        e.deleted = true;
        modCount++;
    }

    private void addEntryToEmptyMap(K key, V value) {
        compare(key, key);   // type (and possibly null) check
        insertAt(0, new Entry<>(key, value));
    }

    /** buildFromSorted: the entries of a sorted map in order, no comparisons. */
    private void buildFromSorted(int n, Iterator<?> it) {
        modCount++;
        for (int i = 0; i < n; i++) {
            @SuppressWarnings("unchecked")
            Map.Entry<K, V> e = (Map.Entry<K, V>) it.next();
            append(new Entry<>(e.getKey(), e.getValue()));
        }
    }

    /** TreeSet.addAll into an empty set from a SortedSet with the same comparator. */
    void addAllForTreeSet(SortedSet<? extends K> set, V defaultVal) {
        modCount++;
        int n = set.size();
        Iterator<? extends K> it = set.iterator();
        for (int i = 0; i < n; i++) append(new Entry<>(it.next(), defaultVal));
    }

    private void append(Entry<K, V> x) {
        if (size == es.length) {
            Entry<K, V>[] a = newArray(es.length * 2);
            for (int j = 0; j < size; j++) a[j] = es[j];
            es = a;
        }
        es[size] = x;
        x.idx = size;
        size++;
    }

    public int size() {
        return size;
    }

    public boolean containsKey(Object key) {
        return getEntry(key) != null;
    }

    public boolean containsValue(Object value) {
        for (int i = 0; i < size; i++) {
            if (valEquals(value, es[i].value)) return true;
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
        return key(getFirstEntry());
    }

    public K lastKey() {
        return key(getLastEntry());
    }

    public void putAll(Map<? extends K, ? extends V> map) {
        if (map == null) throw invokeOnNull("java.util.Map.size()", "map");
        int mapSize = map.size();
        if (size == 0 && mapSize != 0 && map instanceof SortedMap) {
            Comparator<?> c = ((SortedMap<?, ?>) map).comparator();
            if (comparator == c || (comparator != null && comparator.equals(c))) {
                buildFromSorted(mapSize, map.entrySet().iterator());
                return;
            }
        }
        super.putAll(map);
    }

    private V put(K key, V value, boolean replaceOld) {
        if (size == 0) {
            addEntryToEmptyMap(key, value);
            return null;
        }
        natKeyCheck(key);
        int i = find(key);
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
        Entry<K, V> p = getEntry(key);
        if (p == null) return null;
        V old = p.value;
        deleteEntry(p);
        return old;
    }

    public void clear() {
        modCount++;
        for (int i = 0; i < size; i++) {
            es[i].idx = -1;
            es[i] = null;
        }
        size = 0;
    }

    /** JDK: a copy with new entries (same order), the comparator, and modCount 0. */
    @SuppressWarnings("unchecked")
    public Object clone() {
        TreeMap<K, V> clone;
        try {
            clone = (TreeMap<K, V>) super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e);
        }
        Entry<K, V>[] copy = newArray(es.length);
        for (int i = 0; i < size; i++) {
            copy[i] = new Entry<>(es[i].key, es[i].value);
            copy[i].idx = i;
        }
        clone.es = copy;
        clone.modCount = 0;
        clone.entrySet = null;
        clone.navigableKeySet = null;
        clone.descendingMap = null;
        return clone;
    }

    // ---- navigation ----

    public Map.Entry<K, V> firstEntry() {
        return exportEntry(getFirstEntry());
    }

    public Map.Entry<K, V> lastEntry() {
        return exportEntry(getLastEntry());
    }

    public Map.Entry<K, V> pollFirstEntry() {
        Entry<K, V> p = getFirstEntry();
        Map.Entry<K, V> r = exportEntry(p);
        if (p != null) deleteEntry(p);
        return r;
    }

    public Map.Entry<K, V> pollLastEntry() {
        Entry<K, V> p = getLastEntry();
        Map.Entry<K, V> r = exportEntry(p);
        if (p != null) deleteEntry(p);
        return r;
    }

    public Map.Entry<K, V> lowerEntry(K key) {
        return exportEntry(getLowerEntry(key));
    }

    public K lowerKey(K key) {
        return keyOrNull(getLowerEntry(key));
    }

    public Map.Entry<K, V> floorEntry(K key) {
        return exportEntry(getFloorEntry(key));
    }

    public K floorKey(K key) {
        return keyOrNull(getFloorEntry(key));
    }

    public Map.Entry<K, V> ceilingEntry(K key) {
        return exportEntry(getCeilingEntry(key));
    }

    public K ceilingKey(K key) {
        return keyOrNull(getCeilingEntry(key));
    }

    public Map.Entry<K, V> higherEntry(K key) {
        return exportEntry(getHigherEntry(key));
    }

    public K higherKey(K key) {
        return keyOrNull(getHigherEntry(key));
    }

    // ---- Map default-method overrides ----

    public boolean replace(K key, V oldValue, V newValue) {
        Entry<K, V> p = getEntry(key);
        if (p != null && valEquals(oldValue, p.value)) {
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
        for (Entry<K, V> e = getFirstEntry(); e != null; e = successor(e)) {
            action.accept(e.key, e.value);
            if (mc != modCount) throw new ConcurrentModificationException();
        }
    }

    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        int mc = modCount;
        for (Entry<K, V> e = getFirstEntry(); e != null; e = successor(e)) {
            e.value = function.apply(e.key, e.value);
            if (mc != modCount) throw new ConcurrentModificationException();
        }
    }

    private V callMappingFunctionWithCheck(K key, Function<? super K, ? extends V> f) {
        int mc = modCount;
        V v = f.apply(key);
        if (mc != modCount) throw new ConcurrentModificationException();
        return v;
    }

    private V callRemappingFunctionWithCheck(K key, V old, BiFunction<? super K, ? super V, ? extends V> f) {
        int mc = modCount;
        V v = f.apply(key, old);
        if (mc != modCount) throw new ConcurrentModificationException();
        return v;
    }

    private V remapValue(Entry<K, V> t, K key, BiFunction<? super K, ? super V, ? extends V> f) {
        V v = callRemappingFunctionWithCheck(key, t.value, f);
        if (v == null) {
            deleteEntry(t);
            return null;
        }
        t.value = v;
        return v;
    }

    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null) throw new NullPointerException();
        if (size == 0) {
            V v = callMappingFunctionWithCheck(key, mappingFunction);
            if (v == null) return null;
            addEntryToEmptyMap(key, v);
            return v;
        }
        natKeyCheck(key);
        int i = find(key);
        if (i >= 0) {
            Entry<K, V> t = es[i];
            if (t.value == null) t.value = callMappingFunctionWithCheck(key, mappingFunction);
            return t.value;
        }
        V v = callMappingFunctionWithCheck(key, mappingFunction);
        if (v == null) return null;
        insertAt(-i - 1, new Entry<>(key, v));
        return v;
    }

    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        Entry<K, V> p = getEntry(key);
        if (p != null && p.value != null) return remapValue(p, key, remappingFunction);
        return null;
    }

    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        if (size == 0) {
            V v = callRemappingFunctionWithCheck(key, null, remappingFunction);
            if (v == null) return null;
            addEntryToEmptyMap(key, v);
            return v;
        }
        natKeyCheck(key);
        int i = find(key);
        if (i >= 0) return remapValue(es[i], key, remappingFunction);
        V v = callRemappingFunctionWithCheck(key, null, remappingFunction);
        if (v == null) return null;
        insertAt(-i - 1, new Entry<>(key, v));
        return v;
    }

    public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null || value == null) throw new NullPointerException();
        if (size == 0) {
            addEntryToEmptyMap(key, value);
            return value;
        }
        natKeyCheck(key);
        int i = find(key);
        if (i < 0) {
            insertAt(-i - 1, new Entry<>(key, value));
            return value;
        }
        Entry<K, V> t = es[i];
        V v;
        if (t.value == null) {
            v = value;
        } else {
            int mc = modCount;
            v = remappingFunction.apply(t.value, value);
            if (mc != modCount) throw new ConcurrentModificationException();
        }
        if (v == null) {
            deleteEntry(t);
            return null;
        }
        t.value = v;
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
        return descendingMap().navigableKeySet();
    }

    public NavigableMap<K, V> descendingMap() {
        NavigableMap<K, V> km = descendingMap;
        return (km != null) ? km : (descendingMap = new DescendingSubMap<>(this, true, null, true, true, null, true));
    }

    public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
        return new AscendingSubMap<>(this, false, fromKey, fromInclusive, false, toKey, toInclusive);
    }

    public NavigableMap<K, V> headMap(K toKey, boolean inclusive) {
        return new AscendingSubMap<>(this, true, null, true, false, toKey, inclusive);
    }

    public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
        return new AscendingSubMap<>(this, false, fromKey, inclusive, true, null, true);
    }

    public SortedMap<K, V> subMap(K fromKey, K toKey) {
        return subMap(fromKey, true, toKey, false);
    }

    public SortedMap<K, V> headMap(K toKey) {
        return headMap(toKey, false);
    }

    public SortedMap<K, V> tailMap(K fromKey) {
        return tailMap(fromKey, true);
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

    final class Values extends AbstractCollection<V> {
        public Iterator<V> iterator() {
            return new ValueIterator(getFirstEntry());
        }

        public int size() {
            return TreeMap.this.size();
        }

        public boolean contains(Object o) {
            return TreeMap.this.containsValue(o);
        }

        public boolean remove(Object o) {
            for (Entry<K, V> e = getFirstEntry(); e != null; e = successor(e)) {
                if (valEquals(e.getValue(), o)) {
                    deleteEntry(e);
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
            return new EntryIterator(getFirstEntry());
        }

        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
            Object value = entry.getValue();
            Entry<K, V> p = getEntry(entry.getKey());
            return p != null && valEquals(p.getValue(), value);
        }

        public boolean remove(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
            Object value = entry.getValue();
            Entry<K, V> p = getEntry(entry.getKey());
            if (p != null && valEquals(p.getValue(), value)) {
                deleteEntry(p);
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

    Iterator<K> keyIterator() {
        return new KeyIterator(getFirstEntry());
    }

    Iterator<K> descendingKeyIterator() {
        return new DescendingKeyIterator(getLastEntry());
    }

    /** The key set of the map and of every sub map (static: delegates to a NavigableMap). */
    static final class KeySet<E> extends AbstractSet<E> implements NavigableSet<E> {
        private final NavigableMap<E, ?> m;

        KeySet(NavigableMap<E, ?> map) {
            m = map;
        }

        public Iterator<E> iterator() {
            if (m instanceof TreeMap) return ((TreeMap<E, ?>) m).keyIterator();
            return ((NavigableSubMap<E, ?>) m).keyIterator();
        }

        public Iterator<E> descendingIterator() {
            if (m instanceof TreeMap) return ((TreeMap<E, ?>) m).descendingKeyIterator();
            return ((NavigableSubMap<E, ?>) m).descendingKeyIterator();
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
            return new KeySet<>(m.subMap(fromElement, fromInclusive, toElement, toInclusive));
        }

        public NavigableSet<E> headSet(E toElement, boolean inclusive) {
            return new KeySet<>(m.headMap(toElement, inclusive));
        }

        public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
            return new KeySet<>(m.tailMap(fromElement, inclusive));
        }

        public SortedSet<E> subSet(E fromElement, E toElement) {
            return subSet(fromElement, true, toElement, false);
        }

        public SortedSet<E> headSet(E toElement) {
            return headSet(toElement, false);
        }

        public SortedSet<E> tailSet(E fromElement) {
            return tailSet(fromElement, true);
        }

        public NavigableSet<E> descendingSet() {
            return new KeySet<>(m.descendingMap());
        }
    }

    /** Iterators of the whole map: the next entry, fail-fast on modCount. */
    abstract class PrivateEntryIterator<T> implements Iterator<T> {
        Entry<K, V> next;
        Entry<K, V> lastReturned;
        int expectedModCount;

        PrivateEntryIterator(Entry<K, V> first) {
            expectedModCount = modCount;
            next = first;
        }

        public final boolean hasNext() {
            return next != null;
        }

        final Entry<K, V> nextEntry() {
            Entry<K, V> e = next;
            if (e == null) throw new NoSuchElementException();
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            next = successor(e);
            lastReturned = e;
            return e;
        }

        final Entry<K, V> prevEntry() {
            Entry<K, V> e = next;
            if (e == null) throw new NoSuchElementException();
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            next = predecessor(e);
            lastReturned = e;
            return e;
        }

        public void remove() {
            if (lastReturned == null) throw new IllegalStateException();
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            deleteEntry(lastReturned);
            expectedModCount = modCount;
            lastReturned = null;
        }
    }

    final class EntryIterator extends PrivateEntryIterator<Map.Entry<K, V>> {
        EntryIterator(Entry<K, V> first) {
            super(first);
        }

        public Map.Entry<K, V> next() {
            return nextEntry();
        }
    }

    final class ValueIterator extends PrivateEntryIterator<V> {
        ValueIterator(Entry<K, V> first) {
            super(first);
        }

        public V next() {
            return nextEntry().value;
        }
    }

    final class KeyIterator extends PrivateEntryIterator<K> {
        KeyIterator(Entry<K, V> first) {
            super(first);
        }

        public K next() {
            return nextEntry().key;
        }
    }

    final class DescendingKeyIterator extends PrivateEntryIterator<K> {
        DescendingKeyIterator(Entry<K, V> first) {
            super(first);
        }

        public K next() {
            return prevEntry().key;
        }
    }

    // ---- sub maps ----

    /** Fence key of an unbounded sub-map iterator (matches no key). */
    private static final Object UNBOUNDED = new Object();

    /**
     * A range view [lo, hi] of the backing map. A bound is (fromStart, lo, loInclusive) /
     * (toEnd, hi, hiInclusive): fromStart/toEnd mean unbounded. The ascending and descending
     * classes map the relative operations to the absolute ones.
     */
    abstract static class NavigableSubMap<K, V> extends AbstractMap<K, V> implements NavigableMap<K, V>, java.io.Serializable {
        final TreeMap<K, V> m;
        final K lo, hi;
        final boolean fromStart, toEnd;
        final boolean loInclusive, hiInclusive;

        NavigableSubMap(TreeMap<K, V> m, boolean fromStart, K lo, boolean loInclusive, boolean toEnd, K hi, boolean hiInclusive) {
            if (!fromStart && !toEnd) {
                if (m.compare(lo, hi) > 0) throw new IllegalArgumentException("fromKey > toKey");
            } else {
                if (!fromStart) m.compare(lo, lo);   // type check
                if (!toEnd) m.compare(hi, hi);
            }
            this.m = m;
            this.fromStart = fromStart;
            this.lo = lo;
            this.loInclusive = loInclusive;
            this.toEnd = toEnd;
            this.hi = hi;
            this.hiInclusive = hiInclusive;
        }

        final boolean tooLow(Object key) {
            if (!fromStart) {
                int c = m.compare(key, lo);
                if (c < 0 || (c == 0 && !loInclusive)) return true;
            }
            return false;
        }

        final boolean tooHigh(Object key) {
            if (!toEnd) {
                int c = m.compare(key, hi);
                if (c > 0 || (c == 0 && !hiInclusive)) return true;
            }
            return false;
        }

        final boolean inRange(Object key) {
            return !tooLow(key) && !tooHigh(key);
        }

        final boolean inClosedRange(Object key) {
            return (fromStart || m.compare(key, lo) >= 0) && (toEnd || m.compare(hi, key) >= 0);
        }

        final boolean inRange(Object key, boolean inclusive) {
            return inclusive ? inRange(key) : inClosedRange(key);
        }

        final TreeMap.Entry<K, V> absLowest() {
            TreeMap.Entry<K, V> e = fromStart ? m.getFirstEntry() : (loInclusive ? m.getCeilingEntry(lo) : m.getHigherEntry(lo));
            return (e == null || tooHigh(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absHighest() {
            TreeMap.Entry<K, V> e = toEnd ? m.getLastEntry() : (hiInclusive ? m.getFloorEntry(hi) : m.getLowerEntry(hi));
            return (e == null || tooLow(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absCeiling(K key) {
            if (tooLow(key)) return absLowest();
            TreeMap.Entry<K, V> e = m.getCeilingEntry(key);
            return (e == null || tooHigh(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absHigher(K key) {
            if (tooLow(key)) return absLowest();
            TreeMap.Entry<K, V> e = m.getHigherEntry(key);
            return (e == null || tooHigh(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absFloor(K key) {
            if (tooHigh(key)) return absHighest();
            TreeMap.Entry<K, V> e = m.getFloorEntry(key);
            return (e == null || tooLow(e.key)) ? null : e;
        }

        final TreeMap.Entry<K, V> absLower(K key) {
            if (tooHigh(key)) return absHighest();
            TreeMap.Entry<K, V> e = m.getLowerEntry(key);
            return (e == null || tooLow(e.key)) ? null : e;
        }

        /** The first entry past the range, for ascending iteration (null: unbounded). */
        final TreeMap.Entry<K, V> absHighFence() {
            return toEnd ? null : (hiInclusive ? m.getHigherEntry(hi) : m.getCeilingEntry(hi));
        }

        /** The first entry before the range, for descending iteration. */
        final TreeMap.Entry<K, V> absLowFence() {
            return fromStart ? null : (loInclusive ? m.getLowerEntry(lo) : m.getFloorEntry(lo));
        }

        abstract TreeMap.Entry<K, V> subLowest();

        abstract TreeMap.Entry<K, V> subHighest();

        abstract TreeMap.Entry<K, V> subCeiling(K key);

        abstract TreeMap.Entry<K, V> subHigher(K key);

        abstract TreeMap.Entry<K, V> subFloor(K key);

        abstract TreeMap.Entry<K, V> subLower(K key);

        abstract Iterator<K> keyIterator();

        abstract Iterator<K> descendingKeyIterator();

        public boolean isEmpty() {
            return (fromStart && toEnd) ? m.isEmpty() : entrySet().isEmpty();
        }

        public int size() {
            return (fromStart && toEnd) ? m.size() : entrySet().size();
        }

        public final boolean containsKey(Object key) {
            return inRange(key) && m.containsKey(key);
        }

        public final V put(K key, V value) {
            if (!inRange(key)) throw new IllegalArgumentException("key out of range");
            return m.put(key, value);
        }

        public V putIfAbsent(K key, V value) {
            if (!inRange(key)) throw new IllegalArgumentException("key out of range");
            return m.putIfAbsent(key, value);
        }

        public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
            if (!inRange(key)) throw new IllegalArgumentException("key out of range");
            return m.merge(key, value, remappingFunction);
        }

        public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
            if (!inRange(key)) {
                if (mappingFunction == null) throw invokeOnNull("java.util.function.Function.apply(Object)", "mappingFunction");
                if (mappingFunction.apply(key) == null) return null;
                throw new IllegalArgumentException("key out of range");
            }
            return m.computeIfAbsent(key, mappingFunction);
        }

        public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
            if (!inRange(key)) {
                if (remappingFunction == null) throw invokeOnNull("java.util.function.BiFunction.apply(Object, Object)", "remappingFunction");
                if (remappingFunction.apply(key, null) == null) return null;
                throw new IllegalArgumentException("key out of range");
            }
            return m.compute(key, remappingFunction);
        }

        public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
            return !inRange(key) ? null : m.computeIfPresent(key, remappingFunction);
        }

        public final V get(Object key) {
            return !inRange(key) ? null : m.get(key);
        }

        public final V remove(Object key) {
            return !inRange(key) ? null : m.remove(key);
        }

        public final Map.Entry<K, V> ceilingEntry(K key) {
            return exportEntry(subCeiling(key));
        }

        public final K ceilingKey(K key) {
            return keyOrNull(subCeiling(key));
        }

        public final Map.Entry<K, V> higherEntry(K key) {
            return exportEntry(subHigher(key));
        }

        public final K higherKey(K key) {
            return keyOrNull(subHigher(key));
        }

        public final Map.Entry<K, V> floorEntry(K key) {
            return exportEntry(subFloor(key));
        }

        public final K floorKey(K key) {
            return keyOrNull(subFloor(key));
        }

        public final Map.Entry<K, V> lowerEntry(K key) {
            return exportEntry(subLower(key));
        }

        public final K lowerKey(K key) {
            return keyOrNull(subLower(key));
        }

        public final K firstKey() {
            return key(subLowest());
        }

        public final K lastKey() {
            return key(subHighest());
        }

        public final Map.Entry<K, V> firstEntry() {
            return exportEntry(subLowest());
        }

        public final Map.Entry<K, V> lastEntry() {
            return exportEntry(subHighest());
        }

        public final Map.Entry<K, V> pollFirstEntry() {
            TreeMap.Entry<K, V> e = subLowest();
            Map.Entry<K, V> result = exportEntry(e);
            if (e != null) m.deleteEntry(e);
            return result;
        }

        public final Map.Entry<K, V> pollLastEntry() {
            TreeMap.Entry<K, V> e = subHighest();
            Map.Entry<K, V> result = exportEntry(e);
            if (e != null) m.deleteEntry(e);
            return result;
        }

        transient NavigableMap<K, V> descendingMapView;
        transient EntrySetView entrySetView;
        transient KeySet<K> navigableKeySetView;

        public final NavigableSet<K> navigableKeySet() {
            KeySet<K> nksv = navigableKeySetView;
            return (nksv != null) ? nksv : (navigableKeySetView = new TreeMap.KeySet<>(this));
        }

        public final Set<K> keySet() {
            return navigableKeySet();
        }

        public NavigableSet<K> descendingKeySet() {
            return descendingMap().navigableKeySet();
        }

        public final SortedMap<K, V> subMap(K fromKey, K toKey) {
            return subMap(fromKey, true, toKey, false);
        }

        public final SortedMap<K, V> headMap(K toKey) {
            return headMap(toKey, false);
        }

        public final SortedMap<K, V> tailMap(K fromKey) {
            return tailMap(fromKey, true);
        }

        abstract class EntrySetView extends AbstractSet<Map.Entry<K, V>> {
            public int size() {
                if (fromStart && toEnd) return m.size();
                int n = 0;
                Iterator<?> i = iterator();
                while (i.hasNext()) {
                    n++;
                    i.next();
                }
                return n;
            }

            public boolean isEmpty() {
                TreeMap.Entry<K, V> n = absLowest();
                return n == null || tooHigh(n.key);
            }

            public boolean contains(Object o) {
                if (!(o instanceof Map.Entry)) return false;
                Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
                Object key = entry.getKey();
                if (!inRange(key)) return false;
                TreeMap.Entry<?, ?> node = m.getEntry(key);
                return node != null && valEquals(node.getValue(), entry.getValue());
            }

            public boolean remove(Object o) {
                if (!(o instanceof Map.Entry)) return false;
                Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
                Object key = entry.getKey();
                if (!inRange(key)) return false;
                TreeMap.Entry<K, V> node = m.getEntry(key);
                if (node != null && valEquals(node.getValue(), entry.getValue())) {
                    m.deleteEntry(node);
                    return true;
                }
                return false;
            }
        }

        /** Iteration from first towards a fence entry (exclusive), compared by key identity. */
        abstract class SubMapIterator<T> implements Iterator<T> {
            TreeMap.Entry<K, V> lastReturned;
            TreeMap.Entry<K, V> next;
            final Object fenceKey;
            int expectedModCount;

            SubMapIterator(TreeMap.Entry<K, V> first, TreeMap.Entry<K, V> fence) {
                expectedModCount = m.modCount;
                next = first;
                fenceKey = fence == null ? UNBOUNDED : fence.key;
            }

            public final boolean hasNext() {
                TreeMap.Entry<K, V> e = next;
                if (e == null) return false;
                if (e.deleted) throw ModelStuck.unsupported("TreeMap sub-map iterator: next entry removed by another path");
                return e.key != fenceKey;
            }

            final TreeMap.Entry<K, V> nextEntry() {
                TreeMap.Entry<K, V> e = next;
                if (e != null && e.deleted && e.key != fenceKey) throw ModelStuck.unsupported("TreeMap sub-map iterator: next entry removed by another path");
                if (e == null || e.key == fenceKey) throw new NoSuchElementException();
                if (m.modCount != expectedModCount) throw new ConcurrentModificationException();
                next = m.successor(e);
                lastReturned = e;
                return e;
            }

            final TreeMap.Entry<K, V> prevEntry() {
                TreeMap.Entry<K, V> e = next;
                if (e != null && e.deleted && e.key != fenceKey) throw ModelStuck.unsupported("TreeMap sub-map iterator: next entry removed by another path");
                if (e == null || e.key == fenceKey) throw new NoSuchElementException();
                if (m.modCount != expectedModCount) throw new ConcurrentModificationException();
                next = m.predecessor(e);
                lastReturned = e;
                return e;
            }

            public void remove() {
                if (lastReturned == null) throw new IllegalStateException();
                if (m.modCount != expectedModCount) throw new ConcurrentModificationException();
                m.deleteEntry(lastReturned);
                lastReturned = null;
                expectedModCount = m.modCount;
            }
        }

        final class SubMapEntryIterator extends SubMapIterator<Map.Entry<K, V>> {
            SubMapEntryIterator(TreeMap.Entry<K, V> first, TreeMap.Entry<K, V> fence) {
                super(first, fence);
            }

            public Map.Entry<K, V> next() {
                return nextEntry();
            }
        }

        final class DescendingSubMapEntryIterator extends SubMapIterator<Map.Entry<K, V>> {
            DescendingSubMapEntryIterator(TreeMap.Entry<K, V> last, TreeMap.Entry<K, V> fence) {
                super(last, fence);
            }

            public Map.Entry<K, V> next() {
                return prevEntry();
            }
        }

        final class SubMapKeyIterator extends SubMapIterator<K> {
            SubMapKeyIterator(TreeMap.Entry<K, V> first, TreeMap.Entry<K, V> fence) {
                super(first, fence);
            }

            public K next() {
                return nextEntry().key;
            }
        }

        final class DescendingSubMapKeyIterator extends SubMapIterator<K> {
            DescendingSubMapKeyIterator(TreeMap.Entry<K, V> last, TreeMap.Entry<K, V> fence) {
                super(last, fence);
            }

            public K next() {
                return prevEntry().key;
            }
        }
    }

    static final class AscendingSubMap<K, V> extends NavigableSubMap<K, V> {
        AscendingSubMap(TreeMap<K, V> m, boolean fromStart, K lo, boolean loInclusive, boolean toEnd, K hi, boolean hiInclusive) {
            super(m, fromStart, lo, loInclusive, toEnd, hi, hiInclusive);
        }

        public Comparator<? super K> comparator() {
            return m.comparator();
        }

        public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
            if (!inRange(fromKey, fromInclusive)) throw new IllegalArgumentException("fromKey out of range");
            if (!inRange(toKey, toInclusive)) throw new IllegalArgumentException("toKey out of range");
            return new AscendingSubMap<>(m, false, fromKey, fromInclusive, false, toKey, toInclusive);
        }

        public NavigableMap<K, V> headMap(K toKey, boolean inclusive) {
            if (!inRange(toKey, inclusive)) throw new IllegalArgumentException("toKey out of range");
            return new AscendingSubMap<>(m, fromStart, lo, loInclusive, false, toKey, inclusive);
        }

        public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
            if (!inRange(fromKey, inclusive)) throw new IllegalArgumentException("fromKey out of range");
            return new AscendingSubMap<>(m, false, fromKey, inclusive, toEnd, hi, hiInclusive);
        }

        public NavigableMap<K, V> descendingMap() {
            NavigableMap<K, V> mv = descendingMapView;
            return (mv != null) ? mv : (descendingMapView = new DescendingSubMap<>(m, fromStart, lo, loInclusive, toEnd, hi, hiInclusive));
        }

        Iterator<K> keyIterator() {
            return new SubMapKeyIterator(absLowest(), absHighFence());
        }

        Iterator<K> descendingKeyIterator() {
            return new DescendingSubMapKeyIterator(absHighest(), absLowFence());
        }

        final class AscendingEntrySetView extends EntrySetView {
            public Iterator<Map.Entry<K, V>> iterator() {
                return new SubMapEntryIterator(absLowest(), absHighFence());
            }
        }

        public Set<Map.Entry<K, V>> entrySet() {
            EntrySetView es = entrySetView;
            return (es != null) ? es : (entrySetView = new AscendingEntrySetView());
        }

        TreeMap.Entry<K, V> subLowest() {
            return absLowest();
        }

        TreeMap.Entry<K, V> subHighest() {
            return absHighest();
        }

        TreeMap.Entry<K, V> subCeiling(K key) {
            return absCeiling(key);
        }

        TreeMap.Entry<K, V> subHigher(K key) {
            return absHigher(key);
        }

        TreeMap.Entry<K, V> subFloor(K key) {
            return absFloor(key);
        }

        TreeMap.Entry<K, V> subLower(K key) {
            return absLower(key);
        }
    }

    static final class DescendingSubMap<K, V> extends NavigableSubMap<K, V> {
        DescendingSubMap(TreeMap<K, V> m, boolean fromStart, K lo, boolean loInclusive, boolean toEnd, K hi, boolean hiInclusive) {
            super(m, fromStart, lo, loInclusive, toEnd, hi, hiInclusive);
        }

        private final Comparator<? super K> reverseComparator = Collections.reverseOrder(m.comparator);

        public Comparator<? super K> comparator() {
            return reverseComparator;
        }

        public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
            if (!inRange(fromKey, fromInclusive)) throw new IllegalArgumentException("fromKey out of range");
            if (!inRange(toKey, toInclusive)) throw new IllegalArgumentException("toKey out of range");
            return new DescendingSubMap<>(m, false, toKey, toInclusive, false, fromKey, fromInclusive);
        }

        public NavigableMap<K, V> headMap(K toKey, boolean inclusive) {
            if (!inRange(toKey, inclusive)) throw new IllegalArgumentException("toKey out of range");
            return new DescendingSubMap<>(m, false, toKey, inclusive, toEnd, hi, hiInclusive);
        }

        public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
            if (!inRange(fromKey, inclusive)) throw new IllegalArgumentException("fromKey out of range");
            return new DescendingSubMap<>(m, fromStart, lo, loInclusive, false, fromKey, inclusive);
        }

        public NavigableMap<K, V> descendingMap() {
            NavigableMap<K, V> mv = descendingMapView;
            return (mv != null) ? mv : (descendingMapView = new AscendingSubMap<>(m, fromStart, lo, loInclusive, toEnd, hi, hiInclusive));
        }

        Iterator<K> keyIterator() {
            return new DescendingSubMapKeyIterator(absHighest(), absLowFence());
        }

        Iterator<K> descendingKeyIterator() {
            return new SubMapKeyIterator(absLowest(), absHighFence());
        }

        final class DescendingEntrySetView extends EntrySetView {
            public Iterator<Map.Entry<K, V>> iterator() {
                return new DescendingSubMapEntryIterator(absHighest(), absLowFence());
            }
        }

        public Set<Map.Entry<K, V>> entrySet() {
            EntrySetView es = entrySetView;
            return (es != null) ? es : (entrySetView = new DescendingEntrySetView());
        }

        TreeMap.Entry<K, V> subLowest() {
            return absHighest();
        }

        TreeMap.Entry<K, V> subHighest() {
            return absLowest();
        }

        TreeMap.Entry<K, V> subCeiling(K key) {
            return absFloor(key);
        }

        TreeMap.Entry<K, V> subHigher(K key) {
            return absLower(key);
        }

        TreeMap.Entry<K, V> subFloor(K key) {
            return absCeiling(key);
        }

        TreeMap.Entry<K, V> subLower(K key) {
            return absHigher(key);
        }
    }
}

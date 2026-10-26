/*
 * rocq-jvm model of java.util.WeakHashMap (clean-room, Apache-2.0).
 *
 * No garbage collection: entries are never cleared by the collector (a legal behaviour of a JVM
 * whose collector never runs; every key stays strongly reachable from its entry here), so the
 * stale-entry queue is always empty. The table is the JDK's: power-of-two buckets indexed by the
 * JDK's supplemental hash, new entries at the head of a bucket, resize to twice the length when
 * the size exceeds the threshold, and iteration from the last bucket to the first. A null key is
 * stored as a private marker object, whose hash code is its identity hash code (an environment
 * value of the machine), so the bucket of the null key differs from HotSpot's.
 * Not modelled (STUCK): spliterators, a load factor message for a non-integral float.
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;

public class WeakHashMap<K, V> extends AbstractMap<K, V> implements Map<K, V> {
    private static final int DEFAULT_INITIAL_CAPACITY = 16;
    private static final int MAXIMUM_CAPACITY = 1 << 30;
    private static final float DEFAULT_LOAD_FACTOR = 0.75f;

    Entry<K, V>[] table;
    private int size;
    private int threshold;
    private final float loadFactor;
    int modCount;

    @SuppressWarnings("unchecked")
    private Entry<K, V>[] newTable(int n) {
        return (Entry<K, V>[]) new Entry<?, ?>[n];
    }

    public WeakHashMap(int initialCapacity, float loadFactor) {
        if (initialCapacity < 0) throw new IllegalArgumentException("Illegal Initial Capacity: " + initialCapacity);
        if (initialCapacity > MAXIMUM_CAPACITY) initialCapacity = MAXIMUM_CAPACITY;
        if (loadFactor <= 0 || loadFactor != loadFactor) throw new IllegalArgumentException("Illegal Load factor: " + floatString(loadFactor));
        int capacity = HashMap.tableSizeFor(initialCapacity);
        table = newTable(capacity);
        this.loadFactor = loadFactor;
        threshold = (int) (capacity * loadFactor);
    }

    public WeakHashMap(int initialCapacity) {
        this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }

    public WeakHashMap() {
        this(DEFAULT_INITIAL_CAPACITY, DEFAULT_LOAD_FACTOR);
    }

    public WeakHashMap(Map<? extends K, ? extends V> m) {
        this(Math.max(ceilDiv075(sizeOf(m)), DEFAULT_INITIAL_CAPACITY), DEFAULT_LOAD_FACTOR);
        putAll(m);
    }

    private static int sizeOf(Map<?, ?> m) {
        if (m == null) throw TreeMap.invokeOnNull("java.util.Map.size()", "m");
        return m.size();
    }

    /** (int) Math.ceil(n / 0.75) for n >= 0 (exact: 4n/3 rounded up). */
    private static int ceilDiv075(int n) {
        return (int) ((4L * n + 2) / 3);
    }

    /** (int) Math.ceil(n / (double) lf) for n > 0, lf > 0. */
    private static int ceilDiv(int n, float lf) {
        double d = n / (double) lf;
        if (!(d < 2147483647.0)) return Integer.MAX_VALUE;
        int i = (int) d;
        return (i < d) ? i + 1 : i;
    }

    /** Float.toString for the integral values and NaN (message of the constructor), else STUCK. */
    static String floatString(float f) {
        if (f != f) return "NaN";
        if (f == 0) return (1 / f < 0) ? "-0.0" : "0.0";
        if (f == (int) f && f > -1.0e7f && f < 1.0e7f) return (int) f + ".0";
        if (f * 2 == (int) (f * 2) && f > -1.0e6f && f < 1.0e6f) {
            int h = (int) (f * 2);
            return (h < 0 && h / 2 == 0 ? "-" : "") + (h / 2) + ".5";
        }
        throw ModelStuck.unsupported("Float.toString of a load factor");
    }

    private static final Object NULL_KEY = new Object();

    private static Object maskNull(Object key) {
        return (key == null) ? NULL_KEY : key;
    }

    static Object unmaskNull(Object key) {
        return (key == NULL_KEY) ? null : key;
    }

    /** The JDK: the stored key (identity, as Reference.refersTo) or key.equals(stored). */
    private boolean matchesKey(Entry<K, V> e, Object key) {
        Object k = e.referent;
        if (k == key) return true;
        return k != null && key.equals(k);
    }

    final int hash(Object k) {
        int h = k.hashCode();
        h ^= (h >>> 20) ^ (h >>> 12);
        return h ^ (h >>> 7) ^ (h >>> 4);
    }

    private static int indexFor(int h, int length) {
        return h & (length - 1);
    }

    private Entry<K, V>[] getTable() {
        return table;
    }

    public int size() {
        return size;
    }

    public boolean isEmpty() {
        return size() == 0;
    }

    public V get(Object key) {
        Object k = maskNull(key);
        int h = hash(k);
        Entry<K, V>[] tab = getTable();
        int index = indexFor(h, tab.length);
        Entry<K, V> e = tab[index];
        while (e != null) {
            if (e.hash == h && matchesKey(e, k)) return e.value;
            e = e.next;
        }
        return null;
    }

    public boolean containsKey(Object key) {
        return getEntry(key) != null;
    }

    Entry<K, V> getEntry(Object key) {
        Object k = maskNull(key);
        int h = hash(k);
        Entry<K, V>[] tab = getTable();
        int index = indexFor(h, tab.length);
        Entry<K, V> e = tab[index];
        while (e != null && !(e.hash == h && matchesKey(e, k))) e = e.next;
        return e;
    }

    public V put(K key, V value) {
        Object k = maskNull(key);
        int h = hash(k);
        Entry<K, V>[] tab = getTable();
        int i = indexFor(h, tab.length);
        for (Entry<K, V> e = tab[i]; e != null; e = e.next) {
            if (h == e.hash && matchesKey(e, k)) {
                V oldValue = e.value;
                if (value != oldValue) e.value = value;
                return oldValue;
            }
        }
        modCount++;
        Entry<K, V> e = tab[i];
        tab[i] = new Entry<>(k, value, h, e);
        if (++size > threshold) resize(tab.length * 2);
        return null;
    }

    void resize(int newCapacity) {
        Entry<K, V>[] oldTable = getTable();
        int oldCapacity = oldTable.length;
        if (oldCapacity == MAXIMUM_CAPACITY) {
            threshold = Integer.MAX_VALUE;
            return;
        }
        Entry<K, V>[] newTable = newTable(newCapacity);
        transfer(oldTable, newTable);
        table = newTable;
        if (size >= threshold / 2) {
            threshold = (int) (newCapacity * loadFactor);
        } else {
            // only reachable after stale entries were dropped (never here)
            transfer(newTable, oldTable);
            table = oldTable;
        }
    }

    /** Moves every entry of src to the head of its bucket in dest (src bucket order). */
    private void transfer(Entry<K, V>[] src, Entry<K, V>[] dest) {
        for (int j = 0; j < src.length; ++j) {
            Entry<K, V> e = src[j];
            src[j] = null;
            while (e != null) {
                Entry<K, V> next = e.next;
                int i = indexFor(e.hash, dest.length);
                e.next = dest[i];
                dest[i] = e;
                e = next;
            }
        }
    }

    public void putAll(Map<? extends K, ? extends V> m) {
        if (m == null) throw TreeMap.invokeOnNull("java.util.Map.size()", "m");
        int numKeysToBeAdded = m.size();
        if (numKeysToBeAdded == 0) return;
        if (numKeysToBeAdded > threshold) {
            int targetCapacity = ceilDiv(numKeysToBeAdded, loadFactor);
            if (targetCapacity > MAXIMUM_CAPACITY) targetCapacity = MAXIMUM_CAPACITY;
            int newCapacity = table.length;
            while (newCapacity < targetCapacity) newCapacity <<= 1;
            if (newCapacity > table.length) resize(newCapacity);
        }
        for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) put(e.getKey(), e.getValue());
    }

    public V remove(Object key) {
        Object k = maskNull(key);
        int h = hash(k);
        Entry<K, V>[] tab = getTable();
        int i = indexFor(h, tab.length);
        Entry<K, V> prev = tab[i];
        Entry<K, V> e = prev;
        while (e != null) {
            Entry<K, V> next = e.next;
            if (h == e.hash && matchesKey(e, k)) {
                modCount++;
                size--;
                if (prev == e) tab[i] = next;
                else prev.next = next;
                return e.value;
            }
            prev = e;
            e = next;
        }
        return null;
    }

    boolean removeMapping(Object o) {
        if (!(o instanceof Map.Entry)) return false;
        Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
        Entry<K, V>[] tab = getTable();
        Object k = maskNull(entry.getKey());
        int h = hash(k);
        int i = indexFor(h, tab.length);
        Entry<K, V> prev = tab[i];
        Entry<K, V> e = prev;
        while (e != null) {
            Entry<K, V> next = e.next;
            if (h == e.hash && e.equals(entry)) {
                modCount++;
                size--;
                if (prev == e) tab[i] = next;
                else prev.next = next;
                return true;
            }
            prev = e;
            e = next;
        }
        return false;
    }

    public void clear() {
        modCount++;
        Entry<K, V>[] tab = table;
        for (int i = 0; i < tab.length; i++) tab[i] = null;
        size = 0;
    }

    public boolean containsValue(Object value) {
        if (value == null) return containsNullValue();
        Entry<K, V>[] tab = getTable();
        for (int i = tab.length; i-- > 0; ) {
            for (Entry<K, V> e = tab[i]; e != null; e = e.next) {
                if (value.equals(e.value)) return true;
            }
        }
        return false;
    }

    private boolean containsNullValue() {
        Entry<K, V>[] tab = getTable();
        for (int i = tab.length; i-- > 0; ) {
            for (Entry<K, V> e = tab[i]; e != null; e = e.next) {
                if (e.value == null) return true;
            }
        }
        return false;
    }

    /** An entry; the JDK's is a WeakReference to the (masked) key, here a strong one. */
    private static class Entry<K, V> implements Map.Entry<K, V> {
        final Object referent;
        V value;
        final int hash;
        Entry<K, V> next;

        Entry(Object key, V value, int hash, Entry<K, V> next) {
            this.referent = key;
            this.value = value;
            this.hash = hash;
            this.next = next;
        }

        @SuppressWarnings("unchecked")
        public K getKey() {
            return (K) WeakHashMap.unmaskNull(referent);
        }

        public V getValue() {
            return value;
        }

        public V setValue(V newValue) {
            V oldValue = value;
            value = newValue;
            return oldValue;
        }

        public boolean equals(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            K k1 = getKey();
            Object k2 = e.getKey();
            if (k1 == k2 || (k1 != null && k1.equals(k2))) {
                V v1 = getValue();
                Object v2 = e.getValue();
                if (v1 == v2 || (v1 != null && v1.equals(v2))) return true;
            }
            return false;
        }

        public int hashCode() {
            K k = getKey();
            V v = getValue();
            return (k == null ? 0 : k.hashCode()) ^ (v == null ? 0 : v.hashCode());
        }

        public String toString() {
            return getKey() + "=" + getValue();
        }
    }

    private abstract class HashIterator<T> implements Iterator<T> {
        private int index;
        private Entry<K, V> entry;
        private Entry<K, V> lastReturned;
        private int expectedModCount = modCount;
        private Object nextKey;
        private Object currentKey;

        HashIterator() {
            index = isEmpty() ? 0 : table.length;
        }

        public boolean hasNext() {
            Entry<K, V>[] t = table;
            while (nextKey == null) {
                Entry<K, V> e = entry;
                int i = index;
                while (e == null && i > 0) e = t[--i];
                entry = e;
                index = i;
                if (e == null) {
                    currentKey = null;
                    return false;
                }
                nextKey = e.referent;
                if (nextKey == null) entry = entry.next;
            }
            return true;
        }

        protected Entry<K, V> nextEntry() {
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            if (nextKey == null && !hasNext()) throw new NoSuchElementException();
            lastReturned = entry;
            entry = entry.next;
            currentKey = nextKey;
            nextKey = null;
            return lastReturned;
        }

        public void remove() {
            if (lastReturned == null) throw new IllegalStateException();
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            WeakHashMap.this.remove(currentKey);
            expectedModCount = modCount;
            lastReturned = null;
            currentKey = null;
        }
    }

    private class ValueIterator extends HashIterator<V> {
        public V next() {
            return nextEntry().value;
        }
    }

    private class KeyIterator extends HashIterator<K> {
        public K next() {
            return nextEntry().getKey();
        }
    }

    private class EntryIterator extends HashIterator<Map.Entry<K, V>> {
        public Map.Entry<K, V> next() {
            return nextEntry();
        }
    }

    private transient Set<Map.Entry<K, V>> entrySet;

    public Set<K> keySet() {
        Set<K> ks = keySet;
        if (ks == null) {
            ks = new KeySet();
            keySet = ks;
        }
        return ks;
    }

    private class KeySet extends AbstractSet<K> {
        public Iterator<K> iterator() {
            return new KeyIterator();
        }

        public int size() {
            return WeakHashMap.this.size();
        }

        public boolean contains(Object o) {
            return containsKey(o);
        }

        public boolean remove(Object o) {
            if (containsKey(o)) {
                WeakHashMap.this.remove(o);
                return true;
            }
            return false;
        }

        public void clear() {
            WeakHashMap.this.clear();
        }
    }

    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new Values();
            values = vs;
        }
        return vs;
    }

    private class Values extends AbstractCollection<V> {
        public Iterator<V> iterator() {
            return new ValueIterator();
        }

        public int size() {
            return WeakHashMap.this.size();
        }

        public boolean contains(Object o) {
            return containsValue(o);
        }

        public void clear() {
            WeakHashMap.this.clear();
        }
    }

    public Set<Map.Entry<K, V>> entrySet() {
        Set<Map.Entry<K, V>> es = entrySet;
        return es != null ? es : (entrySet = new EntrySet());
    }

    private class EntrySet extends AbstractSet<Map.Entry<K, V>> {
        public Iterator<Map.Entry<K, V>> iterator() {
            return new EntryIterator();
        }

        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            return getEntry(e.getKey()) != null && getEntry(e.getKey()).equals(e);
        }

        public boolean remove(Object o) {
            return removeMapping(o);
        }

        public int size() {
            return WeakHashMap.this.size();
        }

        public void clear() {
            WeakHashMap.this.clear();
        }

        private List<Map.Entry<K, V>> deepCopy() {
            List<Map.Entry<K, V>> list = new ArrayList<>(size());
            for (Map.Entry<K, V> e : this) list.add(new AbstractMap.SimpleEntry<>(e));
            return list;
        }

        public Object[] toArray() {
            return deepCopy().toArray();
        }

        public <T> T[] toArray(T[] a) {
            return deepCopy().toArray(a);
        }
    }

    @SuppressWarnings("unchecked")
    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        int expectedModCount = modCount;
        Entry<K, V>[] tab = getTable();
        for (Entry<K, V> entry : tab) {
            while (entry != null) {
                Object key = entry.referent;
                if (key != null) action.accept((K) WeakHashMap.unmaskNull(key), entry.value);
                entry = entry.next;
                if (expectedModCount != modCount) throw new ConcurrentModificationException();
            }
        }
    }

    @SuppressWarnings("unchecked")
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        int expectedModCount = modCount;
        Entry<K, V>[] tab = getTable();
        for (Entry<K, V> entry : tab) {
            while (entry != null) {
                Object key = entry.referent;
                if (key != null) entry.value = function.apply((K) WeakHashMap.unmaskNull(key), entry.value);
                entry = entry.next;
                if (expectedModCount != modCount) throw new ConcurrentModificationException();
            }
        }
    }
}

/*
 * rocq-jvm model of java.util.IdentityHashMap (clean-room, Apache-2.0).
 *
 * Keys and values alternate in one table with linear probing (step 2), a null key is stored as a
 * private marker, removal closes the probe sequence (Knuth's algorithm R), and the table doubles
 * when 3 * size exceeds its length: the JDK's layout, so iteration order, as in the JDK, depends
 * only on System.identityHashCode (an environment value of the machine, jenv.j_ihash). Iterator
 * removal that moves an unvisited entry before the cursor switches the iterator to a copy of the
 * rest of the table, as in the JDK, so each entry is still visited exactly once.
 * Not modelled (STUCK): serialization, spliterators.
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;

public class IdentityHashMap<K, V> extends AbstractMap<K, V> implements Map<K, V>, java.io.Serializable, Cloneable {
    private static final int DEFAULT_CAPACITY = 32;
    private static final int MINIMUM_CAPACITY = 4;
    private static final int MAXIMUM_CAPACITY = 1 << 29;

    transient Object[] table;
    int size;
    transient int modCount;

    static final Object NULL_KEY = new Object();

    private static Object maskNull(Object key) {
        return (key == null ? NULL_KEY : key);
    }

    static Object unmaskNull(Object key) {
        return (key == NULL_KEY ? null : key);
    }

    public IdentityHashMap() {
        init(DEFAULT_CAPACITY);
    }

    public IdentityHashMap(int expectedMaxSize) {
        if (expectedMaxSize < 0) throw new IllegalArgumentException("expectedMaxSize is negative: " + expectedMaxSize);
        init(capacity(expectedMaxSize));
    }

    private static int capacity(int expectedMaxSize) {
        return (expectedMaxSize > MAXIMUM_CAPACITY / 3) ? MAXIMUM_CAPACITY
            : (expectedMaxSize <= 2 * MINIMUM_CAPACITY / 3) ? MINIMUM_CAPACITY
            : Integer.highestOneBit(expectedMaxSize + (expectedMaxSize << 1));
    }

    private void init(int initCapacity) {
        table = new Object[2 * initCapacity];
    }

    public IdentityHashMap(Map<? extends K, ? extends V> m) {
        this(expected(m));
        putAll(m);
    }

    private static int expected(Map<?, ?> m) {
        if (m == null) throw TreeMap.invokeOnNull("java.util.Map.size()", "m");
        return (int) ((1 + m.size()) * 1.1);
    }

    public int size() {
        return size;
    }

    public boolean isEmpty() {
        return size == 0;
    }

    private static int hash(Object x, int length) {
        int h = System.identityHashCode(x);
        return ((h << 1) - (h << 8)) & (length - 1);
    }

    private static int nextKeyIndex(int i, int len) {
        return (i + 2 < len ? i + 2 : 0);
    }

    @SuppressWarnings("unchecked")
    public V get(Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) return (V) tab[i + 1];
            if (item == null) return null;
            i = nextKeyIndex(i, len);
        }
    }

    public boolean containsKey(Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) return true;
            if (item == null) return false;
            i = nextKeyIndex(i, len);
        }
    }

    public boolean containsValue(Object value) {
        Object[] tab = table;
        for (int i = 1; i < tab.length; i += 2) {
            if (tab[i] == value && tab[i - 1] != null) return true;
        }
        return false;
    }

    private boolean containsMapping(Object key, Object value) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) return tab[i + 1] == value;
            if (item == null) return false;
            i = nextKeyIndex(i, len);
        }
    }

    public V put(K key, V value) {
        final Object k = maskNull(key);
        for (;;) {
            final Object[] tab = table;
            final int len = tab.length;
            int i = hash(k, len);
            Object item;
            boolean retry = false;
            while ((item = tab[i]) != null) {
                if (item == k) {
                    @SuppressWarnings("unchecked")
                    V oldValue = (V) tab[i + 1];
                    tab[i + 1] = value;
                    return oldValue;
                }
                i = nextKeyIndex(i, len);
            }
            final int s = size + 1;
            if (s + (s << 1) > len && resize(len)) continue;
            modCount++;
            tab[i] = k;
            tab[i + 1] = value;
            size = s;
            return null;
        }
    }

    private boolean resize(int newCapacity) {
        int newLength = newCapacity * 2;
        Object[] oldTable = table;
        int oldLength = oldTable.length;
        if (oldLength == 2 * MAXIMUM_CAPACITY) {
            if (size == MAXIMUM_CAPACITY - 1) throw new IllegalStateException("Capacity exhausted.");
            return false;
        }
        if (oldLength >= newLength) return false;
        Object[] newTable = new Object[newLength];
        for (int j = 0; j < oldLength; j += 2) {
            Object key = oldTable[j];
            if (key != null) {
                Object value = oldTable[j + 1];
                oldTable[j] = null;
                oldTable[j + 1] = null;
                int i = hash(key, newLength);
                while (newTable[i] != null) i = nextKeyIndex(i, newLength);
                newTable[i] = key;
                newTable[i + 1] = value;
            }
        }
        table = newTable;
        return true;
    }

    public void putAll(Map<? extends K, ? extends V> m) {
        if (m == null) throw TreeMap.invokeOnNull("java.util.Map.size()", "m");
        int n = m.size();
        if (n == 0) return;
        if (n > size) resize(capacity(n));
        for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) put(e.getKey(), e.getValue());
    }

    public V remove(Object key) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) {
                modCount++;
                size--;
                @SuppressWarnings("unchecked")
                V oldValue = (V) tab[i + 1];
                tab[i + 1] = null;
                tab[i] = null;
                closeDeletion(i);
                return oldValue;
            }
            if (item == null) return null;
            i = nextKeyIndex(i, len);
        }
    }

    private boolean removeMapping(Object key, Object value) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) {
                if (tab[i + 1] != value) return false;
                modCount++;
                size--;
                tab[i] = null;
                tab[i + 1] = null;
                closeDeletion(i);
                return true;
            }
            if (item == null) return false;
            i = nextKeyIndex(i, len);
        }
    }

    /** Moves later entries of the probe sequence into the freed slot d where needed. */
    private void closeDeletion(int d) {
        Object[] tab = table;
        int len = tab.length;
        Object item;
        for (int i = nextKeyIndex(d, len); (item = tab[i]) != null; i = nextKeyIndex(i, len)) {
            int r = hash(item, len);
            if ((i < r && (r <= d || d <= i)) || (r <= d && d <= i)) {
                tab[d] = item;
                tab[d + 1] = tab[i + 1];
                tab[i] = null;
                tab[i + 1] = null;
                d = i;
            }
        }
    }

    public void clear() {
        modCount++;
        Object[] tab = table;
        for (int i = 0; i < tab.length; i++) tab[i] = null;
        size = 0;
    }

    public boolean equals(Object o) {
        if (o == this) {
            return true;
        } else if (o instanceof IdentityHashMap) {
            IdentityHashMap<?, ?> m = (IdentityHashMap<?, ?>) o;
            if (m.size() != size) return false;
            Object[] tab = m.table;
            for (int i = 0; i < tab.length; i += 2) {
                Object k = tab[i];
                if (k != null && !containsMapping(k, tab[i + 1])) return false;
            }
            return true;
        } else if (o instanceof Map) {
            Map<?, ?> m = (Map<?, ?>) o;
            return entrySet().equals(m.entrySet());
        } else {
            return false;
        }
    }

    public int hashCode() {
        int result = 0;
        Object[] tab = table;
        for (int i = 0; i < tab.length; i += 2) {
            Object key = tab[i];
            if (key != null) {
                Object k = unmaskNull(key);
                result += System.identityHashCode(k) ^ System.identityHashCode(tab[i + 1]);
            }
        }
        return result;
    }

    public Object clone() {
        try {
            IdentityHashMap<?, ?> m = (IdentityHashMap<?, ?>) super.clone();
            m.entrySet = null;
            Object[] t = new Object[table.length];
            System.arraycopy(table, 0, t, 0, table.length);
            m.table = t;
            return m;
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e);
        }
    }

    private abstract class IdentityHashMapIterator<T> implements Iterator<T> {
        int index = (size != 0 ? 0 : table.length);
        int expectedModCount = modCount;
        int lastReturnedIndex = -1;
        boolean indexValid;
        Object[] traversalTable = table;

        public boolean hasNext() {
            Object[] tab = traversalTable;
            for (int i = index; i < tab.length; i += 2) {
                Object key = tab[i];
                if (key != null) {
                    index = i;
                    return indexValid = true;
                }
            }
            index = tab.length;
            return false;
        }

        protected int nextIndex() {
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            if (!indexValid && !hasNext()) throw new NoSuchElementException();
            indexValid = false;
            lastReturnedIndex = index;
            index += 2;
            return lastReturnedIndex;
        }

        public void remove() {
            if (lastReturnedIndex == -1) throw new IllegalStateException();
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            expectedModCount = ++modCount;
            int deletedSlot = lastReturnedIndex;
            lastReturnedIndex = -1;
            index = deletedSlot;
            indexValid = false;
            Object[] tab = traversalTable;
            int len = tab.length;
            int d = deletedSlot;
            Object key = tab[d];
            tab[d] = null;
            tab[d + 1] = null;
            if (tab != IdentityHashMap.this.table) {
                // iterating over a copy: remove from the real table
                IdentityHashMap.this.remove(key);
                expectedModCount = modCount;
                return;
            }
            size--;
            Object item;
            for (int i = nextKeyIndex(d, len); (item = tab[i]) != null; i = nextKeyIndex(i, len)) {
                int r = hash(item, len);
                if ((i < r && (r <= d || d <= i)) || (r <= d && d <= i)) {
                    // an unvisited entry moving before the cursor: continue over a copy
                    if (i < deletedSlot && d >= deletedSlot && traversalTable == IdentityHashMap.this.table) {
                        int remaining = len - deletedSlot;
                        Object[] newTable = new Object[remaining];
                        System.arraycopy(tab, deletedSlot, newTable, 0, remaining);
                        traversalTable = newTable;
                        index = 0;
                    }
                    tab[d] = item;
                    tab[d + 1] = tab[i + 1];
                    tab[i] = null;
                    tab[i + 1] = null;
                    d = i;
                }
            }
        }
    }

    private class KeyIterator extends IdentityHashMapIterator<K> {
        @SuppressWarnings("unchecked")
        public K next() {
            return (K) unmaskNull(traversalTable[nextIndex()]);
        }
    }

    private class ValueIterator extends IdentityHashMapIterator<V> {
        @SuppressWarnings("unchecked")
        public V next() {
            return (V) traversalTable[nextIndex() + 1];
        }
    }

    private class EntryIterator extends IdentityHashMapIterator<Map.Entry<K, V>> {
        private Entry lastReturnedEntry;

        public Map.Entry<K, V> next() {
            lastReturnedEntry = new Entry(nextIndex());
            return lastReturnedEntry;
        }

        public void remove() {
            lastReturnedIndex = ((null == lastReturnedEntry) ? -1 : lastReturnedEntry.index);
            super.remove();
            lastReturnedEntry.index = lastReturnedIndex;
            lastReturnedEntry = null;
        }

        /** A view of a table slot of the iterator ("Entry was removed" once removed). */
        private class Entry implements Map.Entry<K, V> {
            private int index;

            private Entry(int index) {
                this.index = index;
            }

            @SuppressWarnings("unchecked")
            public K getKey() {
                checkIndexForEntryUse();
                return (K) unmaskNull(traversalTable[index]);
            }

            @SuppressWarnings("unchecked")
            public V getValue() {
                checkIndexForEntryUse();
                return (V) traversalTable[index + 1];
            }

            @SuppressWarnings("unchecked")
            public V setValue(V value) {
                checkIndexForEntryUse();
                V oldValue = (V) traversalTable[index + 1];
                traversalTable[index + 1] = value;
                if (traversalTable != IdentityHashMap.this.table) put((K) traversalTable[index], value);
                return oldValue;
            }

            public boolean equals(Object o) {
                if (index < 0) return super.equals(o);
                if (!(o instanceof Map.Entry)) return false;
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                return e.getKey() == unmaskNull(traversalTable[index]) && e.getValue() == traversalTable[index + 1];
            }

            public int hashCode() {
                if (lastReturnedIndex < 0) return super.hashCode();
                return System.identityHashCode(unmaskNull(traversalTable[index])) ^ System.identityHashCode(traversalTable[index + 1]);
            }

            public String toString() {
                if (index < 0) return super.toString();
                return unmaskNull(traversalTable[index]) + "=" + traversalTable[index + 1];
            }

            private void checkIndexForEntryUse() {
                if (index < 0) throw new IllegalStateException("Entry was removed");
            }
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

    /** toArray of a view: the table order, CME if the size does not match. */
    private Object[] viewToArray(Object[] a, int what) {
        int expectedModCount = modCount;
        int size = size();
        if (a == null) throw new NullPointerException("Cannot read the array length because \"a\" is null");
        if (a.length < size) a = AbstractCollection.newArrayLike(a, size);
        Object[] tab = table;
        int ti = 0;
        for (int si = 0; si < tab.length; si += 2) {
            Object key = tab[si];
            if (key != null) {
                if (ti >= size) throw new ConcurrentModificationException();
                a[ti++] = what == 0 ? unmaskNull(key) : what == 1 ? tab[si + 1] : new AbstractMap.SimpleEntry<>(unmaskNull(key), tab[si + 1]);
            }
        }
        if (ti < size || expectedModCount != modCount) throw new ConcurrentModificationException();
        if (ti < a.length) a[ti] = null;
        return a;
    }

    private class KeySet extends AbstractSet<K> {
        public Iterator<K> iterator() {
            return new KeyIterator();
        }

        public int size() {
            return size;
        }

        public boolean contains(Object o) {
            return containsKey(o);
        }

        public boolean remove(Object o) {
            int oldSize = size;
            IdentityHashMap.this.remove(o);
            return size != oldSize;
        }

        public boolean removeAll(Collection<?> c) {
            if (c == null) throw new NullPointerException();
            boolean modified = false;
            for (Iterator<K> i = iterator(); i.hasNext(); ) {
                if (c.contains(i.next())) {
                    i.remove();
                    modified = true;
                }
            }
            return modified;
        }

        public void clear() {
            IdentityHashMap.this.clear();
        }

        public int hashCode() {
            int result = 0;
            for (K key : this) result += System.identityHashCode(key);
            return result;
        }

        public Object[] toArray() {
            return toArray(new Object[0]);
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            return (T[]) viewToArray(a, 0);
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
            return size;
        }

        public boolean contains(Object o) {
            return containsValue(o);
        }

        public boolean remove(Object o) {
            for (Iterator<V> i = iterator(); i.hasNext(); ) {
                if (i.next() == o) {
                    i.remove();
                    return true;
                }
            }
            return false;
        }

        public void clear() {
            IdentityHashMap.this.clear();
        }

        public Object[] toArray() {
            return toArray(new Object[0]);
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            return (T[]) viewToArray(a, 1);
        }
    }

    public Set<Map.Entry<K, V>> entrySet() {
        Set<Map.Entry<K, V>> es = entrySet;
        if (es != null) return es;
        return entrySet = new EntrySet();
    }

    private class EntrySet extends AbstractSet<Map.Entry<K, V>> {
        public Iterator<Map.Entry<K, V>> iterator() {
            return new EntryIterator();
        }

        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
            return containsMapping(entry.getKey(), entry.getValue());
        }

        public boolean remove(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
            return removeMapping(entry.getKey(), entry.getValue());
        }

        public int size() {
            return size;
        }

        public void clear() {
            IdentityHashMap.this.clear();
        }

        public boolean removeAll(Collection<?> c) {
            if (c == null) throw new NullPointerException();
            boolean modified = false;
            for (Iterator<Map.Entry<K, V>> i = iterator(); i.hasNext(); ) {
                if (c.contains(i.next())) {
                    i.remove();
                    modified = true;
                }
            }
            return modified;
        }

        public Object[] toArray() {
            return toArray(new Object[0]);
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            return (T[]) viewToArray(a, 2);
        }
    }

    @SuppressWarnings("unchecked")
    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        int expectedModCount = modCount;
        Object[] t = table;
        for (int index = 0; index < t.length; index += 2) {
            Object k = t[index];
            if (k != null) action.accept((K) unmaskNull(k), (V) t[index + 1]);
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
        }
    }

    @SuppressWarnings("unchecked")
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        int expectedModCount = modCount;
        Object[] t = table;
        for (int index = 0; index < t.length; index += 2) {
            Object k = t[index];
            if (k != null) t[index + 1] = function.apply((K) unmaskNull(k), (V) t[index + 1]);
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
        }
    }

    public boolean remove(Object key, Object value) {
        return removeMapping(key, value);
    }

    public boolean replace(K key, V oldValue, V newValue) {
        Object k = maskNull(key);
        Object[] tab = table;
        int len = tab.length;
        int i = hash(k, len);
        while (true) {
            Object item = tab[i];
            if (item == k) {
                if (tab[i + 1] != oldValue) return false;
                tab[i + 1] = newValue;
                return true;
            }
            if (item == null) return false;
            i = nextKeyIndex(i, len);
        }
    }
}

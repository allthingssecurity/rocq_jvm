/*
 * rocq-jvm model of java.util.Hashtable (clean-room, Apache-2.0).
 *
 * The JDK's table: bucket (hash & 0x7FFFFFFF) % length, new entries at the head of a bucket,
 * rehash to 2 * length + 1 when count >= threshold before an insertion, iteration and
 * Enumerations from the last bucket to the first, so iteration order, toString, keys() and
 * elements() are the JDK's. Null keys are rejected by key.hashCode() (the NullPointerException
 * carries HotSpot's helpful message), null values by explicit checks. The key, value and entry
 * views are synchronized on the Hashtable (as Collections.synchronizedSet(view, this) in the
 * JDK). Not modelled (STUCK): serialization, spliterators and streams of the views.
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

public class Hashtable<K, V> extends Dictionary<K, V> implements Map<K, V>, Cloneable, java.io.Serializable {
    private transient Entry<?, ?>[] table;
    private transient int count;
    private int threshold;
    private float loadFactor;
    private transient int modCount = 0;

    private static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;

    public Hashtable(int initialCapacity, float loadFactor) {
        if (initialCapacity < 0) throw new IllegalArgumentException("Illegal Capacity: " + initialCapacity);
        if (loadFactor <= 0 || loadFactor != loadFactor) throw new IllegalArgumentException("Illegal Load: " + WeakHashMap.floatString(loadFactor));
        if (initialCapacity == 0) initialCapacity = 1;
        this.loadFactor = loadFactor;
        table = new Entry<?, ?>[initialCapacity];
        threshold = thresholdOf(initialCapacity, loadFactor);
    }

    /** (int) Math.min(capacity * loadFactor, MAX_ARRAY_SIZE + 1) in float arithmetic. */
    private static int thresholdOf(int capacity, float loadFactor) {
        float f = capacity * loadFactor;
        float lim = (float) (MAX_ARRAY_SIZE + 1);
        return (int) (f < lim ? f : lim);
    }

    public Hashtable(int initialCapacity) {
        this(initialCapacity, 0.75f);
    }

    public Hashtable() {
        this(11, 0.75f);
    }

    public Hashtable(Map<? extends K, ? extends V> t) {
        this(Math.max(2 * sizeOf(t), 11), 0.75f);
        putAll(t);
    }

    private static int sizeOf(Map<?, ?> t) {
        if (t == null) throw TreeMap.invokeOnNull("java.util.Map.size()", "t");
        return t.size();
    }

    /** Properties: no table of its own. */
    Hashtable(Void dummy) {
    }

    /** key.hashCode(), with HotSpot's message for a null key. */
    private static int hashOf(Object key) {
        if (key == null) throw TreeMap.invokeOnNull("Object.hashCode()", "key");
        return key.hashCode();
    }

    public synchronized int size() {
        return count;
    }

    public synchronized boolean isEmpty() {
        return count == 0;
    }

    public synchronized Enumeration<K> keys() {
        return this.<K>getEnumeration(KEYS);
    }

    public synchronized Enumeration<V> elements() {
        return this.<V>getEnumeration(VALUES);
    }

    public synchronized boolean contains(Object value) {
        if (value == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        for (int i = tab.length; i-- > 0; ) {
            for (Entry<?, ?> e = tab[i]; e != null; e = e.next) {
                if (e.value.equals(value)) return true;
            }
        }
        return false;
    }

    public boolean containsValue(Object value) {
        return contains(value);
    }

    public synchronized boolean containsKey(Object key) {
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        for (Entry<?, ?> e = tab[index]; e != null; e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) return true;
        }
        return false;
    }

    @SuppressWarnings("unchecked")
    public synchronized V get(Object key) {
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        for (Entry<?, ?> e = tab[index]; e != null; e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) return (V) e.value;
        }
        return null;
    }

    @SuppressWarnings("unchecked")
    protected void rehash() {
        int oldCapacity = table.length;
        Entry<?, ?>[] oldMap = table;
        int newCapacity = (oldCapacity << 1) + 1;
        if (newCapacity - MAX_ARRAY_SIZE > 0) {
            if (oldCapacity == MAX_ARRAY_SIZE) return;
            newCapacity = MAX_ARRAY_SIZE;
        }
        Entry<?, ?>[] newMap = new Entry<?, ?>[newCapacity];
        modCount++;
        threshold = thresholdOf(newCapacity, loadFactor);
        table = newMap;
        for (int i = oldCapacity; i-- > 0; ) {
            for (Entry<K, V> old = (Entry<K, V>) oldMap[i]; old != null; ) {
                Entry<K, V> e = old;
                old = old.next;
                int index = (e.hash & 0x7FFFFFFF) % newCapacity;
                e.next = (Entry<K, V>) newMap[index];
                newMap[index] = e;
            }
        }
    }

    private void addEntry(int hash, K key, V value, int index) {
        Entry<?, ?>[] tab = table;
        if (count >= threshold) {
            rehash();
            tab = table;
            hash = key.hashCode();
            index = (hash & 0x7FFFFFFF) % tab.length;
        }
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        tab[index] = new Entry<>(hash, key, value, e);
        count++;
        modCount++;
    }

    public synchronized V put(K key, V value) {
        if (value == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> entry = (Entry<K, V>) tab[index];
        for (; entry != null; entry = entry.next) {
            if ((entry.hash == hash) && entry.key.equals(key)) {
                V old = entry.value;
                entry.value = value;
                return old;
            }
        }
        addEntry(hash, key, value, index);
        return null;
    }

    public synchronized V remove(Object key) {
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        for (Entry<K, V> prev = null; e != null; prev = e, e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) {
                if (prev != null) prev.next = e.next;
                else tab[index] = e.next;
                modCount++;
                count--;
                V oldValue = e.value;
                e.value = null;
                return oldValue;
            }
        }
        return null;
    }

    public synchronized void putAll(Map<? extends K, ? extends V> t) {
        if (t == null) throw TreeMap.invokeOnNull("java.util.Map.entrySet()", "t");
        for (Map.Entry<? extends K, ? extends V> e : t.entrySet()) put(e.getKey(), e.getValue());
    }

    public synchronized void clear() {
        Entry<?, ?>[] tab = table;
        for (int index = tab.length; --index >= 0; ) tab[index] = null;
        modCount++;
        count = 0;
    }

    public synchronized Object clone() {
        Hashtable<?, ?> t = cloneHashtable();
        t.table = new Entry<?, ?>[table.length];
        for (int i = table.length; i-- > 0; ) {
            t.table[i] = (table[i] != null) ? (Entry<?, ?>) table[i].clone() : null;
        }
        t.keySet = null;
        t.entrySet = null;
        t.values = null;
        t.modCount = 0;
        return t;
    }

    final Hashtable<?, ?> cloneHashtable() {
        try {
            return (Hashtable<?, ?>) super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e);
        }
    }

    public synchronized String toString() {
        int max = size() - 1;
        if (max == -1) return "{}";
        StringBuilder sb = new StringBuilder();
        Iterator<Map.Entry<K, V>> it = entrySet().iterator();
        sb.append('{');
        for (int i = 0; ; i++) {
            Map.Entry<K, V> e = it.next();
            K key = e.getKey();
            V value = e.getValue();
            sb.append(key == this ? "(this Map)" : key.toString());
            sb.append('=');
            sb.append(value == this ? "(this Map)" : value.toString());
            if (i == max) return sb.append('}').toString();
            sb.append(", ");
        }
    }

    private <T> Enumeration<T> getEnumeration(int type) {
        if (count == 0) return emptyEnumeration();
        return new Enumerator<>(type, false);
    }

    private <T> Iterator<T> getIterator(int type) {
        if (count == 0) return Collections.emptyIterator();
        return new Enumerator<>(type, true);
    }

    private transient volatile Set<K> keySet;
    private transient volatile Set<Map.Entry<K, V>> entrySet;
    private transient volatile Collection<V> values;

    public Set<K> keySet() {
        if (keySet == null) keySet = new SyncSet<>(new KeySet(), this);
        return keySet;
    }

    private class KeySet extends AbstractSet<K> {
        public Iterator<K> iterator() {
            return getIterator(KEYS);
        }

        public int size() {
            return count;
        }

        public boolean contains(Object o) {
            return containsKey(o);
        }

        public boolean remove(Object o) {
            return Hashtable.this.remove(o) != null;
        }

        public void clear() {
            Hashtable.this.clear();
        }
    }

    public Set<Map.Entry<K, V>> entrySet() {
        if (entrySet == null) entrySet = new SyncSet<>(new EntrySet(), this);
        return entrySet;
    }

    private class EntrySet extends AbstractSet<Map.Entry<K, V>> {
        public Iterator<Map.Entry<K, V>> iterator() {
            return getIterator(ENTRIES);
        }

        public boolean add(Map.Entry<K, V> o) {
            return super.add(o);
        }

        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
            Object key = entry.getKey();
            Entry<?, ?>[] tab = table;
            int hash = hashOf(key);
            int index = (hash & 0x7FFFFFFF) % tab.length;
            for (Entry<?, ?> e = tab[index]; e != null; e = e.next) {
                if (e.hash == hash && e.equals(entry)) return true;
            }
            return false;
        }

        public boolean remove(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> entry = (Map.Entry<?, ?>) o;
            Object key = entry.getKey();
            Entry<?, ?>[] tab = table;
            int hash = hashOf(key);
            int index = (hash & 0x7FFFFFFF) % tab.length;
            @SuppressWarnings("unchecked")
            Entry<K, V> e = (Entry<K, V>) tab[index];
            for (Entry<K, V> prev = null; e != null; prev = e, e = e.next) {
                if (e.hash == hash && e.equals(entry)) {
                    if (prev != null) prev.next = e.next;
                    else tab[index] = e.next;
                    e.value = null;
                    modCount++;
                    count--;
                    return true;
                }
            }
            return false;
        }

        public int size() {
            return count;
        }

        public void clear() {
            Hashtable.this.clear();
        }
    }

    public Collection<V> values() {
        if (values == null) values = new SyncCollection<>(new ValueCollection(), this);
        return values;
    }

    private class ValueCollection extends AbstractCollection<V> {
        public Iterator<V> iterator() {
            return getIterator(VALUES);
        }

        public int size() {
            return count;
        }

        public boolean contains(Object o) {
            return containsValue(o);
        }

        public void clear() {
            Hashtable.this.clear();
        }
    }

    public synchronized boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Map)) return false;
        Map<?, ?> t = (Map<?, ?>) o;
        if (t.size() != size()) return false;
        try {
            for (Map.Entry<K, V> e : entrySet()) {
                K key = e.getKey();
                V value = e.getValue();
                if (value == null) {
                    if (!(t.get(key) == null && t.containsKey(key))) return false;
                } else {
                    if (!value.equals(t.get(key))) return false;
                }
            }
        } catch (ClassCastException | NullPointerException unused) {
            return false;
        }
        return true;
    }

    /** The sum of the entry hash codes; 0 for a table already being hashed (a self-reference). */
    public synchronized int hashCode() {
        int h = 0;
        if (count == 0 || loadFactor < 0) return h;
        loadFactor = -loadFactor;   // hashCode computation in progress
        Entry<?, ?>[] tab = table;
        for (Entry<?, ?> entry : tab) {
            while (entry != null) {
                h += entry.hashCode();
                entry = entry.next;
            }
        }
        loadFactor = -loadFactor;
        return h;
    }

    public synchronized V getOrDefault(Object key, V defaultValue) {
        V result = get(key);
        return (null == result) ? defaultValue : result;
    }

    @SuppressWarnings("unchecked")
    public synchronized void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        final int expectedModCount = modCount;
        Entry<?, ?>[] tab = table;
        for (Entry<?, ?> entry : tab) {
            while (entry != null) {
                action.accept((K) entry.key, (V) entry.value);
                entry = entry.next;
                if (expectedModCount != modCount) throw new ConcurrentModificationException();
            }
        }
    }

    @SuppressWarnings("unchecked")
    public synchronized void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        final int expectedModCount = modCount;
        Entry<K, V>[] tab = (Entry<K, V>[]) table;
        for (Entry<K, V> entry : tab) {
            while (entry != null) {
                V v = function.apply(entry.key, entry.value);
                if (v == null) throw new NullPointerException();
                entry.value = v;
                entry = entry.next;
                if (expectedModCount != modCount) throw new ConcurrentModificationException();
            }
        }
    }

    public synchronized V putIfAbsent(K key, V value) {
        if (value == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> entry = (Entry<K, V>) tab[index];
        for (; entry != null; entry = entry.next) {
            if ((entry.hash == hash) && entry.key.equals(key)) {
                V old = entry.value;
                if (old == null) entry.value = value;
                return old;
            }
        }
        addEntry(hash, key, value, index);
        return null;
    }

    public synchronized boolean remove(Object key, Object value) {
        if (value == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        for (Entry<K, V> prev = null; e != null; prev = e, e = e.next) {
            if ((e.hash == hash) && e.key.equals(key) && e.value.equals(value)) {
                if (prev != null) prev.next = e.next;
                else tab[index] = e.next;
                e.value = null;
                modCount++;
                count--;
                return true;
            }
        }
        return false;
    }

    public synchronized boolean replace(K key, V oldValue, V newValue) {
        if (oldValue == null || newValue == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        for (; e != null; e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) {
                if (e.value.equals(oldValue)) {
                    e.value = newValue;
                    return true;
                }
                return false;
            }
        }
        return false;
    }

    public synchronized V replace(K key, V value) {
        if (value == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        for (; e != null; e = e.next) {
            if ((e.hash == hash) && e.key.equals(key)) {
                V oldValue = e.value;
                e.value = value;
                return oldValue;
            }
        }
        return null;
    }

    public synchronized V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        for (; e != null; e = e.next) {
            if (e.hash == hash && e.key.equals(key)) return e.value;
        }
        int mc = modCount;
        V newValue = mappingFunction.apply(key);
        if (mc != modCount) throw new ConcurrentModificationException();
        if (newValue != null) addEntry(hash, key, newValue, index);
        return newValue;
    }

    public synchronized V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        for (Entry<K, V> prev = null; e != null; prev = e, e = e.next) {
            if (e.hash == hash && e.key.equals(key)) {
                int mc = modCount;
                V newValue = remappingFunction.apply(key, e.value);
                if (mc != modCount) throw new ConcurrentModificationException();
                if (newValue == null) {
                    if (prev != null) prev.next = e.next;
                    else tab[index] = e.next;
                    modCount = mc + 1;
                    count--;
                } else {
                    e.value = newValue;
                }
                return newValue;
            }
        }
        return null;
    }

    public synchronized V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        for (Entry<K, V> prev = null; e != null; prev = e, e = e.next) {
            if (e.hash == hash && (e.key == key || e.key.equals(key))) {
                int mc = modCount;
                V newValue = remappingFunction.apply(key, e.value);
                if (mc != modCount) throw new ConcurrentModificationException();
                if (newValue == null) {
                    if (prev != null) prev.next = e.next;
                    else tab[index] = e.next;
                    modCount = mc + 1;
                    count--;
                } else {
                    e.value = newValue;
                }
                return newValue;
            }
        }
        int mc = modCount;
        V newValue = remappingFunction.apply(key, null);
        if (mc != modCount) throw new ConcurrentModificationException();
        if (newValue != null) addEntry(hash, key, newValue, index);
        return newValue;
    }

    public synchronized V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        Entry<?, ?>[] tab = table;
        int hash = hashOf(key);
        int index = (hash & 0x7FFFFFFF) % tab.length;
        @SuppressWarnings("unchecked")
        Entry<K, V> e = (Entry<K, V>) tab[index];
        for (Entry<K, V> prev = null; e != null; prev = e, e = e.next) {
            if (e.hash == hash && e.key.equals(key)) {
                int mc = modCount;
                V newValue = remappingFunction.apply(e.value, value);
                if (mc != modCount) throw new ConcurrentModificationException();
                if (newValue == null) {
                    if (prev != null) prev.next = e.next;
                    else tab[index] = e.next;
                    modCount = mc + 1;
                    count--;
                } else {
                    e.value = newValue;
                }
                return newValue;
            }
        }
        if (value != null) addEntry(hash, key, value, index);
        return value;
    }

    private static class Entry<K, V> implements Map.Entry<K, V> {
        final int hash;
        final K key;
        V value;
        Entry<K, V> next;

        protected Entry(int hash, K key, V value, Entry<K, V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        @SuppressWarnings("unchecked")
        protected Object clone() {
            return new Entry<>(hash, key, value, (next == null ? null : (Entry<K, V>) next.clone()));
        }

        public K getKey() {
            return key;
        }

        public V getValue() {
            return value;
        }

        public V setValue(V value) {
            if (value == null) throw new NullPointerException();
            V oldValue = this.value;
            this.value = value;
            return oldValue;
        }

        public boolean equals(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            return (key == null ? e.getKey() == null : key.equals(e.getKey()))
                && (value == null ? e.getValue() == null : value.equals(e.getValue()));
        }

        public int hashCode() {
            return hash ^ (value == null ? 0 : value.hashCode());
        }

        public String toString() {
            return key.toString() + "=" + value.toString();
        }
    }

    private static final int KEYS = 0;
    private static final int VALUES = 1;
    private static final int ENTRIES = 2;

    /** Enumeration (keys/elements) and fail-fast Iterator (views) over a snapshot of the table
     *  reference, from the last bucket to the first. */
    private class Enumerator<T> implements Enumeration<T>, Iterator<T> {
        final Entry<?, ?>[] table = Hashtable.this.table;
        int index = table.length;
        Entry<?, ?> entry;
        Entry<?, ?> lastReturned;
        final int type;
        final boolean iterator;
        protected int expectedModCount = Hashtable.this.modCount;

        Enumerator(int type, boolean iterator) {
            this.type = type;
            this.iterator = iterator;
        }

        public boolean hasMoreElements() {
            Entry<?, ?> e = entry;
            int i = index;
            Entry<?, ?>[] t = table;
            while (e == null && i > 0) e = t[--i];
            entry = e;
            index = i;
            return e != null;
        }

        @SuppressWarnings("unchecked")
        public T nextElement() {
            Entry<?, ?> et = entry;
            int i = index;
            Entry<?, ?>[] t = table;
            while (et == null && i > 0) et = t[--i];
            entry = et;
            index = i;
            if (et != null) {
                Entry<?, ?> e = lastReturned = entry;
                entry = e.next;
                return type == KEYS ? (T) e.key : (type == VALUES ? (T) e.value : (T) e);
            }
            throw new NoSuchElementException("Hashtable Enumerator");
        }

        public boolean hasNext() {
            return hasMoreElements();
        }

        public T next() {
            if (Hashtable.this.modCount != expectedModCount) throw new ConcurrentModificationException();
            return nextElement();
        }

        public void remove() {
            if (!iterator) throw new UnsupportedOperationException();
            if (lastReturned == null) throw new IllegalStateException("Hashtable Enumerator");
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            synchronized (Hashtable.this) {
                Entry<?, ?>[] tab = Hashtable.this.table;
                int index = (lastReturned.hash & 0x7FFFFFFF) % tab.length;
                @SuppressWarnings("unchecked")
                Entry<K, V> e = (Entry<K, V>) tab[index];
                for (Entry<K, V> prev = null; e != null; prev = e, e = e.next) {
                    if (e == lastReturned) {
                        if (prev == null) tab[index] = e.next;
                        else prev.next = e.next;
                        expectedModCount++;
                        lastReturned = null;
                        Hashtable.this.modCount++;
                        Hashtable.this.count--;
                        return;
                    }
                }
                throw new ConcurrentModificationException();
            }
        }
    }

    // ---- helpers (Collections.emptyEnumeration, Collections.enumeration, and the synchronized
    //      views of Collections.synchronizedSet/Collection(view, mutex)) ----

    @SuppressWarnings("unchecked")
    static <T> Enumeration<T> emptyEnumeration() {
        return (Enumeration<T>) EmptyEnumeration.EMPTY;
    }

    private static final class EmptyEnumeration<E> implements Enumeration<E> {
        static final EmptyEnumeration<Object> EMPTY = new EmptyEnumeration<>();

        public boolean hasMoreElements() {
            return false;
        }

        public E nextElement() {
            throw new NoSuchElementException();
        }

        public Iterator<E> asIterator() {
            return Collections.emptyIterator();
        }
    }

    /** Collections.enumeration(c). */
    static <T> Enumeration<T> enumeration(Collection<T> c) {
        final Iterator<T> i = c.iterator();
        return new Enumeration<T>() {
            public boolean hasMoreElements() {
                return i.hasNext();
            }

            public T nextElement() {
                return i.next();
            }
        };
    }

    static class SyncCollection<E> implements Collection<E>, java.io.Serializable {
        final Collection<E> c;
        final Object mutex;

        SyncCollection(Collection<E> c, Object mutex) {
            this.c = c;
            this.mutex = mutex;
        }

        public int size() {
            synchronized (mutex) {
                return c.size();
            }
        }

        public boolean isEmpty() {
            synchronized (mutex) {
                return c.isEmpty();
            }
        }

        public boolean contains(Object o) {
            synchronized (mutex) {
                return c.contains(o);
            }
        }

        public Object[] toArray() {
            synchronized (mutex) {
                return c.toArray();
            }
        }

        public <T> T[] toArray(T[] a) {
            synchronized (mutex) {
                return c.toArray(a);
            }
        }

        public Iterator<E> iterator() {
            return c.iterator();   // must be synchronized by the user
        }

        public boolean add(E e) {
            synchronized (mutex) {
                return c.add(e);
            }
        }

        public boolean remove(Object o) {
            synchronized (mutex) {
                return c.remove(o);
            }
        }

        public boolean containsAll(Collection<?> coll) {
            synchronized (mutex) {
                return c.containsAll(coll);
            }
        }

        public boolean addAll(Collection<? extends E> coll) {
            synchronized (mutex) {
                return c.addAll(coll);
            }
        }

        public boolean removeAll(Collection<?> coll) {
            synchronized (mutex) {
                return c.removeAll(coll);
            }
        }

        public boolean retainAll(Collection<?> coll) {
            synchronized (mutex) {
                return c.retainAll(coll);
            }
        }

        public void clear() {
            synchronized (mutex) {
                c.clear();
            }
        }

        public String toString() {
            synchronized (mutex) {
                return c.toString();
            }
        }

        public void forEach(java.util.function.Consumer<? super E> consumer) {
            synchronized (mutex) {
                c.forEach(consumer);
            }
        }

        public boolean removeIf(java.util.function.Predicate<? super E> filter) {
            synchronized (mutex) {
                return c.removeIf(filter);
            }
        }

        public java.util.stream.Stream<E> stream() {
            throw ModelStuck.unsupported("Hashtable view: stream");
        }
    }

    static class SyncSet<E> extends SyncCollection<E> implements Set<E> {
        SyncSet(Set<E> s, Object mutex) {
            super(s, mutex);
        }

        public boolean equals(Object o) {
            if (this == o) return true;
            synchronized (mutex) {
                return c.equals(o);
            }
        }

        public int hashCode() {
            synchronized (mutex) {
                return c.hashCode();
            }
        }
    }
}

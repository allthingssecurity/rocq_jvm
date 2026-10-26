/*
 * rocq-jvm model of java.util.AbstractMap (clean-room, Apache-2.0).  Every operation is
 * written in terms of entrySet(), as the Javadoc specifies.
 */
package java.util;

public abstract class AbstractMap<K, V> implements Map<K, V> {
    /** Views, created on first use and then returned again (identity is observable). */
    transient Set<K> keySet;
    transient Collection<V> values;

    protected AbstractMap() {
    }

    static boolean eq(Object a, Object b) {
        return a == b || (a != null && a.equals(b));
    }

    static int hashOf(Object o) {
        return o == null ? 0 : o.hashCode();
    }

    public int size() {
        return entrySet().size();
    }

    public boolean isEmpty() {
        return size() == 0;
    }

    public boolean containsValue(Object value) {
        Iterator<Entry<K, V>> it = entrySet().iterator();
        if (value == null) {
            while (it.hasNext()) {
                if (it.next().getValue() == null) return true;
            }
        } else {
            while (it.hasNext()) {
                if (value.equals(it.next().getValue())) return true;
            }
        }
        return false;
    }

    public boolean containsKey(Object key) {
        Iterator<Entry<K, V>> it = entrySet().iterator();
        if (key == null) {
            while (it.hasNext()) {
                if (it.next().getKey() == null) return true;
            }
        } else {
            while (it.hasNext()) {
                if (key.equals(it.next().getKey())) return true;
            }
        }
        return false;
    }

    public V get(Object key) {
        Iterator<Entry<K, V>> it = entrySet().iterator();
        if (key == null) {
            while (it.hasNext()) {
                Entry<K, V> e = it.next();
                if (e.getKey() == null) return e.getValue();
            }
        } else {
            while (it.hasNext()) {
                Entry<K, V> e = it.next();
                if (key.equals(e.getKey())) return e.getValue();
            }
        }
        return null;
    }

    public V put(K key, V value) {
        throw new UnsupportedOperationException();
    }

    public V remove(Object key) {
        Iterator<Entry<K, V>> it = entrySet().iterator();
        Entry<K, V> found = null;
        if (key == null) {
            while (found == null && it.hasNext()) {
                Entry<K, V> e = it.next();
                if (e.getKey() == null) found = e;
            }
        } else {
            while (found == null && it.hasNext()) {
                Entry<K, V> e = it.next();
                if (key.equals(e.getKey())) found = e;
            }
        }
        V old = null;
        if (found != null) {
            old = found.getValue();
            it.remove();
        }
        return old;
    }

    public void putAll(Map<? extends K, ? extends V> m) {
        for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) put(e.getKey(), e.getValue());
    }

    public void clear() {
        entrySet().clear();
    }

    public Set<K> keySet() {
        Set<K> ks = keySet;
        if (ks == null) {
            ks = new KeyView();
            keySet = ks;
        }
        return ks;
    }

    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new ValueView();
            values = vs;
        }
        return vs;
    }

    /** JDK: a shallow copy whose key and value views are recreated. */
    protected Object clone() throws CloneNotSupportedException {
        AbstractMap<?, ?> result = (AbstractMap<?, ?>) super.clone();
        result.keySet = null;
        result.values = null;
        return result;
    }

    public abstract Set<Entry<K, V>> entrySet();

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Map)) return false;
        Map<?, ?> m = (Map<?, ?>) o;
        if (m.size() != size()) return false;
        try {
            for (Entry<K, V> e : entrySet()) {
                K key = e.getKey();
                V value = e.getValue();
                if (value == null) {
                    if (!(m.get(key) == null && m.containsKey(key))) return false;
                } else {
                    if (!value.equals(m.get(key))) return false;
                }
            }
        } catch (ClassCastException | NullPointerException unused) {
            return false;
        }
        return true;
    }

    public int hashCode() {
        int h = 0;
        for (Entry<K, V> e : entrySet()) h += e.hashCode();
        return h;
    }

    /** Javadoc: "{k1=v1, k2=v2}"; elements' toString() called directly (see AbstractCollection). */
    public String toString() {
        Iterator<Entry<K, V>> it = entrySet().iterator();
        if (!it.hasNext()) return "{}";
        StringBuilder sb = new StringBuilder();
        sb.append('{');
        for (;;) {
            Entry<K, V> e = it.next();
            K key = e.getKey();
            V value = e.getValue();
            sb.append(key == this ? "(this Map)" : (key == null ? "null" : key.toString()));
            sb.append('=');
            sb.append(value == this ? "(this Map)" : (value == null ? "null" : value.toString()));
            if (!it.hasNext()) return sb.append('}').toString();
            sb.append(',').append(' ');
        }
    }

    private final class KeyView extends AbstractSet<K> {
        public Iterator<K> iterator() {
            return new Iterator<K>() {
                private final Iterator<Entry<K, V>> i = entrySet().iterator();

                public boolean hasNext() {
                    return i.hasNext();
                }

                public K next() {
                    return i.next().getKey();
                }

                public void remove() {
                    i.remove();
                }
            };
        }

        public int size() {
            return AbstractMap.this.size();
        }

        public boolean isEmpty() {
            return AbstractMap.this.isEmpty();
        }

        public void clear() {
            AbstractMap.this.clear();
        }

        public boolean contains(Object k) {
            return AbstractMap.this.containsKey(k);
        }
    }

    private final class ValueView extends AbstractCollection<V> {
        public Iterator<V> iterator() {
            return new Iterator<V>() {
                private final Iterator<Entry<K, V>> i = entrySet().iterator();

                public boolean hasNext() {
                    return i.hasNext();
                }

                public V next() {
                    return i.next().getValue();
                }

                public void remove() {
                    i.remove();
                }
            };
        }

        public int size() {
            return AbstractMap.this.size();
        }

        public boolean isEmpty() {
            return AbstractMap.this.isEmpty();
        }

        public void clear() {
            AbstractMap.this.clear();
        }

        public boolean contains(Object v) {
            return AbstractMap.this.containsValue(v);
        }
    }

    /** Javadoc: a mutable key-value pair; equals/hashCode as in Map.Entry. */
    public static class SimpleEntry<K, V> implements Entry<K, V>, java.io.Serializable {
        private final K key;
        private V value;

        public SimpleEntry(K key, V value) {
            this.key = key;
            this.value = value;
        }

        public SimpleEntry(Entry<? extends K, ? extends V> entry) {
            this.key = entry.getKey();
            this.value = entry.getValue();
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
            return (key == null ? "null" : key.toString()) + "=" + (value == null ? "null" : value.toString());
        }
    }

    /** Javadoc: an immutable key-value pair; setValue throws UnsupportedOperationException. */
    public static class SimpleImmutableEntry<K, V> implements Entry<K, V>, java.io.Serializable {
        private final K key;
        private final V value;

        public SimpleImmutableEntry(K key, V value) {
            this.key = key;
            this.value = value;
        }

        public SimpleImmutableEntry(Entry<? extends K, ? extends V> entry) {
            this.key = entry.getKey();
            this.value = entry.getValue();
        }

        public K getKey() {
            return key;
        }

        public V getValue() {
            return value;
        }

        public V setValue(V value) {
            throw new UnsupportedOperationException();
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
            return (key == null ? "null" : key.toString()) + "=" + (value == null ? "null" : value.toString());
        }
    }
}

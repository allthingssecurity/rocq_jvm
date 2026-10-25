/*
 * rocq-jvm model of java.util.Map and Map.Entry (clean-room, Apache-2.0; the default methods
 * follow the "implementation requirements" paragraphs of the Javadoc).
 * Map.of/ofEntries/entry/copyOf: ImmutableCollections.
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

public interface Map<K, V> {
    int size();
    boolean isEmpty();
    boolean containsKey(Object key);
    boolean containsValue(Object value);
    V get(Object key);
    V put(K key, V value);
    V remove(Object key);
    void putAll(Map<? extends K, ? extends V> m);
    void clear();
    Set<K> keySet();
    Collection<V> values();
    Set<Map.Entry<K, V>> entrySet();
    boolean equals(Object o);
    int hashCode();

    interface Entry<K, V> {
        K getKey();
        V getValue();
        V setValue(V value);
        boolean equals(Object o);
        int hashCode();

        static <K extends Comparable<? super K>, V> Comparator<Map.Entry<K, V>> comparingByKey() {
            return (Comparator<Map.Entry<K, V>>) (c1, c2) -> c1.getKey().compareTo(c2.getKey());
        }

        static <K, V extends Comparable<? super V>> Comparator<Map.Entry<K, V>> comparingByValue() {
            return (Comparator<Map.Entry<K, V>>) (c1, c2) -> c1.getValue().compareTo(c2.getValue());
        }

        static <K, V> Comparator<Map.Entry<K, V>> comparingByKey(Comparator<? super K> cmp) {
            Objects.requireNonNull(cmp);
            return (Comparator<Map.Entry<K, V>>) (c1, c2) -> cmp.compare(c1.getKey(), c2.getKey());
        }

        static <K, V> Comparator<Map.Entry<K, V>> comparingByValue(Comparator<? super V> cmp) {
            Objects.requireNonNull(cmp);
            return (Comparator<Map.Entry<K, V>>) (c1, c2) -> cmp.compare(c1.getValue(), c2.getValue());
        }

        @SuppressWarnings("unchecked")
        static <K, V> Map.Entry<K, V> copyOf(Map.Entry<? extends K, ? extends V> e) {
            Objects.requireNonNull(e);
            if (e instanceof KeyValueHolder) {
                return (Map.Entry<K, V>) e;
            } else {
                return Map.entry(e.getKey(), e.getValue());
            }
        }
    }

    private static boolean eq(Object a, Object b) {
        return a == b || (a != null && a.equals(b));
    }

    default V getOrDefault(Object key, V defaultValue) {
        V v = get(key);
        if (v != null || containsKey(key)) return v;
        return defaultValue;
    }

    default void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        for (Map.Entry<K, V> entry : entrySet()) {
            K k;
            V v;
            try {
                k = entry.getKey();
                v = entry.getValue();
            } catch (IllegalStateException ise) {
                throw new ConcurrentModificationException(ise);
            }
            action.accept(k, v);
        }
    }

    default void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        for (Map.Entry<K, V> entry : entrySet()) {
            K k;
            V v;
            try {
                k = entry.getKey();
                v = entry.getValue();
            } catch (IllegalStateException ise) {
                throw new ConcurrentModificationException(ise);
            }
            v = function.apply(k, v);
            try {
                entry.setValue(v);
            } catch (IllegalStateException ise) {
                throw new ConcurrentModificationException(ise);
            }
        }
    }

    default V putIfAbsent(K key, V value) {
        V v = get(key);
        if (v == null) v = put(key, value);
        return v;
    }

    default boolean remove(Object key, Object value) {
        Object cur = get(key);
        if (!eq(cur, value) || (cur == null && !containsKey(key))) return false;
        remove(key);
        return true;
    }

    default boolean replace(K key, V oldValue, V newValue) {
        Object cur = get(key);
        if (!eq(cur, oldValue) || (cur == null && !containsKey(key))) return false;
        put(key, newValue);
        return true;
    }

    default V replace(K key, V value) {
        V cur = get(key);
        if (cur != null || containsKey(key)) cur = put(key, value);
        return cur;
    }

    default V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null) throw new NullPointerException();
        V v = get(key);
        if (v == null) {
            V nv = mappingFunction.apply(key);
            if (nv != null) {
                put(key, nv);
                return nv;
            }
        }
        return v;
    }

    default V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        V old = get(key);
        if (old != null) {
            V nv = remappingFunction.apply(key, old);
            if (nv != null) {
                put(key, nv);
                return nv;
            }
            remove(key);
        }
        return null;
    }

    default V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        V old = get(key);
        V nv = remappingFunction.apply(key, old);
        if (nv == null) {
            if (old != null || containsKey(key)) remove(key);
            return null;
        }
        put(key, nv);
        return nv;
    }

    default V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        if (value == null) throw new NullPointerException();
        V old = get(key);
        V nv = (old == null) ? value : remappingFunction.apply(old, value);
        if (nv == null) remove(key);
        else put(key, nv);
        return nv;
    }

    @SuppressWarnings("unchecked")
    static <K, V> Map<K, V> of() {
        return (Map<K, V>) ImmutableCollections.EMPTY_MAP;
    }
    static <K, V> Map<K, V> of(K k1, V v1) {
        return new ImmutableCollections.Map1<>(k1, v1);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2, k3, v3);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2, k3, v3, k4, v4);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6, k7, v7);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6, k7, v7, k8, v8);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8, K k9, V v9) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6, k7, v7, k8, v8, k9, v9);
    }
    static <K, V> Map<K, V> of(K k1, V v1, K k2, V v2, K k3, V v3, K k4, V v4, K k5, V v5, K k6, V v6, K k7, V v7, K k8, V v8, K k9, V v9, K k10, V v10) {
        return new ImmutableCollections.MapN<>(k1, v1, k2, v2, k3, v3, k4, v4, k5, v5, k6, v6, k7, v7, k8, v8, k9, v9, k10, v10);
    }

    @SafeVarargs
    @SuppressWarnings("unchecked")
    static <K, V> Map<K, V> ofEntries(Entry<? extends K, ? extends V>... entries) {
        if (entries == null) throw ImmutableCollections.lengthOfNull("entries");
        if (entries.length == 0) {
            return (Map<K, V>) ImmutableCollections.EMPTY_MAP;
        } else if (entries.length == 1) {
            if (entries[0] == null) throw ImmutableCollections.invokeOnNull("java.util.Map$Entry.getKey()", "entries[0]");
            return new ImmutableCollections.Map1<>(entries[0].getKey(), entries[0].getValue());
        } else {
            Object[] kva = new Object[entries.length << 1];
            int a = 0;
            for (Entry<? extends K, ? extends V> entry : entries) {
                if (entry == null) throw ImmutableCollections.invokeOnNull("java.util.Map$Entry.getKey()", "entry");
                kva[a++] = entry.getKey();
                kva[a++] = entry.getValue();
            }
            return new ImmutableCollections.MapN<>(kva);
        }
    }

    static <K, V> Entry<K, V> entry(K k, V v) {
        return new KeyValueHolder<>(k, v);
    }

    @SuppressWarnings({"rawtypes", "unchecked"})
    static <K, V> Map<K, V> copyOf(Map<? extends K, ? extends V> map) {
        if (map instanceof ImmutableCollections.AbstractImmutableMap) {
            return (Map<K, V>) map;
        } else if (map == null) {
            throw ImmutableCollections.invokeOnNull("java.util.Map.isEmpty()", "map");
        } else if (map.isEmpty()) {
            return Map.of();
        } else {
            return (Map<K, V>) Map.ofEntries(map.entrySet().toArray(new Entry[0]));
        }
    }
}

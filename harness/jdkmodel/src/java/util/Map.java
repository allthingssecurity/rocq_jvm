/*
 * rocq-jvm model of java.util.Map and Map.Entry (clean-room, Apache-2.0; the default methods
 * follow the "implementation requirements" paragraphs of the Javadoc).
 * Not modelled: Map.of/ofEntries/entry/copyOf, Entry.comparingBy* (calls are STUCK).
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
}

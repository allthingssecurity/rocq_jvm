/*
 * rocq-jvm model of java.util.concurrent.ConcurrentMap (clean-room, Apache-2.0).
 * The default methods follow the "implementation requirements" paragraphs of the Javadoc
 * (they differ from Map's: a null value means absent, and they retry instead of failing).
 */
package java.util.concurrent;

import java.util.Map;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

public interface ConcurrentMap<K, V> extends Map<K, V> {
    V putIfAbsent(K key, V value);

    boolean remove(Object key, Object value);

    boolean replace(K key, V oldValue, V newValue);

    V replace(K key, V value);

    default V getOrDefault(Object key, V defaultValue) {
        V v;
        return ((v = get(key)) != null) ? v : defaultValue;
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
                continue;   // the entry is no longer in the map
            }
            action.accept(k, v);
        }
    }

    default void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        forEach((k, v) -> {
            while (!replace(k, v, function.apply(k, v))) {
                if ((v = get(k)) == null) break;
            }
        });
    }

    default V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null) throw new NullPointerException();
        V oldValue, newValue;
        return ((oldValue = get(key)) == null && (newValue = mappingFunction.apply(key)) != null
                && (oldValue = putIfAbsent(key, newValue)) == null) ? newValue : oldValue;
    }

    default V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        for (V oldValue; (oldValue = get(key)) != null; ) {
            V newValue = remappingFunction.apply(key, oldValue);
            if ((newValue == null) ? remove(key, oldValue) : replace(key, oldValue, newValue)) return newValue;
        }
        return null;
    }

    default V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        retry:
        for (;;) {
            V oldValue = get(key);
            haveOldValue:
            for (;;) {
                V newValue = remappingFunction.apply(key, oldValue);
                if (newValue != null) {
                    if (oldValue != null) {
                        if (replace(key, oldValue, newValue)) return newValue;
                    } else if ((oldValue = putIfAbsent(key, newValue)) == null) {
                        return newValue;
                    } else {
                        continue haveOldValue;
                    }
                } else if (oldValue == null || remove(key, oldValue)) {
                    return null;
                }
                continue retry;
            }
        }
    }

    default V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null || value == null) throw new NullPointerException();
        retry:
        for (;;) {
            V oldValue = get(key);
            haveOldValue:
            for (;;) {
                if (oldValue != null) {
                    V newValue = remappingFunction.apply(oldValue, value);
                    if (newValue != null) {
                        if (replace(key, oldValue, newValue)) return newValue;
                    } else if (remove(key, oldValue)) {
                        return null;
                    }
                    continue retry;
                } else {
                    if ((oldValue = putIfAbsent(key, value)) == null) return value;
                    continue haveOldValue;
                }
            }
        }
    }
}

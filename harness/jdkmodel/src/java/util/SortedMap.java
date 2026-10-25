/* rocq-jvm model of java.util.SortedMap (clean-room, Apache-2.0). */
package java.util;

public interface SortedMap<K, V> extends Map<K, V> {
    Comparator<? super K> comparator();
    SortedMap<K, V> subMap(K fromKey, K toKey);
    SortedMap<K, V> headMap(K toKey);
    SortedMap<K, V> tailMap(K fromKey);
    K firstKey();
    K lastKey();
}

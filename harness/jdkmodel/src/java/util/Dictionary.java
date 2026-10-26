/*
 * rocq-jvm model of java.util.Dictionary (clean-room, Apache-2.0): the abstract superclass of
 * Hashtable.
 */
package java.util;

public abstract class Dictionary<K, V> {
    public Dictionary() {
    }

    public abstract int size();

    public abstract boolean isEmpty();

    public abstract Enumeration<K> keys();

    public abstract Enumeration<V> elements();

    public abstract V get(Object key);

    public abstract V put(K key, V value);

    public abstract V remove(Object key);
}

/*
 * rocq-jvm model of java.util.LinkedHashMap (clean-room, Apache-2.0; from the Javadoc).
 * A HashMap whose entries are also on a doubly linked list in insertion order, or in access
 * order (accessOrder = true: get/getOrDefault/put/putIfAbsent/replace/compute/merge of an
 * existing key moves it to the end and counts as a structural modification).  After an
 * insertion, removeEldestEntry(eldest) is asked whether to remove the first entry.
 * Iteration follows the list.  SequencedMap methods (JDK 21) are not modelled.
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;

public class LinkedHashMap<K, V> extends HashMap<K, V> implements Map<K, V> {
    transient HashMap.Node<K, V> head;
    transient HashMap.Node<K, V> tail;
    final boolean accessOrder;

    public LinkedHashMap(int initialCapacity, float loadFactor) {
        super(initialCapacity, loadFactor);
        accessOrder = false;
    }

    public LinkedHashMap(int initialCapacity) {
        super(initialCapacity);
        accessOrder = false;
    }

    public LinkedHashMap() {
        super();
        accessOrder = false;
    }

    public LinkedHashMap(Map<? extends K, ? extends V> m) {
        super();
        accessOrder = false;
        putMapEntries(m, false);
    }

    public LinkedHashMap(int initialCapacity, float loadFactor, boolean accessOrder) {
        super(initialCapacity, loadFactor);
        this.accessOrder = accessOrder;
    }

    private void linkLast(Node<K, V> p) {
        Node<K, V> last = tail;
        tail = p;
        if (last == null) {
            head = p;
        } else {
            p.before = last;
            last.after = p;
        }
    }

    /** dst takes src's place on the list. */
    private void transferLinks(Node<K, V> src, Node<K, V> dst) {
        Node<K, V> b = dst.before = src.before;
        Node<K, V> a = dst.after = src.after;
        if (b == null) head = dst;
        else b.after = dst;
        if (a == null) tail = dst;
        else a.before = dst;
    }

    Node<K, V> newNode(int h, K key, V value, Node<K, V> next) {
        Node<K, V> p = new Node<>(h, key, value, next);
        linkLast(p);
        return p;
    }

    Node<K, V> replacementNode(Node<K, V> p, Node<K, V> next) {
        Node<K, V> q = new Node<>(p.hash, p.key, p.value, next);
        transferLinks(p, q);
        return q;
    }

    TreeNode<K, V> newTreeNode(int h, K key, V value, Node<K, V> next) {
        TreeNode<K, V> p = new TreeNode<>(h, key, value, next);
        linkLast(p);
        return p;
    }

    TreeNode<K, V> replacementTreeNode(Node<K, V> p, Node<K, V> next) {
        TreeNode<K, V> q = new TreeNode<>(p.hash, p.key, p.value, next);
        transferLinks(p, q);
        return q;
    }

    void afterNodeRemoval(Node<K, V> p) {
        Node<K, V> b = p.before, a = p.after;
        p.before = p.after = null;
        if (b == null) head = a;
        else b.after = a;
        if (a == null) tail = b;
        else a.before = b;
    }

    void afterNodeInsertion(boolean evict) {
        Node<K, V> first;
        if (evict && (first = head) != null && removeEldestEntry(first)) {
            K key = first.key;
            removeNode(hash(key), key, null, false, true);
        }
    }

    void afterNodeAccess(Node<K, V> p) {
        Node<K, V> last = tail;
        if (accessOrder && last != p) {
            Node<K, V> b = p.before, a = p.after;
            p.after = null;
            if (b == null) head = a;
            else b.after = a;
            if (a != null) a.before = b;
            else last = b;
            if (last == null) {
                head = p;
            } else {
                p.before = last;
                last.after = p;
            }
            tail = p;
            modCount++;
        }
    }

    public boolean containsValue(Object value) {
        for (Node<K, V> e = head; e != null; e = e.after) {
            V v = e.value;
            if (v == value || (value != null && value.equals(v))) return true;
        }
        return false;
    }

    public V get(Object key) {
        Node<K, V> e = getNode(key);
        if (e == null) return null;
        if (accessOrder) afterNodeAccess(e);
        return e.value;
    }

    public V getOrDefault(Object key, V defaultValue) {
        Node<K, V> e = getNode(key);
        if (e == null) return defaultValue;
        if (accessOrder) afterNodeAccess(e);
        return e.value;
    }

    public void clear() {
        super.clear();
        head = tail = null;
    }

    protected boolean removeEldestEntry(Map.Entry<K, V> eldest) {
        return false;
    }

    public Set<K> keySet() {
        Set<K> ks = keySet;
        if (ks == null) {
            ks = new LinkedKeySet();
            keySet = ks;
        }
        return ks;
    }

    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new LinkedValues();
            values = vs;
        }
        return vs;
    }

    public Set<Map.Entry<K, V>> entrySet() {
        Set<Map.Entry<K, V>> es = entrySet;
        if (es == null) {
            es = new LinkedEntrySet();
            entrySet = es;
        }
        return es;
    }

    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        int mc = modCount;
        for (Node<K, V> e = head; e != null; e = e.after) action.accept(e.key, e.value);
        if (modCount != mc) throw new ConcurrentModificationException();
    }

    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        int mc = modCount;
        for (Node<K, V> e = head; e != null; e = e.after) e.value = function.apply(e.key, e.value);
        if (modCount != mc) throw new ConcurrentModificationException();
    }

    final class LinkedKeySet extends AbstractSet<K> {
        public int size() {
            return size;
        }

        public void clear() {
            LinkedHashMap.this.clear();
        }

        public Iterator<K> iterator() {
            return new LinkedKeyIterator();
        }

        public boolean contains(Object o) {
            return containsKey(o);
        }

        public boolean remove(Object key) {
            return removeNode(hash(key), key, null, false, true) != null;
        }

        public void forEach(Consumer<? super K> action) {
            if (action == null) throw new NullPointerException();
            int mc = modCount;
            for (Node<K, V> e = head; e != null; e = e.after) action.accept(e.key);
            if (modCount != mc) throw new ConcurrentModificationException();
        }
    }

    final class LinkedValues extends AbstractCollection<V> {
        public int size() {
            return size;
        }

        public void clear() {
            LinkedHashMap.this.clear();
        }

        public Iterator<V> iterator() {
            return new LinkedValueIterator();
        }

        public boolean contains(Object o) {
            return containsValue(o);
        }

        public void forEach(Consumer<? super V> action) {
            if (action == null) throw new NullPointerException();
            int mc = modCount;
            for (Node<K, V> e = head; e != null; e = e.after) action.accept(e.value);
            if (modCount != mc) throw new ConcurrentModificationException();
        }
    }

    final class LinkedEntrySet extends AbstractSet<Map.Entry<K, V>> {
        public int size() {
            return size;
        }

        public void clear() {
            LinkedHashMap.this.clear();
        }

        public Iterator<Map.Entry<K, V>> iterator() {
            return new LinkedEntryIterator();
        }

        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            Object key = e.getKey();
            Node<K, V> candidate = getNode(key);
            return candidate != null && candidate.equals(e);
        }

        public boolean remove(Object o) {
            if (o instanceof Map.Entry) {
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }

        public void forEach(Consumer<? super Map.Entry<K, V>> action) {
            if (action == null) throw new NullPointerException();
            int mc = modCount;
            for (Node<K, V> e = head; e != null; e = e.after) action.accept(e);
            if (modCount != mc) throw new ConcurrentModificationException();
        }
    }

    abstract class LinkedHashIterator {
        Node<K, V> next;
        Node<K, V> current;
        int expectedModCount;

        LinkedHashIterator() {
            next = head;
            expectedModCount = modCount;
            current = null;
        }

        public final boolean hasNext() {
            return next != null;
        }

        final Node<K, V> nextNode() {
            Node<K, V> e = next;
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            if (e == null) throw new NoSuchElementException();
            current = e;
            next = e.after;
            return e;
        }

        public final void remove() {
            Node<K, V> p = current;
            if (p == null) throw new IllegalStateException();
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            current = null;
            removeNode(p.hash, p.key, null, false, false);
            expectedModCount = modCount;
        }
    }

    final class LinkedKeyIterator extends LinkedHashIterator implements Iterator<K> {
        public K next() {
            return nextNode().getKey();
        }
    }

    final class LinkedValueIterator extends LinkedHashIterator implements Iterator<V> {
        public V next() {
            return nextNode().value;
        }
    }

    final class LinkedEntryIterator extends LinkedHashIterator implements Iterator<Map.Entry<K, V>> {
        public Map.Entry<K, V> next() {
            return nextNode();
        }
    }
}

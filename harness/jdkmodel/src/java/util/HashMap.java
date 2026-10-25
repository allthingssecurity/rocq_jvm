/*
 * rocq-jvm model of java.util.HashMap (clean-room, Apache-2.0).
 *
 * Written from the Javadoc and from the documented algorithm of the JDK HashMap, NOT from
 * OpenJDK source.  The observable behaviour (return values, exceptions, iteration order,
 * fail-fast ConcurrentModificationException) is checked against JDK 21 by differential tests
 * (harness/jdkmodel/tests).  Algorithm facts used:
 * - hash(key) = 0 for null, else h ^ (h >>> 16) with h = key.hashCode(); bin index =
 *   hash & (table length - 1); table lengths are powers of two, at most 2^30;
 * - the table is allocated on first insertion: length 16 (threshold 12) for new HashMap(),
 *   else the power of two >= the requested initial capacity (at least 1); threshold =
 *   (int)(length * loadFactor), doubled together with the length once length >= 16;
 * - a bin is a singly linked list, new entries appended at the tail (put) or prepended at the
 *   head (computeIfAbsent/compute/merge); a resize splits each bin into the entries that keep
 *   their index and those that move up by the old length, both in their previous order;
 * - a list bin that reaches 8 entries plus one more (put) or 7 plus one (compute*) is turned
 *   into a red-black tree ("tree bin") if the table has at least 64 slots, otherwise the table
 *   is resized; tree bins are ordered by hash, then compareTo for keys of the same class
 *   C implements Comparable<C>, then a tie-break by class name and identity hash code; the
 *   tree root is moved to the front of the bin's list after every insertion/deletion, and new
 *   tree entries are linked into the list right after their tree parent; a tree bin with too
 *   few nodes (6 or less after a split, or a degenerate shape on removal) becomes a list again;
 * - iteration walks the table slots in index order and each bin's list in order.
 *
 * Limitations (the machine is STUCK, never wrong): the identity-hash-code tie-break (keys with
 * equal hash codes, same class, not Comparable, in a tree bin), Comparable key classes other
 * than String and the boxes (needs the generic signature), clone, tables larger than the
 * machine's array bound, keySet/values/entrySet spliterator/stream.
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

public class HashMap<K, V> extends AbstractMap<K, V> implements Map<K, V>, Cloneable, java.io.Serializable {
    static final int MAX_CAPACITY = 1 << 30;
    static final int TREEIFY_BIN = 8;
    static final int UNTREEIFY_BIN = 6;
    static final int MIN_TREE_TABLE = 64;

    /** An entry.  before/after are used only by LinkedHashMap (its insertion/access list). */
    static class Node<K, V> implements Map.Entry<K, V> {
        final int hash;
        final K key;
        V value;
        Node<K, V> next;
        Node<K, V> before;
        Node<K, V> after;

        Node(int hash, K key, V value, Node<K, V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        public final K getKey() {
            return key;
        }

        public final V getValue() {
            return value;
        }

        public final String toString() {
            return (key == null ? "null" : key.toString()) + "=" + (value == null ? "null" : value.toString());
        }

        public final int hashCode() {
            return hashOf(key) ^ hashOf(value);
        }

        public final V setValue(V newValue) {
            V old = value;
            value = newValue;
            return old;
        }

        public final boolean equals(Object o) {
            if (o == this) return true;
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            return eq(key, e.getKey()) && eq(value, e.getValue());
        }
    }

    static int hash(Object key) {
        if (key == null) return 0;
        int h = key.hashCode();
        return h ^ (h >>> 16);
    }

    /** Smallest power of two >= cap (1 for cap <= 1), cap <= MAX_CAPACITY. */
    static int tableSizeFor(int cap) {
        int n = 1;
        while (n < cap && n < MAX_CAPACITY) n <<= 1;
        return n;
    }

    transient Node<K, V>[] table;
    transient Set<Map.Entry<K, V>> entrySet;
    transient int size;
    transient int modCount;
    /** Next size at which to resize; before the table exists: its initial length (0 = 16). */
    int threshold;
    final float loadFactor;

    public HashMap(int initialCapacity, float loadFactor) {
        if (initialCapacity < 0) throw new IllegalArgumentException();
        if (initialCapacity > MAX_CAPACITY) initialCapacity = MAX_CAPACITY;
        if (loadFactor <= 0 || loadFactor != loadFactor) throw new IllegalArgumentException();
        this.loadFactor = loadFactor;
        this.threshold = tableSizeFor(initialCapacity);
    }

    public HashMap(int initialCapacity) {
        this(initialCapacity, 0.75f);
    }

    public HashMap() {
        this.loadFactor = 0.75f;
    }

    public HashMap(Map<? extends K, ? extends V> m) {
        this.loadFactor = 0.75f;
        putMapEntries(m, false);
    }

    final void putMapEntries(Map<? extends K, ? extends V> m, boolean evict) {
        int s = m.size();
        if (s > 0) {
            if (table == null) {
                // pre-size: ceil(s / loadFactor) entries without a resize
                double d = s / (double) loadFactor;
                int t;
                if (d < (double) MAX_CAPACITY) {
                    t = (int) d;
                    if ((double) t < d) t++;
                } else {
                    t = MAX_CAPACITY;
                }
                if (t > threshold) threshold = tableSizeFor(t);
            } else {
                while (s > threshold && table.length < MAX_CAPACITY) resize();
            }
            for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) {
                K key = e.getKey();
                V value = e.getValue();
                putVal(hash(key), key, value, false, evict);
            }
        }
    }

    public int size() {
        return size;
    }

    public boolean isEmpty() {
        return size == 0;
    }

    public V get(Object key) {
        Node<K, V> e = getNode(key);
        return e == null ? null : e.value;
    }

    static boolean sameKey(Node<?, ?> e, int h, Object key) {
        Object k;
        return e.hash == h && ((k = e.key) == key || (key != null && key.equals(k)));
    }

    final Node<K, V> getNode(Object key) {
        Node<K, V>[] tab = table;
        if (tab == null || tab.length == 0) return null;
        int h = hash(key);
        Node<K, V> first = tab[(tab.length - 1) & h];
        if (first == null) return null;
        if (sameKey(first, h, key)) return first;
        Node<K, V> e = first.next;
        if (e == null) return null;
        if (first instanceof TreeNode) return ((TreeNode<K, V>) first).getTreeNode(h, key);
        do {
            if (sameKey(e, h, key)) return e;
            e = e.next;
        } while (e != null);
        return null;
    }

    public boolean containsKey(Object key) {
        return getNode(key) != null;
    }

    public V put(K key, V value) {
        return putVal(hash(key), key, value, false, true);
    }

    final V putVal(int h, K key, V value, boolean onlyIfAbsent, boolean evict) {
        Node<K, V>[] tab = table;
        if (tab == null || tab.length == 0) tab = resize();
        int i = (tab.length - 1) & h;
        Node<K, V> p = tab[i];
        Node<K, V> found = null;
        if (p == null) {
            tab[i] = newNode(h, key, value, null);
        } else if (sameKey(p, h, key)) {
            found = p;
        } else if (p instanceof TreeNode) {
            found = ((TreeNode<K, V>) p).putTreeVal(this, tab, h, key, value);
        } else {
            int count = 0;   // nodes after p walked so far
            for (;;) {
                Node<K, V> e = p.next;
                if (e == null) {
                    p.next = newNode(h, key, value, null);
                    if (count >= TREEIFY_BIN - 1) treeifyBin(tab, h);
                    break;
                }
                if (sameKey(e, h, key)) {
                    found = e;
                    break;
                }
                p = e;
                count++;
            }
        }
        if (found != null) {
            V old = found.value;
            if (!onlyIfAbsent || old == null) found.value = value;
            afterNodeAccess(found);
            return old;
        }
        modCount++;
        if (++size > threshold) resize();
        afterNodeInsertion(evict);
        return null;
    }

    @SuppressWarnings("unchecked")
    final Node<K, V>[] resize() {
        Node<K, V>[] oldTab = table;
        int oldCap = (oldTab == null) ? 0 : oldTab.length;
        int oldThr = threshold;
        int newCap;
        int newThr = 0;
        if (oldCap > 0) {
            if (oldCap >= MAX_CAPACITY) {
                threshold = Integer.MAX_VALUE;
                return oldTab;
            }
            newCap = oldCap << 1;
            if (newCap < MAX_CAPACITY && oldCap >= 16) newThr = oldThr << 1;
        } else if (oldThr > 0) {
            newCap = oldThr;
        } else {
            newCap = 16;
            newThr = 12;
        }
        if (newThr == 0) {
            float ft = (float) newCap * loadFactor;
            newThr = (newCap < MAX_CAPACITY && ft < (float) MAX_CAPACITY) ? (int) ft : Integer.MAX_VALUE;
        }
        threshold = newThr;
        Node<K, V>[] newTab = (Node<K, V>[]) new Node[newCap];
        table = newTab;
        if (oldTab != null) {
            for (int j = 0; j < oldCap; j++) {
                Node<K, V> e = oldTab[j];
                if (e == null) continue;
                oldTab[j] = null;
                if (e.next == null) {
                    newTab[e.hash & (newCap - 1)] = e;
                } else if (e instanceof TreeNode) {
                    ((TreeNode<K, V>) e).split(this, newTab, j, oldCap);
                } else {
                    Node<K, V> loH = null, loT = null, hiH = null, hiT = null;
                    while (e != null) {
                        Node<K, V> nx = e.next;
                        if ((e.hash & oldCap) == 0) {
                            if (loT == null) loH = e;
                            else loT.next = e;
                            loT = e;
                        } else {
                            if (hiT == null) hiH = e;
                            else hiT.next = e;
                            hiT = e;
                        }
                        e = nx;
                    }
                    if (loT != null) {
                        loT.next = null;
                        newTab[j] = loH;
                    }
                    if (hiT != null) {
                        hiT.next = null;
                        newTab[j + oldCap] = hiH;
                    }
                }
            }
        }
        return newTab;
    }

    /** The bin of h has become long: resize a small table, else make the bin a tree. */
    final void treeifyBin(Node<K, V>[] tab, int h) {
        if (tab == null || tab.length < MIN_TREE_TABLE) {
            resize();
            return;
        }
        int index = (tab.length - 1) & h;
        Node<K, V> e = tab[index];
        if (e == null) return;
        TreeNode<K, V> hd = null, tl = null;
        do {
            TreeNode<K, V> p = replacementTreeNode(e, null);
            if (tl == null) {
                hd = p;
            } else {
                p.prev = tl;
                tl.next = p;
            }
            tl = p;
            e = e.next;
        } while (e != null);
        tab[index] = hd;
        if (hd != null) hd.treeify(tab);
    }

    public void putAll(Map<? extends K, ? extends V> m) {
        putMapEntries(m, true);
    }

    public V remove(Object key) {
        Node<K, V> e = removeNode(hash(key), key, null, false, true);
        return e == null ? null : e.value;
    }

    final Node<K, V> removeNode(int h, Object key, Object value, boolean matchValue, boolean movable) {
        Node<K, V>[] tab = table;
        if (tab == null || tab.length == 0) return null;
        int index = (tab.length - 1) & h;
        Node<K, V> p = tab[index];
        if (p == null) return null;
        Node<K, V> node = null;
        if (sameKey(p, h, key)) {
            node = p;
        } else if (p.next != null) {
            if (p instanceof TreeNode) {
                node = ((TreeNode<K, V>) p).getTreeNode(h, key);
            } else {
                Node<K, V> e = p.next;
                do {
                    if (sameKey(e, h, key)) {
                        node = e;
                        break;
                    }
                    p = e;
                    e = e.next;
                } while (e != null);
            }
        }
        if (node == null) return null;
        if (matchValue) {
            V v = node.value;
            if (!(v == value || (value != null && value.equals(v)))) return null;
        }
        if (node instanceof TreeNode) ((TreeNode<K, V>) node).removeTreeNode(this, tab, movable);
        else if (node == p) tab[index] = node.next;
        else p.next = node.next;
        modCount++;
        size--;
        afterNodeRemoval(node);
        return node;
    }

    public void clear() {
        Node<K, V>[] tab = table;
        modCount++;
        if (tab != null && size > 0) {
            size = 0;
            for (int i = 0; i < tab.length; i++) tab[i] = null;
        }
    }

    public boolean containsValue(Object value) {
        Node<K, V>[] tab = table;
        if (tab != null && size > 0) {
            for (int i = 0; i < tab.length; i++) {
                for (Node<K, V> e = tab[i]; e != null; e = e.next) {
                    V v = e.value;
                    if (v == value || (value != null && value.equals(v))) return true;
                }
            }
        }
        return false;
    }

    public Set<K> keySet() {
        Set<K> ks = keySet;
        if (ks == null) {
            ks = new KeySet();
            keySet = ks;
        }
        return ks;
    }

    public Collection<V> values() {
        Collection<V> vs = values;
        if (vs == null) {
            vs = new Values();
            values = vs;
        }
        return vs;
    }

    public Set<Map.Entry<K, V>> entrySet() {
        Set<Map.Entry<K, V>> es = entrySet;
        if (es == null) {
            es = new EntrySet();
            entrySet = es;
        }
        return es;
    }

    final class KeySet extends AbstractSet<K> {
        public int size() {
            return size;
        }

        public void clear() {
            HashMap.this.clear();
        }

        public Iterator<K> iterator() {
            return new KeyIterator();
        }

        public boolean contains(Object o) {
            return containsKey(o);
        }

        public boolean remove(Object key) {
            return removeNode(hash(key), key, null, false, true) != null;
        }

        public void forEach(Consumer<? super K> action) {
            if (action == null) throw new NullPointerException();
            Node<K, V>[] tab = table;
            if (size > 0 && tab != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; i++) {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next) action.accept(e.key);
                }
                if (modCount != mc) throw new ConcurrentModificationException();
            }
        }
    }

    final class Values extends AbstractCollection<V> {
        public int size() {
            return size;
        }

        public void clear() {
            HashMap.this.clear();
        }

        public Iterator<V> iterator() {
            return new ValueIterator();
        }

        public boolean contains(Object o) {
            return containsValue(o);
        }

        public void forEach(Consumer<? super V> action) {
            if (action == null) throw new NullPointerException();
            Node<K, V>[] tab = table;
            if (size > 0 && tab != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; i++) {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next) action.accept(e.value);
                }
                if (modCount != mc) throw new ConcurrentModificationException();
            }
        }
    }

    final class EntrySet extends AbstractSet<Map.Entry<K, V>> {
        public int size() {
            return size;
        }

        public void clear() {
            HashMap.this.clear();
        }

        public Iterator<Map.Entry<K, V>> iterator() {
            return new EntryIterator();
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
            Node<K, V>[] tab = table;
            if (size > 0 && tab != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; i++) {
                    for (Node<K, V> e = tab[i]; e != null; e = e.next) action.accept(e);
                }
                if (modCount != mc) throw new ConcurrentModificationException();
            }
        }
    }

    // ---- Map default-method overrides with HashMap's own behaviour ----

    public V getOrDefault(Object key, V defaultValue) {
        Node<K, V> e = getNode(key);
        return e == null ? defaultValue : e.value;
    }

    public V putIfAbsent(K key, V value) {
        return putVal(hash(key), key, value, true, true);
    }

    public boolean remove(Object key, Object value) {
        return removeNode(hash(key), key, value, true, true) != null;
    }

    public boolean replace(K key, V oldValue, V newValue) {
        Node<K, V> e = getNode(key);
        if (e != null) {
            V v = e.value;
            if (v == oldValue || (v != null && v.equals(oldValue))) {
                e.value = newValue;
                afterNodeAccess(e);
                return true;
            }
        }
        return false;
    }

    public V replace(K key, V value) {
        Node<K, V> e = getNode(key);
        if (e != null) {
            V old = e.value;
            e.value = value;
            afterNodeAccess(e);
            return old;
        }
        return null;
    }

    /** State shared by computeIfAbsent/compute/merge: the bin of the key and what was found. */
    private Node<K, V>[] cTab;
    private int cIndex;
    private int cCount;
    private TreeNode<K, V> cTree;
    private Node<K, V> cFirst;

    /** Resize if needed (these methods resize BEFORE inserting), then look the key up. */
    private Node<K, V> computeLookup(int h, Object key) {
        Node<K, V>[] tab = table;
        if (size > threshold || tab == null || tab.length == 0) tab = resize();
        int i = (tab.length - 1) & h;
        Node<K, V> first = tab[i];
        Node<K, V> old = null;
        int count = 0;
        TreeNode<K, V> t = null;
        if (first != null) {
            if (first instanceof TreeNode) {
                t = (TreeNode<K, V>) first;
                old = t.getTreeNode(h, key);
            } else {
                Node<K, V> e = first;
                do {
                    if (sameKey(e, h, key)) {
                        old = e;
                        break;
                    }
                    count++;
                    e = e.next;
                } while (e != null);
            }
        }
        cTab = tab;
        cIndex = i;
        cCount = count;
        cTree = t;
        cFirst = first;
        return old;
    }

    /** Insert a new entry found absent by computeLookup: at the head of a list bin. */
    private void computeInsert(Node<K, V>[] tab, int i, int count, TreeNode<K, V> t, Node<K, V> first,
                               int h, K key, V v) {
        if (t != null) {
            t.putTreeVal(this, tab, h, key, v);
        } else {
            tab[i] = newNode(h, key, v, first);
            if (count >= TREEIFY_BIN - 1) treeifyBin(tab, h);
        }
    }

    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if (mappingFunction == null) throw new NullPointerException();
        int h = hash(key);
        Node<K, V> old = computeLookup(h, key);
        Node<K, V>[] tab = cTab;
        int i = cIndex, count = cCount;
        TreeNode<K, V> t = cTree;
        Node<K, V> first = cFirst;
        cTab = null; cTree = null; cFirst = null;
        if (old != null && old.value != null) {
            V ov = old.value;
            afterNodeAccess(old);
            return ov;
        }
        int mc = modCount;
        V v = mappingFunction.apply(key);
        if (mc != modCount) throw new ConcurrentModificationException();
        if (v == null) return null;
        if (old != null) {
            old.value = v;
            afterNodeAccess(old);
            return v;
        }
        computeInsert(tab, i, count, t, first, h, key, v);
        modCount = mc + 1;
        size++;
        afterNodeInsertion(true);
        return v;
    }

    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        Node<K, V> e = getNode(key);
        if (e != null && e.value != null) {
            V ov = e.value;
            int mc = modCount;
            V v = remappingFunction.apply(key, ov);
            if (mc != modCount) throw new ConcurrentModificationException();
            if (v == null) {
                removeNode(hash(key), key, null, false, true);
            } else {
                e.value = v;
                afterNodeAccess(e);
                return v;
            }
        }
        return null;
    }

    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (remappingFunction == null) throw new NullPointerException();
        int h = hash(key);
        Node<K, V> old = computeLookup(h, key);
        Node<K, V>[] tab = cTab;
        int i = cIndex, count = cCount;
        TreeNode<K, V> t = cTree;
        Node<K, V> first = cFirst;
        cTab = null; cTree = null; cFirst = null;
        V ov = (old == null) ? null : old.value;
        int mc = modCount;
        V v = remappingFunction.apply(key, ov);
        if (mc != modCount) throw new ConcurrentModificationException();
        if (old != null) {
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            } else {
                removeNode(h, key, null, false, true);
            }
        } else if (v != null) {
            computeInsert(tab, i, count, t, first, h, key, v);
            modCount = mc + 1;
            size++;
            afterNodeInsertion(true);
        }
        return v;
    }

    public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (value == null || remappingFunction == null) throw new NullPointerException();
        int h = hash(key);
        Node<K, V> old = computeLookup(h, key);
        Node<K, V>[] tab = cTab;
        int i = cIndex, count = cCount;
        TreeNode<K, V> t = cTree;
        Node<K, V> first = cFirst;
        cTab = null; cTree = null; cFirst = null;
        if (old != null) {
            V v;
            if (old.value != null) {
                int mc = modCount;
                v = remappingFunction.apply(old.value, value);
                if (mc != modCount) throw new ConcurrentModificationException();
            } else {
                v = value;
            }
            if (v != null) {
                old.value = v;
                afterNodeAccess(old);
            } else {
                removeNode(h, key, null, false, true);
            }
            return v;
        }
        computeInsert(tab, i, count, t, first, h, key, value);
        modCount++;
        size++;
        afterNodeInsertion(true);
        return value;
    }

    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        Node<K, V>[] tab = table;
        if (size > 0 && tab != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; i++) {
                for (Node<K, V> e = tab[i]; e != null; e = e.next) action.accept(e.key, e.value);
            }
            if (modCount != mc) throw new ConcurrentModificationException();
        }
    }

    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        Node<K, V>[] tab = table;
        if (size > 0 && tab != null) {
            int mc = modCount;
            for (int i = 0; i < tab.length; i++) {
                for (Node<K, V> e = tab[i]; e != null; e = e.next) e.value = function.apply(e.key, e.value);
            }
            if (modCount != mc) throw new ConcurrentModificationException();
        }
    }

    public Object clone() {
        throw ModelStuck.unsupported("HashMap.clone");
    }

    // ---- hooks for LinkedHashMap ----

    Node<K, V> newNode(int h, K key, V value, Node<K, V> next) {
        return new Node<>(h, key, value, next);
    }

    Node<K, V> replacementNode(Node<K, V> p, Node<K, V> next) {
        return new Node<>(p.hash, p.key, p.value, next);
    }

    TreeNode<K, V> newTreeNode(int h, K key, V value, Node<K, V> next) {
        return new TreeNode<>(h, key, value, next);
    }

    TreeNode<K, V> replacementTreeNode(Node<K, V> p, Node<K, V> next) {
        return new TreeNode<>(p.hash, p.key, p.value, next);
    }

    void afterNodeAccess(Node<K, V> p) {
    }

    void afterNodeInsertion(boolean evict) {
    }

    void afterNodeRemoval(Node<K, V> p) {
    }

    // ---- iterators ----

    abstract class HashIterator {
        Node<K, V> next;
        Node<K, V> current;
        int expectedModCount;
        int index;

        HashIterator() {
            expectedModCount = modCount;
            Node<K, V>[] t = table;
            if (t != null && size > 0) advance(t);
        }

        /** next := first non-empty slot at index or later (index moves past it). */
        private void advance(Node<K, V>[] t) {
            while (index < t.length) {
                Node<K, V> e = t[index++];
                if (e != null) {
                    next = e;
                    return;
                }
            }
        }

        public final boolean hasNext() {
            return next != null;
        }

        final Node<K, V> nextNode() {
            Node<K, V> e = next;
            if (modCount != expectedModCount) throw new ConcurrentModificationException();
            if (e == null) throw new NoSuchElementException();
            current = e;
            next = e.next;
            if (next == null) {
                Node<K, V>[] t = table;
                if (t != null) advance(t);
            }
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

    final class KeyIterator extends HashIterator implements Iterator<K> {
        public K next() {
            return nextNode().key;
        }
    }

    final class ValueIterator extends HashIterator implements Iterator<V> {
        public V next() {
            return nextNode().value;
        }
    }

    final class EntryIterator extends HashIterator implements Iterator<Map.Entry<K, V>> {
        public Map.Entry<K, V> next() {
            return nextNode();
        }
    }

    // ---- tree bins ----

    /** C if x's class is C implements Comparable<C> (String and the boxes); null if x is not
     *  Comparable.  Other Comparable classes need their generic signature: STUCK. */
    static Class<?> comparableClassFor(Object x) {
        if (x instanceof String || x instanceof Integer || x instanceof Long || x instanceof Short
            || x instanceof Byte || x instanceof Character || x instanceof Boolean) {
            return x.getClass();
        }
        if (x instanceof Comparable) {
            throw ModelStuck.unsupported("HashMap tree bin: is the key class C implements Comparable<C>?");
        }
        return null;
    }

    /** k.compareTo(x) if x is of class kc (the comparable class of k), else 0. */
    static int compareComparables(Class<?> kc, Object k, Object x) {
        if (x == null || x.getClass() != kc) return 0;
        if (k instanceof String) return ((String) k).compareTo((String) x);
        if (k instanceof Integer) return ((Integer) k).compareTo((Integer) x);
        if (k instanceof Long) return ((Long) k).compareTo((Long) x);
        if (k instanceof Short) return ((Short) k).compareTo((Short) x);
        if (k instanceof Byte) return ((Byte) k).compareTo((Byte) x);
        if (k instanceof Character) return ((Character) k).compareTo((Character) x);
        if (k instanceof Boolean) return ((Boolean) k).compareTo((Boolean) x);
        throw ModelStuck.unsupported("HashMap tree bin: compareTo");
    }

    /** Order of keys with equal hash codes that do not compare: by class name, then by
     *  identity hash code.  A null key orders first (HotSpot identity hash codes are > 0). */
    static int tieBreakOrder(Object a, Object b) {
        if (a == null) return -1;
        if (b == null) return 1;
        if (a.getClass() != b.getClass()) {
            int d = a.getClass().getName().compareTo(b.getClass().getName());
            if (d != 0) return d;
        }
        // HotSpot's identity hash codes decide here; the machine's are a parameter (jenv.j_ihash), so
        // an order that depends on them is not claimed
        throw ModelStuck.unsupported("HashMap tree bin: order by identity hash code");
    }

    static final class TreeNode<K, V> extends Node<K, V> {
        TreeNode<K, V> parent;
        TreeNode<K, V> left;
        TreeNode<K, V> right;
        TreeNode<K, V> prev;   // the bin list is doubly linked in a tree bin
        boolean red;

        TreeNode(int hash, K key, V val, Node<K, V> next) {
            super(hash, key, val, next);
        }

        TreeNode<K, V> root() {
            TreeNode<K, V> r = this;
            while (r.parent != null) r = r.parent;
            return r;
        }

        /** Make root the first node of its bin's list. */
        static <K, V> void moveRootToFront(Node<K, V>[] tab, TreeNode<K, V> root) {
            if (root == null || tab == null || tab.length == 0) return;
            int index = (tab.length - 1) & root.hash;
            TreeNode<K, V> first = (TreeNode<K, V>) tab[index];
            if (root == first) return;
            tab[index] = root;
            TreeNode<K, V> rp = root.prev;
            Node<K, V> rn = root.next;
            if (rn != null) ((TreeNode<K, V>) rn).prev = rp;
            if (rp != null) rp.next = rn;
            if (first != null) first.prev = root;
            root.next = first;
            root.prev = null;
        }

        /** The node of key k (hash h) in the subtree of this node, or null. */
        TreeNode<K, V> find(int h, Object k, Class<?> kc) {
            TreeNode<K, V> p = this;
            do {
                TreeNode<K, V> pl = p.left, pr = p.right;
                int ph = p.hash;
                Object pk;
                if (ph > h) {
                    p = pl;
                } else if (ph < h) {
                    p = pr;
                } else if ((pk = p.key) == k || (k != null && k.equals(pk))) {
                    return p;
                } else if (pl == null) {
                    p = pr;
                } else if (pr == null) {
                    p = pl;
                } else {
                    int dir = 0;
                    if (kc == null) kc = comparableClassFor(k);
                    if (kc != null) dir = compareComparables(kc, k, pk);
                    if (dir != 0) {
                        p = (dir < 0) ? pl : pr;
                    } else {
                        TreeNode<K, V> q = pr.find(h, k, kc);
                        if (q != null) return q;
                        p = pl;
                    }
                }
            } while (p != null);
            return null;
        }

        TreeNode<K, V> getTreeNode(int h, Object k) {
            return ((parent != null) ? root() : this).find(h, k, null);
        }

        /** Direction of key k (hash h) relative to node p, for an insertion; never 0. */
        static int insertDir(int h, Object k, Class<?>[] kcBox, TreeNode<?, ?> p) {
            int ph = p.hash;
            if (ph > h) return -1;
            if (ph < h) return 1;
            Object pk = p.key;
            int dir = 0;
            if (kcBox[0] == null) kcBox[0] = comparableClassFor(k);
            if (kcBox[0] != null) dir = compareComparables(kcBox[0], k, pk);
            return dir;
        }

        /** Build a red-black tree from the list starting at this node; list order kept,
         *  then the root moved to the front. */
        void treeify(Node<K, V>[] tab) {
            TreeNode<K, V> root = null;
            for (TreeNode<K, V> x = this, nx; x != null; x = nx) {
                nx = (TreeNode<K, V>) x.next;
                x.left = x.right = null;
                if (root == null) {
                    x.parent = null;
                    x.red = false;
                    root = x;
                    continue;
                }
                K k = x.key;
                int h = x.hash;
                Class<?>[] kcBox = new Class<?>[1];
                for (TreeNode<K, V> p = root;;) {
                    int ph = p.hash;
                    int dir;
                    if (ph > h) {
                        dir = -1;
                    } else if (ph < h) {
                        dir = 1;
                    } else {
                        dir = insertDir(h, k, kcBox, p);
                        if (dir == 0) dir = tieBreakOrder(k, p.key);
                    }
                    TreeNode<K, V> xp = p;
                    p = (dir <= 0) ? p.left : p.right;
                    if (p == null) {
                        x.parent = xp;
                        if (dir <= 0) xp.left = x;
                        else xp.right = x;
                        root = balanceInsertion(root, x);
                        break;
                    }
                }
            }
            moveRootToFront(tab, root);
        }

        /** Plain list nodes for the list starting at this node, same order. */
        Node<K, V> untreeify(HashMap<K, V> map) {
            Node<K, V> hd = null, tl = null;
            for (Node<K, V> q = this; q != null; q = q.next) {
                Node<K, V> p = map.replacementNode(q, null);
                if (tl == null) hd = p;
                else tl.next = p;
                tl = p;
            }
            return hd;
        }

        /** Insert (h, k, v) into this tree bin; the existing node if the key is present. */
        TreeNode<K, V> putTreeVal(HashMap<K, V> map, Node<K, V>[] tab, int h, K k, V v) {
            Class<?>[] kcBox = new Class<?>[1];
            boolean searched = false;
            TreeNode<K, V> root = (parent != null) ? root() : this;
            for (TreeNode<K, V> p = root;;) {
                int ph = p.hash;
                Object pk;
                int dir;
                if (ph > h) {
                    dir = -1;
                } else if (ph < h) {
                    dir = 1;
                } else if ((pk = p.key) == k || (k != null && k.equals(pk))) {
                    return p;
                } else {
                    if (kcBox[0] == null) kcBox[0] = comparableClassFor(k);
                    dir = (kcBox[0] == null) ? 0 : compareComparables(kcBox[0], k, pk);
                    if (dir == 0) {
                        if (!searched) {
                            searched = true;
                            TreeNode<K, V> q;
                            TreeNode<K, V> ch = p.left;
                            if (ch != null && (q = ch.find(h, k, kcBox[0])) != null) return q;
                            ch = p.right;
                            if (ch != null && (q = ch.find(h, k, kcBox[0])) != null) return q;
                        }
                        dir = tieBreakOrder(k, pk);
                    }
                }
                TreeNode<K, V> xp = p;
                p = (dir <= 0) ? p.left : p.right;
                if (p == null) {
                    Node<K, V> xpn = xp.next;
                    TreeNode<K, V> x = map.newTreeNode(h, k, v, xpn);
                    if (dir <= 0) xp.left = x;
                    else xp.right = x;
                    xp.next = x;
                    x.parent = x.prev = xp;
                    if (xpn != null) ((TreeNode<K, V>) xpn).prev = x;
                    moveRootToFront(tab, balanceInsertion(root, x));
                    return null;
                }
            }
        }

        /** Remove this node (which must be in the tree bin of its hash). */
        void removeTreeNode(HashMap<K, V> map, Node<K, V>[] tab, boolean movable) {
            if (tab == null || tab.length == 0) return;
            int index = (tab.length - 1) & hash;
            TreeNode<K, V> first = (TreeNode<K, V>) tab[index];
            TreeNode<K, V> root = first;
            // unlink from the bin list
            TreeNode<K, V> succ = (TreeNode<K, V>) next, pred = prev;
            if (pred == null) tab[index] = first = succ;
            else pred.next = succ;
            if (succ != null) succ.prev = pred;
            if (first == null) return;
            if (root.parent != null) root = root.root();
            if (root == null
                || (movable && (root.right == null || root.left == null || root.left.left == null))) {
                tab[index] = first.untreeify(map);   // too small for a tree
                return;
            }
            // unlink from the tree
            TreeNode<K, V> p = this, pl = left, pr = right, replacement;
            if (pl != null && pr != null) {
                // exchange p with its successor s (positions and colours), then delete p there
                TreeNode<K, V> s = pr, sl;
                while ((sl = s.left) != null) s = sl;
                boolean c = s.red;
                s.red = p.red;
                p.red = c;
                TreeNode<K, V> sr = s.right;
                TreeNode<K, V> pp = p.parent;
                if (s == pr) {
                    p.parent = s;
                    s.right = p;
                } else {
                    TreeNode<K, V> sp = s.parent;
                    p.parent = sp;
                    if (sp != null) {
                        if (s == sp.left) sp.left = p;
                        else sp.right = p;
                    }
                    s.right = pr;
                    if (pr != null) pr.parent = s;
                }
                p.left = null;
                p.right = sr;
                if (sr != null) sr.parent = p;
                s.left = pl;
                if (pl != null) pl.parent = s;
                s.parent = pp;
                if (pp == null) root = s;
                else if (p == pp.left) pp.left = s;
                else pp.right = s;
                replacement = (sr != null) ? sr : p;
            } else if (pl != null) {
                replacement = pl;
            } else if (pr != null) {
                replacement = pr;
            } else {
                replacement = p;
            }
            if (replacement != p) {
                TreeNode<K, V> pp = replacement.parent = p.parent;
                if (pp == null) {
                    root = replacement;
                    replacement.red = false;
                } else if (p == pp.left) {
                    pp.left = replacement;
                } else {
                    pp.right = replacement;
                }
                p.left = p.right = p.parent = null;
            }
            TreeNode<K, V> r = p.red ? root : balanceDeletion(root, replacement);
            if (replacement == p) {   // p was a leaf: detach it now
                TreeNode<K, V> pp = p.parent;
                p.parent = null;
                if (pp != null) {
                    if (p == pp.left) pp.left = null;
                    else if (p == pp.right) pp.right = null;
                }
            }
            if (movable) moveRootToFront(tab, r);
        }

        /** Resize: split this tree bin (slot index of the old table) into the entries staying at
         *  index and those moving to index + bit, in list order. */
        void split(HashMap<K, V> map, Node<K, V>[] tab, int index, int bit) {
            TreeNode<K, V> loH = null, loT = null, hiH = null, hiT = null;
            int lc = 0, hc = 0;
            for (TreeNode<K, V> e = this, nx; e != null; e = nx) {
                nx = (TreeNode<K, V>) e.next;
                e.next = null;
                if ((e.hash & bit) == 0) {
                    e.prev = loT;
                    if (loT == null) loH = e;
                    else loT.next = e;
                    loT = e;
                    lc++;
                } else {
                    e.prev = hiT;
                    if (hiT == null) hiH = e;
                    else hiT.next = e;
                    hiT = e;
                    hc++;
                }
            }
            if (loH != null) {
                if (lc <= UNTREEIFY_BIN) {
                    tab[index] = loH.untreeify(map);
                } else {
                    tab[index] = loH;
                    if (hiH != null) loH.treeify(tab);   // else the tree is unchanged
                }
            }
            if (hiH != null) {
                if (hc <= UNTREEIFY_BIN) {
                    tab[index + bit] = hiH.untreeify(map);
                } else {
                    tab[index + bit] = hiH;
                    if (loH != null) hiH.treeify(tab);
                }
            }
        }

        // red-black tree primitives (CLRS)

        static <K, V> TreeNode<K, V> rotateLeft(TreeNode<K, V> root, TreeNode<K, V> p) {
            TreeNode<K, V> r;
            if (p != null && (r = p.right) != null) {
                TreeNode<K, V> rl = p.right = r.left;
                if (rl != null) rl.parent = p;
                TreeNode<K, V> pp = r.parent = p.parent;
                if (pp == null) {
                    root = r;
                    r.red = false;
                } else if (pp.left == p) {
                    pp.left = r;
                } else {
                    pp.right = r;
                }
                r.left = p;
                p.parent = r;
            }
            return root;
        }

        static <K, V> TreeNode<K, V> rotateRight(TreeNode<K, V> root, TreeNode<K, V> p) {
            TreeNode<K, V> l;
            if (p != null && (l = p.left) != null) {
                TreeNode<K, V> lr = p.left = l.right;
                if (lr != null) lr.parent = p;
                TreeNode<K, V> pp = l.parent = p.parent;
                if (pp == null) {
                    root = l;
                    l.red = false;
                } else if (pp.right == p) {
                    pp.right = l;
                } else {
                    pp.left = l;
                }
                l.right = p;
                p.parent = l;
            }
            return root;
        }

        static boolean isRed(TreeNode<?, ?> n) {
            return n != null && n.red;
        }

        /** CLRS RB-INSERT-FIXUP for the new red node x; returns the root. */
        static <K, V> TreeNode<K, V> balanceInsertion(TreeNode<K, V> root, TreeNode<K, V> x) {
            x.red = true;
            for (;;) {
                TreeNode<K, V> xp = x.parent;
                if (xp == null) {
                    x.red = false;
                    return x;
                }
                if (!xp.red) return root;
                TreeNode<K, V> xpp = xp.parent;
                if (xpp == null) return root;
                if (xp == xpp.left) {
                    TreeNode<K, V> uncle = xpp.right;
                    if (isRed(uncle)) {
                        uncle.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    } else {
                        if (x == xp.right) {
                            x = xp;
                            root = rotateLeft(root, x);
                            xp = x.parent;
                            xpp = (xp == null) ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateRight(root, xpp);
                            }
                        }
                    }
                } else {
                    TreeNode<K, V> uncle = xpp.left;
                    if (isRed(uncle)) {
                        uncle.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    } else {
                        if (x == xp.left) {
                            x = xp;
                            root = rotateRight(root, x);
                            xp = x.parent;
                            xpp = (xp == null) ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateLeft(root, xpp);
                            }
                        }
                    }
                }
            }
        }

        /** CLRS RB-DELETE-FIXUP starting at x (x may be the removed leaf itself, still
         *  attached); returns the root. */
        static <K, V> TreeNode<K, V> balanceDeletion(TreeNode<K, V> root, TreeNode<K, V> x) {
            for (;;) {
                if (x == null || x == root) return root;
                TreeNode<K, V> xp = x.parent;
                if (xp == null) {
                    x.red = false;
                    return x;
                }
                if (x.red) {
                    x.red = false;
                    return root;
                }
                if (xp.left == x) {
                    TreeNode<K, V> w = xp.right;
                    if (isRed(w)) {
                        w.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xp = x.parent;
                        w = (xp == null) ? null : xp.right;
                    }
                    if (w == null) {
                        x = xp;
                    } else {
                        TreeNode<K, V> sl = w.left, sr = w.right;
                        if (!isRed(sr) && !isRed(sl)) {
                            w.red = true;
                            x = xp;
                        } else {
                            if (!isRed(sr)) {
                                if (sl != null) sl.red = false;
                                w.red = true;
                                root = rotateRight(root, w);
                                xp = x.parent;
                                w = (xp == null) ? null : xp.right;
                            }
                            if (w != null) {
                                w.red = (xp == null) ? false : xp.red;
                                if ((sr = w.right) != null) sr.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                } else {
                    TreeNode<K, V> w = xp.left;
                    if (isRed(w)) {
                        w.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xp = x.parent;
                        w = (xp == null) ? null : xp.left;
                    }
                    if (w == null) {
                        x = xp;
                    } else {
                        TreeNode<K, V> sl = w.left, sr = w.right;
                        if (!isRed(sl) && !isRed(sr)) {
                            w.red = true;
                            x = xp;
                        } else {
                            if (!isRed(sl)) {
                                if (sr != null) sr.red = false;
                                w.red = true;
                                root = rotateLeft(root, w);
                                xp = x.parent;
                                w = (xp == null) ? null : xp.left;
                            }
                            if (w != null) {
                                w.red = (xp == null) ? false : xp.red;
                                if ((sl = w.left) != null) sl.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            x = root;
                        }
                    }
                }
            }
        }
    }
}

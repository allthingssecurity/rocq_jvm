/*
 * rocq-jvm model of java.util.concurrent.ConcurrentSkipListMap (clean-room, Apache-2.0).
 *
 * The JDK's base level only: a sorted singly linked list of nodes behind a header node (made by
 * the first insertion). The index levels of the JDK are a search accelerator whose shape is
 * random (ThreadLocalRandom), so they decide only which keys a search compares with, never a
 * result; searches here walk the list. What is observable is kept: a removed node gets value
 * null and keeps its successor at the time of removal (the JDK's marker), a value replaced in
 * place keeps its node, and iterators (weakly consistent) prefetch the next node and its value
 * and continue from the node they returned, so they behave as the JDK's under modification
 * (they never throw ConcurrentModificationException). The first insertion into an empty map
 * compares the key with itself (type check). Entries returned are immutable snapshots. The
 * element count is per map, the JDK's LongAdder (clone() of an emptied map shares the list with
 * the original, as in the JDK). Each atomic step of the JDK (a search plus a compare-and-set) is
 * synchronized on a lock; user functions (compute / merge / forEach actions) run outside it.
 *
 * Ordering: the comparator, or the keys' compareTo; the ClassCastException of the bridge
 * compareTo(Object) of String and the boxes is thrown with HotSpot's message (for a user class
 * argument the message is STUCK). Differences that only a comparator with side effects could
 * observe: the sequence of compare calls. Not modelled: spliterators (and so streams: STUCK),
 * serialization.
 */
package java.util.concurrent;

import java.util.AbstractCollection;
import java.util.AbstractMap;
import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NavigableSet;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.SortedMap;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.function.Predicate;

public class ConcurrentSkipListMap<K, V> extends AbstractMap<K, V>
        implements ConcurrentNavigableMap<K, V>, Cloneable, java.io.Serializable {
    private static final long serialVersionUID = -8627078645895051609L;

    @SuppressWarnings("serial")
    final Comparator<? super K> comparator;

    /** A node: the header has key null; a removed node has val null and keeps its next. */
    static final class Node<K, V> {
        final K key;
        V val;
        Node<K, V> next;
        Node(K key, V value, Node<K, V> next) {
            this.key = key;
            this.val = value;
            this.next = next;
        }
    }

    private transient Node<K, V> head;
    private transient long adder;
    private transient Object lock = new Object();
    private transient KeySet<K, V> keySet;
    private transient Values<K, V> values;
    private transient EntrySet<K, V> entrySet;
    private transient SubMap<K, V> descendingMap;

    // ---------------- utilities ----------------

    private static boolean isJdkComparable(Object x) {
        return x instanceof String || x instanceof Integer || x instanceof Long || x instanceof Short
            || x instanceof Byte || x instanceof Character || x instanceof Boolean;
    }

    /** The JDK's cpr. */
    @SuppressWarnings({"unchecked", "rawtypes"})
    static int cpr(Comparator c, Object x, Object y) {
        if (c != null) return c.compare(x, y);
        if (y != null && isJdkComparable(x) && x.getClass() != y.getClass()) {
            // the bridge compareTo(Object) of String and the boxes casts its argument first
            String a = y.getClass().getName(), b = x.getClass().getName();
            if (!isJdkComparable(y)) throw ModelStuck.unsupported("ConcurrentSkipListMap: ClassCastException message for a user class");
            throw new ClassCastException("class " + a + " cannot be cast to class " + b
                + " (" + a + " and " + b + " are in module java.base of loader 'bootstrap')");
        }
        if (x == null) throw new NullPointerException("Cannot invoke \"java.lang.Comparable.compareTo(Object)\" because \"x\" is null");
        return ((Comparable) x).compareTo(y);
    }

    final Node<K, V> baseHead() {
        synchronized (lock) {
            return head;
        }
    }

    final long getAdderCount() {
        synchronized (lock) {
            long c = adder;
            return (c <= 0L) ? 0L : c;
        }
    }

    /** The successor of a node (lock taken: the list may change under other threads). */
    final Node<K, V> nextOf(Node<K, V> n) {
        synchronized (lock) {
            return n.next;
        }
    }

    final V valOf(Node<K, V> n) {
        synchronized (lock) {
            return n.val;
        }
    }

    /** CAS of a node's value. */
    final boolean casVal(Node<K, V> n, V cmp, V val) {
        synchronized (lock) {
            if (n.val != cmp) return false;
            n.val = val;
            return true;
        }
    }

    // ---------------- traversal ----------------

    final Node<K, V> findNode(Object key) {
        if (key == null) throw new NullPointerException();
        Comparator<? super K> cmp = comparator;
        synchronized (lock) {
            if (head == null) return null;
            for (Node<K, V> n = head.next; n != null; n = n.next) {
                int c = cpr(cmp, key, n.key);
                if (c > 0) continue;
                return (c == 0) ? n : null;
            }
            return null;
        }
    }

    private V doGet(Object key) {
        if (key == null) throw new NullPointerException();
        Node<K, V> n = findNode(key);
        return (n == null) ? null : n.val;
    }

    // ---------------- insertion ----------------

    private V doPut(K key, V value, boolean onlyIfAbsent) {
        if (key == null) throw new NullPointerException();
        Comparator<? super K> cmp = comparator;
        synchronized (lock) {
            if (head == null) head = new Node<K, V>(null, null, null);
            Node<K, V> b = head;
            for (;;) {
                Node<K, V> n = b.next;
                int c;
                if (n == null) {
                    if (b.key == null) cpr(cmp, key, key);   // empty: type check the key now
                    c = -1;
                } else if ((c = cpr(cmp, key, n.key)) > 0) {
                    b = n;
                    continue;
                } else if (c == 0) {
                    V v = n.val;
                    if (!onlyIfAbsent) n.val = value;
                    return v;
                }
                b.next = new Node<K, V>(key, value, n);
                adder++;
                return null;
            }
        }
    }

    // ---------------- deletion ----------------

    /** Removes the node n, whose predecessor is b (lock held). */
    private void unlink(Node<K, V> b, Node<K, V> n) {
        n.val = null;
        b.next = n.next;
        adder--;
    }

    final V doRemove(Object key, Object value) {
        if (key == null) throw new NullPointerException();
        Comparator<? super K> cmp = comparator;
        synchronized (lock) {
            if (head == null) return null;
            for (Node<K, V> b = head, n; (n = b.next) != null; b = n) {
                int c = cpr(cmp, key, n.key);
                if (c > 0) continue;
                if (c < 0) return null;
                V v = n.val;
                if (value != null && !value.equals(v)) return null;
                unlink(b, n);
                return v;
            }
            return null;
        }
    }

    final Node<K, V> findFirst() {
        synchronized (lock) {
            return (head == null) ? null : head.next;
        }
    }

    final AbstractMap.SimpleImmutableEntry<K, V> findFirstEntry() {
        synchronized (lock) {
            Node<K, V> n;
            if (head == null || (n = head.next) == null) return null;
            return new AbstractMap.SimpleImmutableEntry<K, V>(n.key, n.val);
        }
    }

    private AbstractMap.SimpleImmutableEntry<K, V> doRemoveFirstEntry() {
        synchronized (lock) {
            Node<K, V> n;
            if (head == null || (n = head.next) == null) return null;
            K k = n.key;
            V v = n.val;
            unlink(head, n);
            return new AbstractMap.SimpleImmutableEntry<K, V>(k, v);
        }
    }

    final Node<K, V> findLast() {
        synchronized (lock) {
            if (head == null) return null;
            Node<K, V> b = head;
            while (b.next != null) b = b.next;
            return (b.key == null) ? null : b;
        }
    }

    final AbstractMap.SimpleImmutableEntry<K, V> findLastEntry() {
        synchronized (lock) {
            Node<K, V> n = findLast();
            return (n == null) ? null : new AbstractMap.SimpleImmutableEntry<K, V>(n.key, n.val);
        }
    }

    private Map.Entry<K, V> doRemoveLastEntry() {
        synchronized (lock) {
            if (head == null || head.next == null) return null;
            Node<K, V> b = head, n = head.next;
            while (n.next != null) {
                b = n;
                n = n.next;
            }
            K k = n.key;
            V v = n.val;
            unlink(b, n);
            return new AbstractMap.SimpleImmutableEntry<K, V>(k, v);
        }
    }

    // ---------------- relational operations ----------------

    private static final int EQ = 1;
    private static final int LT = 2;
    private static final int GT = 0;

    final Node<K, V> findNear(K key, int rel, Comparator<? super K> cmp) {
        if (key == null) throw new NullPointerException();
        synchronized (lock) {
            if (head == null) return null;
            for (Node<K, V> b = head;;) {
                Node<K, V> n = b.next;
                int c;
                if (n == null) return ((rel & LT) != 0 && b.key != null) ? b : null;
                if (((c = cpr(cmp, key, n.key)) == 0 && (rel & EQ) != 0) || (c < 0 && (rel & LT) == 0)) return n;
                if (c <= 0 && (rel & LT) != 0) return (b.key != null) ? b : null;
                b = n;
            }
        }
    }

    final AbstractMap.SimpleImmutableEntry<K, V> findNearEntry(K key, int rel, Comparator<? super K> cmp) {
        synchronized (lock) {
            Node<K, V> n = findNear(key, rel, cmp);
            return (n == null) ? null : new AbstractMap.SimpleImmutableEntry<K, V>(n.key, n.val);
        }
    }

    // ---------------- constructors ----------------

    public ConcurrentSkipListMap() {
        this.comparator = null;
    }

    public ConcurrentSkipListMap(Comparator<? super K> comparator) {
        this.comparator = comparator;
    }

    public ConcurrentSkipListMap(Map<? extends K, ? extends V> m) {
        this.comparator = null;
        if (m == null) throw new NullPointerException("Cannot invoke \"java.util.Map.entrySet()\" because \"m\" is null");
        putAll(m);
    }

    public ConcurrentSkipListMap(SortedMap<K, ? extends V> m) {
        if (m == null) throw new NullPointerException("Cannot invoke \"java.util.SortedMap.comparator()\" because \"m\" is null");
        this.comparator = m.comparator();
        buildFromSorted(m);
    }

    @SuppressWarnings("unchecked")
    public ConcurrentSkipListMap<K, V> clone() {
        try {
            ConcurrentSkipListMap<K, V> clone = (ConcurrentSkipListMap<K, V>) super.clone();
            clone.keySet = null;
            clone.entrySet = null;
            clone.values = null;
            clone.descendingMap = null;
            clone.adder = 0L;
            clone.buildFromSorted(this);
            return clone;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }

    /** Links the entries in the map's order, without comparisons (as the JDK). */
    private void buildFromSorted(SortedMap<K, ? extends V> map) {
        if (map == null) throw new NullPointerException();
        Iterator<? extends Map.Entry<? extends K, ? extends V>> it = map.entrySet().iterator();
        Node<K, V> h = new Node<K, V>(null, null, null);
        Node<K, V> bp = h;
        long count = 0;
        while (it.hasNext()) {
            Map.Entry<? extends K, ? extends V> e = it.next();
            K k = e.getKey();
            V v = e.getValue();
            if (k == null || v == null) throw new NullPointerException();
            Node<K, V> z = new Node<K, V>(k, v, null);
            bp = bp.next = z;
            ++count;
        }
        if (count != 0L) {
            synchronized (lock) {
                adder += count;
                head = h;
            }
        }
    }

    // ---------------- Map API ----------------

    public boolean containsKey(Object key) {
        return doGet(key) != null;
    }

    public V get(Object key) {
        return doGet(key);
    }

    public V getOrDefault(Object key, V defaultValue) {
        V v;
        return (v = doGet(key)) == null ? defaultValue : v;
    }

    public V put(K key, V value) {
        if (value == null) throw new NullPointerException();
        return doPut(key, value, false);
    }

    public V remove(Object key) {
        return doRemove(key, null);
    }

    public boolean containsValue(Object value) {
        if (value == null) throw new NullPointerException();
        Node<K, V> b, n;
        V v;
        if ((b = baseHead()) != null) {
            while ((n = nextOf(b)) != null) {
                if ((v = valOf(n)) != null && value.equals(v)) return true;
                else b = n;
            }
        }
        return false;
    }

    public int size() {
        long c;
        return ((baseHead() == null) ? 0 : ((c = getAdderCount()) >= Integer.MAX_VALUE) ? Integer.MAX_VALUE : (int) c);
    }

    public boolean isEmpty() {
        return findFirst() == null;
    }

    public void clear() {
        synchronized (lock) {
            if (head == null) return;
            for (Node<K, V> n = head.next; n != null; n = n.next) {
                if (n.val != null) {
                    n.val = null;
                    adder--;
                }
            }
            head.next = null;
        }
    }

    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if (key == null || mappingFunction == null) throw new NullPointerException();
        V v, p, r;
        if ((v = doGet(key)) == null && (r = mappingFunction.apply(key)) != null)
            v = (p = doPut(key, r, true)) == null ? r : p;
        return v;
    }

    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (key == null || remappingFunction == null) throw new NullPointerException();
        Node<K, V> n;
        V v;
        while ((n = findNode(key)) != null) {
            if ((v = valOf(n)) != null) {
                V r = remappingFunction.apply(key, v);
                if (r != null) {
                    if (casVal(n, v, r)) return r;
                } else if (doRemove(key, v) != null) {
                    break;
                }
            }
        }
        return null;
    }

    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (key == null || remappingFunction == null) throw new NullPointerException();
        for (;;) {
            Node<K, V> n;
            V v;
            V r;
            if ((n = findNode(key)) == null) {
                if ((r = remappingFunction.apply(key, null)) == null) break;
                if (doPut(key, r, true) == null) return r;
            } else if ((v = valOf(n)) != null) {
                if ((r = remappingFunction.apply(key, v)) != null) {
                    if (casVal(n, v, r)) return r;
                } else if (doRemove(key, v) != null) {
                    break;
                }
            }
        }
        return null;
    }

    public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (key == null || value == null || remappingFunction == null) throw new NullPointerException();
        for (;;) {
            Node<K, V> n;
            V v;
            V r;
            if ((n = findNode(key)) == null) {
                if (doPut(key, value, true) == null) return value;
            } else if ((v = valOf(n)) != null) {
                if ((r = remappingFunction.apply(v, value)) != null) {
                    if (casVal(n, v, r)) return r;
                } else if (doRemove(key, v) != null) {
                    return null;
                }
            }
        }
    }

    // ---------------- views ----------------

    public NavigableSet<K> keySet() {
        KeySet<K, V> ks;
        if ((ks = keySet) != null) return ks;
        return keySet = new KeySet<>(this);
    }

    public NavigableSet<K> navigableKeySet() {
        KeySet<K, V> ks;
        if ((ks = keySet) != null) return ks;
        return keySet = new KeySet<>(this);
    }

    public Collection<V> values() {
        Values<K, V> vs;
        if ((vs = values) != null) return vs;
        return values = new Values<>(this);
    }

    public Set<Map.Entry<K, V>> entrySet() {
        EntrySet<K, V> es;
        if ((es = entrySet) != null) return es;
        return entrySet = new EntrySet<K, V>(this);
    }

    public ConcurrentNavigableMap<K, V> descendingMap() {
        ConcurrentNavigableMap<K, V> dm;
        if ((dm = descendingMap) != null) return dm;
        return descendingMap = new SubMap<K, V>(this, null, false, null, false, true);
    }

    public NavigableSet<K> descendingKeySet() {
        return descendingMap().navigableKeySet();
    }

    // ---------------- AbstractMap overrides ----------------

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Map)) return false;
        Map<?, ?> m = (Map<?, ?>) o;
        try {
            Comparator<? super K> cmp = comparator;
            Iterator<? extends Map.Entry<?, ?>> it = m.entrySet().iterator();
            if (m instanceof SortedMap && ((SortedMap<?, ?>) m).comparator() == cmp) {
                Node<K, V> b, n;
                if ((b = baseHead()) != null) {
                    while ((n = nextOf(b)) != null) {
                        K k;
                        V v;
                        if ((v = valOf(n)) != null && (k = n.key) != null) {
                            if (!it.hasNext()) return false;
                            Map.Entry<?, ?> e = it.next();
                            Object mk = e.getKey();
                            Object mv = e.getValue();
                            if (mk == null || mv == null) return false;
                            try {
                                if (cpr(cmp, k, mk) != 0) return false;
                            } catch (ClassCastException cce) {
                                return false;
                            }
                            if (!mv.equals(v)) return false;
                        }
                        b = n;
                    }
                }
                return !it.hasNext();
            } else {
                while (it.hasNext()) {
                    V v;
                    Map.Entry<?, ?> e = it.next();
                    Object mk = e.getKey();
                    Object mv = e.getValue();
                    if (mk == null || mv == null || (v = get(mk)) == null || !v.equals(mv)) return false;
                }
                Node<K, V> b, n;
                if ((b = baseHead()) != null) {
                    K k;
                    V v;
                    Object mv;
                    while ((n = nextOf(b)) != null) {
                        if ((v = valOf(n)) != null && (k = n.key) != null && ((mv = m.get(k)) == null || !mv.equals(v)))
                            return false;
                        b = n;
                    }
                }
                return true;
            }
        } catch (ClassCastException | NullPointerException unused) {
            return false;
        }
    }

    // ---------------- ConcurrentMap API ----------------

    public V putIfAbsent(K key, V value) {
        if (value == null) throw new NullPointerException();
        return doPut(key, value, true);
    }

    public boolean remove(Object key, Object value) {
        if (key == null) throw new NullPointerException();
        return value != null && doRemove(key, value) != null;
    }

    public boolean replace(K key, V oldValue, V newValue) {
        if (key == null || oldValue == null || newValue == null) throw new NullPointerException();
        for (;;) {
            Node<K, V> n;
            V v;
            if ((n = findNode(key)) == null) return false;
            if ((v = valOf(n)) != null) {
                if (!oldValue.equals(v)) return false;
                if (casVal(n, v, newValue)) return true;
            }
        }
    }

    public V replace(K key, V value) {
        if (key == null || value == null) throw new NullPointerException();
        for (;;) {
            Node<K, V> n;
            V v;
            if ((n = findNode(key)) == null) return null;
            if ((v = valOf(n)) != null && casVal(n, v, value)) return v;
        }
    }

    // ---------------- SortedMap API ----------------

    public Comparator<? super K> comparator() {
        return comparator;
    }

    public K firstKey() {
        Node<K, V> n = findFirst();
        if (n == null) throw new NoSuchElementException();
        return n.key;
    }

    public K lastKey() {
        Node<K, V> n = findLast();
        if (n == null) throw new NoSuchElementException();
        return n.key;
    }

    public ConcurrentNavigableMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
        if (fromKey == null || toKey == null) throw new NullPointerException();
        return new SubMap<K, V>(this, fromKey, fromInclusive, toKey, toInclusive, false);
    }

    public ConcurrentNavigableMap<K, V> headMap(K toKey, boolean inclusive) {
        if (toKey == null) throw new NullPointerException();
        return new SubMap<K, V>(this, null, false, toKey, inclusive, false);
    }

    public ConcurrentNavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
        if (fromKey == null) throw new NullPointerException();
        return new SubMap<K, V>(this, fromKey, inclusive, null, false, false);
    }

    public ConcurrentNavigableMap<K, V> subMap(K fromKey, K toKey) {
        return subMap(fromKey, true, toKey, false);
    }

    public ConcurrentNavigableMap<K, V> headMap(K toKey) {
        return headMap(toKey, false);
    }

    public ConcurrentNavigableMap<K, V> tailMap(K fromKey) {
        return tailMap(fromKey, true);
    }

    // ---------------- relational operations ----------------

    public Map.Entry<K, V> lowerEntry(K key) { return findNearEntry(key, LT, comparator); }

    public K lowerKey(K key) {
        Node<K, V> n = findNear(key, LT, comparator);
        return (n == null) ? null : n.key;
    }

    public Map.Entry<K, V> floorEntry(K key) { return findNearEntry(key, LT | EQ, comparator); }

    public K floorKey(K key) {
        Node<K, V> n = findNear(key, LT | EQ, comparator);
        return (n == null) ? null : n.key;
    }

    public Map.Entry<K, V> ceilingEntry(K key) { return findNearEntry(key, GT | EQ, comparator); }

    public K ceilingKey(K key) {
        Node<K, V> n = findNear(key, GT | EQ, comparator);
        return (n == null) ? null : n.key;
    }

    public Map.Entry<K, V> higherEntry(K key) { return findNearEntry(key, GT, comparator); }

    public K higherKey(K key) {
        Node<K, V> n = findNear(key, GT, comparator);
        return (n == null) ? null : n.key;
    }

    public Map.Entry<K, V> firstEntry() { return findFirstEntry(); }

    public Map.Entry<K, V> lastEntry() { return findLastEntry(); }

    public Map.Entry<K, V> pollFirstEntry() { return doRemoveFirstEntry(); }

    public Map.Entry<K, V> pollLastEntry() { return doRemoveLastEntry(); }

    // ---------------- iterators ----------------

    abstract class Iter<T> implements Iterator<T> {
        Node<K, V> lastReturned;
        Node<K, V> next;
        V nextValue;

        Iter() {
            advance(baseHead());
        }

        public final boolean hasNext() {
            return next != null;
        }

        /** From b (the node returned last): the next live node and its value, read now. */
        final void advance(Node<K, V> b) {
            Node<K, V> n = null;
            V v = null;
            synchronized (lock) {
                if ((lastReturned = b) != null) {
                    while ((n = b.next) != null && (v = n.val) == null) b = n;
                }
            }
            nextValue = v;
            next = n;
        }

        public final void remove() {
            Node<K, V> n;
            K k;
            if ((n = lastReturned) == null || (k = n.key) == null) throw new IllegalStateException();
            ConcurrentSkipListMap.this.remove(k);
            lastReturned = null;
        }
    }

    final class ValueIterator extends Iter<V> {
        public V next() {
            V v;
            if ((v = nextValue) == null) throw new NoSuchElementException();
            advance(next);
            return v;
        }
    }

    final class KeyIterator extends Iter<K> {
        public K next() {
            Node<K, V> n;
            if ((n = next) == null) throw new NoSuchElementException();
            K k = n.key;
            advance(n);
            return k;
        }
    }

    final class EntryIterator extends Iter<Map.Entry<K, V>> {
        public Map.Entry<K, V> next() {
            Node<K, V> n;
            if ((n = next) == null) throw new NoSuchElementException();
            K k = n.key;
            V v = nextValue;
            advance(n);
            return new AbstractMap.SimpleImmutableEntry<K, V>(k, v);
        }
    }

    // ---------------- view classes ----------------

    static final <E> List<E> toList(Collection<E> c) {
        ArrayList<E> list = new ArrayList<E>();
        for (E e : c) list.add(e);
        return list;
    }

    static final class KeySet<K, V> extends AbstractSet<K> implements NavigableSet<K> {
        final ConcurrentNavigableMap<K, V> m;
        KeySet(ConcurrentNavigableMap<K, V> map) { m = map; }
        public int size() { return m.size(); }
        public boolean isEmpty() { return m.isEmpty(); }
        public boolean contains(Object o) { return m.containsKey(o); }
        public boolean remove(Object o) { return m.remove(o) != null; }
        public void clear() { m.clear(); }
        public K lower(K e) { return m.lowerKey(e); }
        public K floor(K e) { return m.floorKey(e); }
        public K ceiling(K e) { return m.ceilingKey(e); }
        public K higher(K e) { return m.higherKey(e); }
        public Comparator<? super K> comparator() { return m.comparator(); }
        public K first() { return m.firstKey(); }
        public K last() { return m.lastKey(); }
        public K pollFirst() {
            Map.Entry<K, V> e = m.pollFirstEntry();
            return (e == null) ? null : e.getKey();
        }
        public K pollLast() {
            Map.Entry<K, V> e = m.pollLastEntry();
            return (e == null) ? null : e.getKey();
        }
        public Iterator<K> iterator() {
            return (m instanceof ConcurrentSkipListMap)
                ? ((ConcurrentSkipListMap<K, V>) m).new KeyIterator()
                : ((SubMap<K, V>) m).new SubMapKeyIterator();
        }
        public boolean equals(Object o) {
            if (o == this) return true;
            if (!(o instanceof Set)) return false;
            Collection<?> c = (Collection<?>) o;
            try {
                return containsAll(c) && c.containsAll(this);
            } catch (ClassCastException | NullPointerException unused) {
                return false;
            }
        }
        public Object[] toArray() { return toList(this).toArray(); }
        public <T> T[] toArray(T[] a) { return toList(this).toArray(a); }
        public Iterator<K> descendingIterator() { return descendingSet().iterator(); }
        public NavigableSet<K> subSet(K fromElement, boolean fromInclusive, K toElement, boolean toInclusive) {
            return new KeySet<>(m.subMap(fromElement, fromInclusive, toElement, toInclusive));
        }
        public NavigableSet<K> headSet(K toElement, boolean inclusive) { return new KeySet<>(m.headMap(toElement, inclusive)); }
        public NavigableSet<K> tailSet(K fromElement, boolean inclusive) { return new KeySet<>(m.tailMap(fromElement, inclusive)); }
        public NavigableSet<K> subSet(K fromElement, K toElement) { return subSet(fromElement, true, toElement, false); }
        public NavigableSet<K> headSet(K toElement) { return headSet(toElement, false); }
        public NavigableSet<K> tailSet(K fromElement) { return tailSet(fromElement, true); }
        public NavigableSet<K> descendingSet() { return new KeySet<>(m.descendingMap()); }
    }

    static final class Values<K, V> extends AbstractCollection<V> {
        final ConcurrentNavigableMap<K, V> m;
        Values(ConcurrentNavigableMap<K, V> map) { m = map; }
        public Iterator<V> iterator() {
            return (m instanceof ConcurrentSkipListMap)
                ? ((ConcurrentSkipListMap<K, V>) m).new ValueIterator()
                : ((SubMap<K, V>) m).new SubMapValueIterator();
        }
        public int size() { return m.size(); }
        public boolean isEmpty() { return m.isEmpty(); }
        public boolean contains(Object o) { return m.containsValue(o); }
        public void clear() { m.clear(); }
        public Object[] toArray() { return toList(this).toArray(); }
        public <T> T[] toArray(T[] a) { return toList(this).toArray(a); }
        public boolean removeIf(Predicate<? super V> filter) {
            if (filter == null) throw new NullPointerException();
            if (m instanceof ConcurrentSkipListMap) return ((ConcurrentSkipListMap<K, V>) m).removeValueIf(filter);
            Iterator<Map.Entry<K, V>> it = ((SubMap<K, V>) m).new SubMapEntryIterator();
            boolean removed = false;
            while (it.hasNext()) {
                Map.Entry<K, V> e = it.next();
                V v = e.getValue();
                if (filter.test(v) && m.remove(e.getKey(), v)) removed = true;
            }
            return removed;
        }
    }

    static final class EntrySet<K, V> extends AbstractSet<Map.Entry<K, V>> {
        final ConcurrentNavigableMap<K, V> m;
        EntrySet(ConcurrentNavigableMap<K, V> map) { m = map; }
        public Iterator<Map.Entry<K, V>> iterator() {
            return (m instanceof ConcurrentSkipListMap)
                ? ((ConcurrentSkipListMap<K, V>) m).new EntryIterator()
                : ((SubMap<K, V>) m).new SubMapEntryIterator();
        }
        public boolean contains(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            V v = m.get(e.getKey());
            return v != null && v.equals(e.getValue());
        }
        public boolean remove(Object o) {
            if (!(o instanceof Map.Entry)) return false;
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            return m.remove(e.getKey(), e.getValue());
        }
        public boolean isEmpty() { return m.isEmpty(); }
        public int size() { return m.size(); }
        public void clear() { m.clear(); }
        public boolean equals(Object o) {
            if (o == this) return true;
            if (!(o instanceof Set)) return false;
            Collection<?> c = (Collection<?>) o;
            try {
                return containsAll(c) && c.containsAll(this);
            } catch (ClassCastException | NullPointerException unused) {
                return false;
            }
        }
        public Object[] toArray() { return toList(this).toArray(); }
        public <T> T[] toArray(T[] a) { return toList(this).toArray(a); }
        public boolean removeIf(Predicate<? super Entry<K, V>> filter) {
            if (filter == null) throw new NullPointerException();
            if (m instanceof ConcurrentSkipListMap) return ((ConcurrentSkipListMap<K, V>) m).removeEntryIf(filter);
            Iterator<Map.Entry<K, V>> it = ((SubMap<K, V>) m).new SubMapEntryIterator();
            boolean removed = false;
            while (it.hasNext()) {
                Map.Entry<K, V> e = it.next();
                if (filter.test(e) && m.remove(e.getKey(), e.getValue())) removed = true;
            }
            return removed;
        }
    }

    // ---------------- sub maps ----------------

    static final class SubMap<K, V> extends AbstractMap<K, V> implements ConcurrentNavigableMap<K, V>, java.io.Serializable {
        private static final long serialVersionUID = -7647078645895051609L;
        final ConcurrentSkipListMap<K, V> m;
        @SuppressWarnings("serial")
        private final K lo;
        @SuppressWarnings("serial")
        private final K hi;
        private final boolean loInclusive;
        private final boolean hiInclusive;
        final boolean isDescending;
        private transient KeySet<K, V> keySetView;
        private transient Values<K, V> valuesView;
        private transient EntrySet<K, V> entrySetView;

        SubMap(ConcurrentSkipListMap<K, V> map, K fromKey, boolean fromInclusive, K toKey, boolean toInclusive, boolean isDescending) {
            Comparator<? super K> cmp = map.comparator;
            if (fromKey != null && toKey != null && cpr(cmp, fromKey, toKey) > 0)
                throw new IllegalArgumentException("inconsistent range");
            this.m = map;
            this.lo = fromKey;
            this.hi = toKey;
            this.loInclusive = fromInclusive;
            this.hiInclusive = toInclusive;
            this.isDescending = isDescending;
        }

        boolean tooLow(Object key, Comparator<? super K> cmp) {
            int c;
            return (lo != null && ((c = cpr(cmp, key, lo)) < 0 || (c == 0 && !loInclusive)));
        }

        boolean tooHigh(Object key, Comparator<? super K> cmp) {
            int c;
            return (hi != null && ((c = cpr(cmp, key, hi)) > 0 || (c == 0 && !hiInclusive)));
        }

        boolean inBounds(Object key, Comparator<? super K> cmp) {
            return !tooLow(key, cmp) && !tooHigh(key, cmp);
        }

        void checkKeyBounds(K key, Comparator<? super K> cmp) {
            if (key == null) throw new NullPointerException();
            if (!inBounds(key, cmp)) throw new IllegalArgumentException("key out of range");
        }

        boolean isBeforeEnd(ConcurrentSkipListMap.Node<K, V> n, Comparator<? super K> cmp) {
            if (n == null) return false;
            if (hi == null) return true;
            K k = n.key;
            if (k == null) return true;
            int c = cpr(cmp, k, hi);
            return c < 0 || (c == 0 && hiInclusive);
        }

        ConcurrentSkipListMap.Node<K, V> loNode(Comparator<? super K> cmp) {
            if (lo == null) return m.findFirst();
            else if (loInclusive) return m.findNear(lo, GT | EQ, cmp);
            else return m.findNear(lo, GT, cmp);
        }

        ConcurrentSkipListMap.Node<K, V> hiNode(Comparator<? super K> cmp) {
            if (hi == null) return m.findLast();
            else if (hiInclusive) return m.findNear(hi, LT | EQ, cmp);
            else return m.findNear(hi, LT, cmp);
        }

        K lowestKey() {
            Comparator<? super K> cmp = m.comparator;
            ConcurrentSkipListMap.Node<K, V> n = loNode(cmp);
            if (isBeforeEnd(n, cmp)) return n.key;
            else throw new NoSuchElementException();
        }

        K highestKey() {
            Comparator<? super K> cmp = m.comparator;
            ConcurrentSkipListMap.Node<K, V> n = hiNode(cmp);
            if (n != null) {
                K last = n.key;
                if (inBounds(last, cmp)) return last;
            }
            throw new NoSuchElementException();
        }

        Map.Entry<K, V> lowestEntry() {
            Comparator<? super K> cmp = m.comparator;
            for (;;) {
                ConcurrentSkipListMap.Node<K, V> n;
                V v;
                if ((n = loNode(cmp)) == null || !isBeforeEnd(n, cmp)) return null;
                else if ((v = m.valOf(n)) != null) return new AbstractMap.SimpleImmutableEntry<K, V>(n.key, v);
            }
        }

        Map.Entry<K, V> highestEntry() {
            Comparator<? super K> cmp = m.comparator;
            for (;;) {
                ConcurrentSkipListMap.Node<K, V> n;
                V v;
                if ((n = hiNode(cmp)) == null || !inBounds(n.key, cmp)) return null;
                else if ((v = m.valOf(n)) != null) return new AbstractMap.SimpleImmutableEntry<K, V>(n.key, v);
            }
        }

        Map.Entry<K, V> removeLowest() {
            Comparator<? super K> cmp = m.comparator;
            for (;;) {
                ConcurrentSkipListMap.Node<K, V> n;
                K k;
                V v;
                if ((n = loNode(cmp)) == null) return null;
                else if (!inBounds((k = n.key), cmp)) return null;
                else if ((v = m.doRemove(k, null)) != null) return new AbstractMap.SimpleImmutableEntry<K, V>(k, v);
            }
        }

        Map.Entry<K, V> removeHighest() {
            Comparator<? super K> cmp = m.comparator;
            for (;;) {
                ConcurrentSkipListMap.Node<K, V> n;
                K k;
                V v;
                if ((n = hiNode(cmp)) == null) return null;
                else if (!inBounds((k = n.key), cmp)) return null;
                else if ((v = m.doRemove(k, null)) != null) return new AbstractMap.SimpleImmutableEntry<K, V>(k, v);
            }
        }

        Map.Entry<K, V> getNearEntry(K key, int rel) {
            Comparator<? super K> cmp = m.comparator;
            if (isDescending) {
                if ((rel & LT) == 0) rel |= LT;
                else rel &= ~LT;
            }
            if (tooLow(key, cmp)) return ((rel & LT) != 0) ? null : lowestEntry();
            if (tooHigh(key, cmp)) return ((rel & LT) != 0) ? highestEntry() : null;
            AbstractMap.SimpleImmutableEntry<K, V> e = m.findNearEntry(key, rel, cmp);
            if (e == null || !inBounds(e.getKey(), cmp)) return null;
            else return e;
        }

        K getNearKey(K key, int rel) {
            Comparator<? super K> cmp = m.comparator;
            if (isDescending) {
                if ((rel & LT) == 0) rel |= LT;
                else rel &= ~LT;
            }
            if (tooLow(key, cmp)) {
                if ((rel & LT) == 0) {
                    ConcurrentSkipListMap.Node<K, V> n = loNode(cmp);
                    if (isBeforeEnd(n, cmp)) return n.key;
                }
                return null;
            }
            if (tooHigh(key, cmp)) {
                if ((rel & LT) != 0) {
                    ConcurrentSkipListMap.Node<K, V> n = hiNode(cmp);
                    if (n != null) {
                        K last = n.key;
                        if (inBounds(last, cmp)) return last;
                    }
                }
                return null;
            }
            for (;;) {
                Node<K, V> n = m.findNear(key, rel, cmp);
                if (n == null || !inBounds(n.key, cmp)) return null;
                if (m.valOf(n) != null) return n.key;
            }
        }

        public boolean containsKey(Object key) {
            if (key == null) throw new NullPointerException();
            return inBounds(key, m.comparator) && m.containsKey(key);
        }

        public V get(Object key) {
            if (key == null) throw new NullPointerException();
            return (!inBounds(key, m.comparator)) ? null : m.get(key);
        }

        public V put(K key, V value) {
            checkKeyBounds(key, m.comparator);
            return m.put(key, value);
        }

        public V remove(Object key) {
            return (!inBounds(key, m.comparator)) ? null : m.remove(key);
        }

        public int size() {
            Comparator<? super K> cmp = m.comparator;
            long count = 0;
            for (ConcurrentSkipListMap.Node<K, V> n = loNode(cmp); isBeforeEnd(n, cmp); n = m.nextOf(n)) {
                if (m.valOf(n) != null) ++count;
            }
            return count >= Integer.MAX_VALUE ? Integer.MAX_VALUE : (int) count;
        }

        public boolean isEmpty() {
            Comparator<? super K> cmp = m.comparator;
            return !isBeforeEnd(loNode(cmp), cmp);
        }

        public boolean containsValue(Object value) {
            if (value == null) throw new NullPointerException();
            Comparator<? super K> cmp = m.comparator;
            for (ConcurrentSkipListMap.Node<K, V> n = loNode(cmp); isBeforeEnd(n, cmp); n = m.nextOf(n)) {
                V v = m.valOf(n);
                if (v != null && value.equals(v)) return true;
            }
            return false;
        }

        public void clear() {
            Comparator<? super K> cmp = m.comparator;
            for (ConcurrentSkipListMap.Node<K, V> n = loNode(cmp); isBeforeEnd(n, cmp); n = m.nextOf(n)) {
                if (m.valOf(n) != null) m.remove(n.key);
            }
        }

        public V putIfAbsent(K key, V value) {
            checkKeyBounds(key, m.comparator);
            return m.putIfAbsent(key, value);
        }

        public boolean remove(Object key, Object value) {
            return inBounds(key, m.comparator) && m.remove(key, value);
        }

        public boolean replace(K key, V oldValue, V newValue) {
            checkKeyBounds(key, m.comparator);
            return m.replace(key, oldValue, newValue);
        }

        public V replace(K key, V value) {
            checkKeyBounds(key, m.comparator);
            return m.replace(key, value);
        }

        public Comparator<? super K> comparator() {
            Comparator<? super K> cmp = m.comparator();
            if (isDescending) return Collections.reverseOrder(cmp);
            else return cmp;
        }

        SubMap<K, V> newSubMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
            Comparator<? super K> cmp = m.comparator;
            if (isDescending) {
                K tk = fromKey;
                fromKey = toKey;
                toKey = tk;
                boolean ti = fromInclusive;
                fromInclusive = toInclusive;
                toInclusive = ti;
            }
            if (lo != null) {
                if (fromKey == null) {
                    fromKey = lo;
                    fromInclusive = loInclusive;
                } else {
                    int c = cpr(cmp, fromKey, lo);
                    if (c < 0 || (c == 0 && !loInclusive && fromInclusive)) throw new IllegalArgumentException("key out of range");
                }
            }
            if (hi != null) {
                if (toKey == null) {
                    toKey = hi;
                    toInclusive = hiInclusive;
                } else {
                    int c = cpr(cmp, toKey, hi);
                    if (c > 0 || (c == 0 && !hiInclusive && toInclusive)) throw new IllegalArgumentException("key out of range");
                }
            }
            return new SubMap<K, V>(m, fromKey, fromInclusive, toKey, toInclusive, isDescending);
        }

        public SubMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
            if (fromKey == null || toKey == null) throw new NullPointerException();
            return newSubMap(fromKey, fromInclusive, toKey, toInclusive);
        }

        public SubMap<K, V> headMap(K toKey, boolean inclusive) {
            if (toKey == null) throw new NullPointerException();
            return newSubMap(null, false, toKey, inclusive);
        }

        public SubMap<K, V> tailMap(K fromKey, boolean inclusive) {
            if (fromKey == null) throw new NullPointerException();
            return newSubMap(fromKey, inclusive, null, false);
        }

        public SubMap<K, V> subMap(K fromKey, K toKey) { return subMap(fromKey, true, toKey, false); }

        public SubMap<K, V> headMap(K toKey) { return headMap(toKey, false); }

        public SubMap<K, V> tailMap(K fromKey) { return tailMap(fromKey, true); }

        public SubMap<K, V> descendingMap() {
            return new SubMap<K, V>(m, lo, loInclusive, hi, hiInclusive, !isDescending);
        }

        public Map.Entry<K, V> ceilingEntry(K key) { return getNearEntry(key, GT | EQ); }
        public K ceilingKey(K key) { return getNearKey(key, GT | EQ); }
        public Map.Entry<K, V> lowerEntry(K key) { return getNearEntry(key, LT); }
        public K lowerKey(K key) { return getNearKey(key, LT); }
        public Map.Entry<K, V> floorEntry(K key) { return getNearEntry(key, LT | EQ); }
        public K floorKey(K key) { return getNearKey(key, LT | EQ); }
        public Map.Entry<K, V> higherEntry(K key) { return getNearEntry(key, GT); }
        public K higherKey(K key) { return getNearKey(key, GT); }
        public K firstKey() { return isDescending ? highestKey() : lowestKey(); }
        public K lastKey() { return isDescending ? lowestKey() : highestKey(); }
        public Map.Entry<K, V> firstEntry() { return isDescending ? highestEntry() : lowestEntry(); }
        public Map.Entry<K, V> lastEntry() { return isDescending ? lowestEntry() : highestEntry(); }
        public Map.Entry<K, V> pollFirstEntry() { return isDescending ? removeHighest() : removeLowest(); }
        public Map.Entry<K, V> pollLastEntry() { return isDescending ? removeLowest() : removeHighest(); }

        public NavigableSet<K> keySet() {
            KeySet<K, V> ks;
            if ((ks = keySetView) != null) return ks;
            return keySetView = new KeySet<>(this);
        }

        public NavigableSet<K> navigableKeySet() {
            KeySet<K, V> ks;
            if ((ks = keySetView) != null) return ks;
            return keySetView = new KeySet<>(this);
        }

        public Collection<V> values() {
            Values<K, V> vs;
            if ((vs = valuesView) != null) return vs;
            return valuesView = new Values<>(this);
        }

        public Set<Map.Entry<K, V>> entrySet() {
            EntrySet<K, V> es;
            if ((es = entrySetView) != null) return es;
            return entrySetView = new EntrySet<K, V>(this);
        }

        public NavigableSet<K> descendingKeySet() {
            return descendingMap().navigableKeySet();
        }

        abstract class SubMapIter<T> implements Iterator<T> {
            Node<K, V> lastReturned;
            Node<K, V> next;
            V nextValue;

            SubMapIter() {
                Comparator<? super K> cmp = m.comparator;
                for (;;) {
                    next = isDescending ? hiNode(cmp) : loNode(cmp);
                    if (next == null) break;
                    V x = m.valOf(next);
                    if (x != null) {
                        if (!inBounds(next.key, cmp)) next = null;
                        else nextValue = x;
                        break;
                    }
                }
            }

            public final boolean hasNext() {
                return next != null;
            }

            final void advance() {
                if (next == null) throw new NoSuchElementException();
                lastReturned = next;
                if (isDescending) descend();
                else ascend();
            }

            private void ascend() {
                Comparator<? super K> cmp = m.comparator;
                for (;;) {
                    next = m.nextOf(next);
                    if (next == null) break;
                    V x = m.valOf(next);
                    if (x != null) {
                        if (tooHigh(next.key, cmp)) next = null;
                        else nextValue = x;
                        break;
                    }
                }
            }

            private void descend() {
                Comparator<? super K> cmp = m.comparator;
                for (;;) {
                    next = m.findNear(lastReturned.key, LT, cmp);
                    if (next == null) break;
                    V x = m.valOf(next);
                    if (x != null) {
                        if (tooLow(next.key, cmp)) next = null;
                        else nextValue = x;
                        break;
                    }
                }
            }

            public void remove() {
                Node<K, V> l = lastReturned;
                if (l == null) throw new IllegalStateException();
                m.remove(l.key);
                lastReturned = null;
            }
        }

        final class SubMapValueIterator extends SubMapIter<V> {
            public V next() {
                V v = nextValue;
                advance();
                return v;
            }
        }

        final class SubMapKeyIterator extends SubMapIter<K> {
            public K next() {
                Node<K, V> n = next;
                advance();
                return n.key;
            }
        }

        final class SubMapEntryIterator extends SubMapIter<Map.Entry<K, V>> {
            public Map.Entry<K, V> next() {
                Node<K, V> n = next;
                V v = nextValue;
                advance();
                return new AbstractMap.SimpleImmutableEntry<K, V>(n.key, v);
            }
        }
    }

    // ---------------- bulk operations ----------------

    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        Node<K, V> b, n;
        V v;
        if ((b = baseHead()) != null) {
            while ((n = nextOf(b)) != null) {
                if ((v = valOf(n)) != null) action.accept(n.key, v);
                b = n;
            }
        }
    }

    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        Node<K, V> b, n;
        V v;
        if ((b = baseHead()) != null) {
            while ((n = nextOf(b)) != null) {
                while ((v = valOf(n)) != null) {
                    V r = function.apply(n.key, v);
                    if (r == null) throw new NullPointerException();
                    if (casVal(n, v, r)) break;
                }
                b = n;
            }
        }
    }

    boolean removeEntryIf(Predicate<? super Entry<K, V>> function) {
        if (function == null) throw new NullPointerException();
        boolean removed = false;
        Node<K, V> b, n;
        V v;
        if ((b = baseHead()) != null) {
            while ((n = nextOf(b)) != null) {
                if ((v = valOf(n)) != null) {
                    K k = n.key;
                    Map.Entry<K, V> e = new AbstractMap.SimpleImmutableEntry<>(k, v);
                    if (function.test(e) && remove(k, v)) removed = true;
                }
                b = n;
            }
        }
        return removed;
    }

    boolean removeValueIf(Predicate<? super V> function) {
        if (function == null) throw new NullPointerException();
        boolean removed = false;
        Node<K, V> b, n;
        V v;
        if ((b = baseHead()) != null) {
            while ((n = nextOf(b)) != null) {
                if ((v = valOf(n)) != null && function.test(v) && remove(n.key, v)) removed = true;
                b = n;
            }
        }
        return removed;
    }
}

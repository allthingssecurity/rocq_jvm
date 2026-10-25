/*
 * rocq-jvm model of java.util.concurrent.ConcurrentHashMap (clean-room, Apache-2.0).
 *
 * Written from the Javadoc, from the published description of the algorithm (bins locked on
 * their first node, lists appended at the tail, red-black "tree bins" whose list is kept in its
 * own order with new nodes in front, resizing by doubling with forwarding markers, the
 * load factor used only for the initial size) and from black-box measurements of JDK 21
 * (table length and iteration order after every operation, read reflectively), NOT from
 * OpenJDK source.  The observable behaviour (return values, exceptions incl. "Recursive update",
 * iteration order, view semantics) is checked against JDK 21 by differential tests
 * (harness/jdkmodel/tests ChmOps) and, with threads, by the thread-layer tests (ChmThreads).
 *
 * Concurrency (for the thread layer of the machine, sequentially consistent):
 * - writes lock the bin's first node (synchronized), re-check it, then change the bin, as the
 *   real map does; an empty bin is filled by a compare-and-set (here: a short critical section
 *   on [ctl]); computeIfAbsent/compute on an empty bin park a ReservationNode while the
 *   function runs;
 * - reads (get, iteration) take no lock; a tree bin is searched along its list;
 * - one thread at a time resizes (the real map lets other writers help); a writer that meets a
 *   forwarding marker waits until the resize is over and retries; readers follow the marker;
 * - the element count is a single counter (the real map spreads it over cells).
 * Not modelled (STUCK): the bulk parallel operations (forEach/search/reduce with a
 * parallelism threshold), spliterator/stream, serialization, clone, keys whose tree-bin order
 * needs the identity hash code or a Comparable class other than String and the boxes.
 */
package java.util.concurrent;

import java.util.AbstractCollection;
import java.util.Collection;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;

public class ConcurrentHashMap<K, V> extends java.util.AbstractMap<K, V>
        implements ConcurrentMap<K, V>, java.io.Serializable {

    static final int MAXIMUM_CAPACITY = 1 << 30;
    static final int DEFAULT_CAPACITY = 16;
    static final int TREEIFY_THRESHOLD = 8;
    static final int UNTREEIFY_THRESHOLD = 6;
    static final int MIN_TREEIFY_CAPACITY = 64;
    static final int MOVED = -1;      // hash of a forwarding marker
    static final int TREEBIN = -2;    // hash of a tree bin's head
    static final int RESERVED = -3;   // hash of a reservation
    static final int HASH_BITS = 0x7fffffff;

    // ---- nodes ----

    static class Node<K, V> implements Map.Entry<K, V> {
        final int hash;
        final K key;
        volatile V val;
        volatile Node<K, V> next;

        Node(int hash, K key, V val) {
            this.hash = hash;
            this.key = key;
            this.val = val;
        }

        Node(int hash, K key, V val, Node<K, V> next) {
            this(hash, key, val);
            this.next = next;
        }

        public final K getKey() {
            return key;
        }

        public final V getValue() {
            return val;
        }

        public final int hashCode() {
            return key.hashCode() ^ val.hashCode();
        }

        public final String toString() {
            return key + "=" + val;
        }

        public final V setValue(V value) {
            throw new UnsupportedOperationException();
        }

        public final boolean equals(Object o) {
            Object k, v, u;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry) && (k = (e = (Map.Entry<?, ?>) o).getKey()) != null
                    && (v = e.getValue()) != null && (k == key || k.equals(key))
                    && (v == (u = val) || v.equals(u)));
        }

        /** The node of key k (hash h) in the bin that starts here, or null. */
        Node<K, V> find(int h, Object k) {
            Node<K, V> e = this;
            if (k != null) {
                do {
                    K ek;
                    if (e.hash == h && ((ek = e.key) == k || (ek != null && k.equals(ek)))) return e;
                } while ((e = e.next) != null);
            }
            return null;
        }
    }

    static final class ForwardingNode<K, V> extends Node<K, V> {
        final Node<K, V>[] nextTable;

        ForwardingNode(Node<K, V>[] tab) {
            super(MOVED, null, null);
            this.nextTable = tab;
        }

        Node<K, V> find(int h, Object k) {
            Node<K, V>[] tab = nextTable;
            for (;;) {
                Node<K, V> e;
                int n;
                if (k == null || tab == null || (n = tab.length) == 0 || (e = tab[(n - 1) & h]) == null) return null;
                if (e instanceof ForwardingNode) {
                    tab = ((ForwardingNode<K, V>) e).nextTable;
                    continue;
                }
                return e.find(h, k);
            }
        }
    }

    static final class ReservationNode<K, V> extends Node<K, V> {
        ReservationNode() {
            super(RESERVED, null, null);
        }

        Node<K, V> find(int h, Object k) {
            return null;
        }
    }

    static final int spread(int h) {
        return (h ^ (h >>> 16)) & HASH_BITS;
    }

    /** The smallest power of two >= c (1 for c <= 1), at most MAXIMUM_CAPACITY. */
    static final int tableSizeFor(int c) {
        int n = 1;
        while (n < c && n < MAXIMUM_CAPACITY) n <<= 1;
        return n;
    }

    // ---- state ----

    transient volatile Node<K, V>[] table;
    /** 0: no table yet, default size; > 0 before the table exists: its length; afterwards the
     *  count at which to resize (3/4 of the length); -1 while the table is being created or
     *  resized. */
    private transient volatile int sizeCtl;
    private transient volatile long baseCount;
    /** Guards sizeCtl, baseCount and the filling of empty bins (the real map uses CAS). */
    private final transient Object ctl = new Object();

    private transient KeySetView<K, V> keySet;
    private transient ValuesView<K, V> values;
    private transient EntrySetView<K, V> entrySet;

    // ---- constructors ----

    public ConcurrentHashMap() {
    }

    public ConcurrentHashMap(int initialCapacity) {
        this(initialCapacity, 0.75f, 1);
    }

    public ConcurrentHashMap(Map<? extends K, ? extends V> m) {
        this.sizeCtl = DEFAULT_CAPACITY;
        putAll(m);
    }

    public ConcurrentHashMap(int initialCapacity, float loadFactor) {
        this(initialCapacity, loadFactor, 1);
    }

    public ConcurrentHashMap(int initialCapacity, float loadFactor, int concurrencyLevel) {
        if (!(loadFactor > 0.0f) || initialCapacity < 0 || concurrencyLevel <= 0) throw new IllegalArgumentException();
        if (initialCapacity < concurrencyLevel) initialCapacity = concurrencyLevel;
        long size = (long) (1.0 + (long) initialCapacity / loadFactor);
        this.sizeCtl = (size >= (long) MAXIMUM_CAPACITY) ? MAXIMUM_CAPACITY : tableSizeFor((int) size);
    }


    /** Mapping functions run with [fnDepth] > 0: a resize requested meanwhile (the function
     *  changed this map, which the Javadoc forbids) is not modelled. */
    private transient int fnDepth;

    private <T, R> R fn1(Function<? super T, ? extends R> f, T a) {
        fnDepth++;
        try {
            return f.apply(a);
        } finally {
            fnDepth--;
        }
    }

    private <T, U, R> R fn2(BiFunction<? super T, ? super U, ? extends R> f, T a, U b) {
        fnDepth++;
        try {
            return f.apply(a, b);
        } finally {
            fnDepth--;
        }
    }

    private void checkResizeAllowed() {
        if (fnDepth > 0) throw ModelStuck.unsupported("ConcurrentHashMap: resize while a mapping function runs");
    }

    // ---- table helpers ----

    /** Compare-and-set of an empty slot. */
    private boolean casEmpty(Node<K, V>[] tab, int i, Node<K, V> v) {
        synchronized (ctl) {
            if (tab[i] != null) return false;
            tab[i] = v;
            return true;
        }
    }

    private boolean casSlot(Node<K, V>[] tab, int i, Node<K, V> expect, Node<K, V> v) {
        synchronized (ctl) {
            if (tab[i] != expect) return false;
            tab[i] = v;
            return true;
        }
    }

    private Node<K, V>[] initTable() {
        Node<K, V>[] tab;
        while ((tab = table) == null || tab.length == 0) {
            int sc;
            boolean mine = false;
            synchronized (ctl) {
                if ((sc = sizeCtl) >= 0 && table == null) {
                    sizeCtl = -1;
                    mine = true;
                }
            }
            if (!mine) {
                Thread.yield();
                continue;
            }
            int n = (sc > 0) ? sc : DEFAULT_CAPACITY;
            @SuppressWarnings("unchecked")
            Node<K, V>[] nt = (Node<K, V>[]) new Node<?, ?>[n];
            table = tab = nt;
            synchronized (ctl) {
                sizeCtl = n - (n >>> 2);
            }
            break;
        }
        return tab;
    }

    /** A writer met a forwarding marker: wait for the resize to finish, return the new table. */
    private Node<K, V>[] awaitTransfer(Node<K, V>[] tab) {
        while (table == tab) Thread.yield();
        return table;
    }

    /** Add x to the count; if check >= 0 resize while the count has reached sizeCtl. */
    private void addCount(long x, int check) {
        long s;
        synchronized (ctl) {
            s = baseCount = baseCount + x;
        }
        if (check >= 0) {
            Node<K, V>[] tab;
            int n;
            for (;;) {
                boolean mine = false;
                int sc;
                synchronized (ctl) {
                    sc = sizeCtl;
                    if (sc >= 0 && s >= (long) sc && (tab = table) != null && (n = tab.length) < MAXIMUM_CAPACITY) {
                        sizeCtl = -1;
                        mine = true;
                    } else {
                        tab = null;
                        n = 0;
                    }
                }
                if (!mine) break;
                checkResizeAllowed();
                transfer(tab);
                synchronized (ctl) {
                    s = baseCount;
                }
            }
        }
    }

    /** Size the table for [size] more elements (putAll, and a long bin in a small table). */
    private void tryPresize(int size) {
        int c = (size >= (MAXIMUM_CAPACITY >>> 1)) ? MAXIMUM_CAPACITY : tableSizeFor(size + (size >>> 1) + 1);
        for (;;) {
            int sc;
            Node<K, V>[] tab;
            int n;
            boolean create = false, grow = false;
            synchronized (ctl) {
                sc = sizeCtl;
                if (sc < 0) return;
                tab = table;
                n = (tab == null) ? 0 : tab.length;
                if (n == 0) {
                    sizeCtl = -1;
                    create = true;
                } else if (c <= sc || n >= MAXIMUM_CAPACITY) {
                    return;
                } else {
                    sizeCtl = -1;
                    grow = true;
                }
            }
            if (create) {
                int len = (sc > c) ? sc : c;
                @SuppressWarnings("unchecked")
                Node<K, V>[] nt = (Node<K, V>[]) new Node<?, ?>[len];
                table = nt;
                synchronized (ctl) {
                    sizeCtl = len - (len >>> 2);
                }
            } else if (grow) {
                checkResizeAllowed();
                transfer(tab);
            }
        }
    }

    /** Double the table (sizeCtl is -1, held by this thread): move every bin, high index first,
     *  leave a forwarding marker in the old slot, then publish the new table. */
    private void transfer(Node<K, V>[] tab) {
        int n = tab.length;
        @SuppressWarnings("unchecked")
        Node<K, V>[] nextTab = (Node<K, V>[]) new Node<?, ?>[n << 1];
        ForwardingNode<K, V> fwd = new ForwardingNode<>(nextTab);
        try {
            for (int i = n - 1; i >= 0; i--) {
                for (;;) {
                    Node<K, V> f = tab[i];
                    if (f == null) {
                        if (casEmpty(tab, i, fwd)) break;
                        continue;
                    }
                    boolean done = false;
                    synchronized (f) {
                        if (tab[i] == f) {
                            moveBin(tab, nextTab, i, n, f);
                            tab[i] = fwd;
                            done = true;
                        }
                    }
                    if (done) break;
                }
            }
            table = nextTab;
            synchronized (ctl) {
                sizeCtl = (n << 1) - (n >>> 1);
            }
        } catch (RuntimeException | Error ex) {
            // "Recursive update" from a reserved bin: give the size control back
            synchronized (ctl) {
                sizeCtl = n - (n >>> 2);
            }
            throw ex;
        }
    }

    /** Split bin i of the old table (length n) into slots i and i + n of the new one. */
    private void moveBin(Node<K, V>[] tab, Node<K, V>[] nextTab, int i, int n, Node<K, V> f) {
        Node<K, V> ln, hn;
        if (f.hash >= 0) {
            // the longest tail whose nodes all go to the same slot is moved as it is; the nodes
            // before it are copied, each pushed in front of its slot's list
            int runBit = f.hash & n;
            Node<K, V> lastRun = f;
            for (Node<K, V> p = f.next; p != null; p = p.next) {
                int b = p.hash & n;
                if (b != runBit) {
                    runBit = b;
                    lastRun = p;
                }
            }
            if (runBit == 0) {
                ln = lastRun;
                hn = null;
            } else {
                hn = lastRun;
                ln = null;
            }
            for (Node<K, V> p = f; p != lastRun; p = p.next) {
                int ph = p.hash;
                K pk = p.key;
                V pv = p.val;
                if ((ph & n) == 0) ln = new Node<>(ph, pk, pv, ln);
                else hn = new Node<>(ph, pk, pv, hn);
            }
        } else if (f instanceof TreeBin) {
            TreeBin<K, V> t = (TreeBin<K, V>) f;
            TreeNode<K, V> lo = null, loTail = null, hi = null, hiTail = null;
            int lc = 0, hc = 0;
            for (Node<K, V> e = t.first; e != null; e = e.next) {
                int h = e.hash;
                TreeNode<K, V> p = new TreeNode<>(h, e.key, e.val, null, null);
                if ((h & n) == 0) {
                    if ((p.prev = loTail) == null) lo = p;
                    else loTail.next = p;
                    loTail = p;
                    ++lc;
                } else {
                    if ((p.prev = hiTail) == null) hi = p;
                    else hiTail.next = p;
                    hiTail = p;
                    ++hc;
                }
            }
            ln = (lc <= UNTREEIFY_THRESHOLD) ? untreeify(lo) : (hc != 0) ? new TreeBin<>(lo) : t;
            hn = (hc <= UNTREEIFY_THRESHOLD) ? untreeify(hi) : (lc != 0) ? new TreeBin<>(hi) : t;
        } else if (f instanceof ReservationNode) {
            throw new IllegalStateException("Recursive update");
        } else {
            ln = hn = null;
        }
        nextTab[i] = ln;
        nextTab[i + n] = hn;
    }

    /** A bin with TREEIFY_THRESHOLD nodes: grow a small table, else make the bin a tree. */
    private void treeifyBin(Node<K, V>[] tab, int index) {
        Node<K, V> b;
        if (tab != null) {
            int n = tab.length;
            if (n < MIN_TREEIFY_CAPACITY) {
                tryPresize(n << 1);
            } else if ((b = tab[index]) != null && b.hash >= 0) {
                synchronized (b) {
                    if (tab[index] == b) {
                        TreeNode<K, V> hd = null, tl = null;
                        for (Node<K, V> e = b; e != null; e = e.next) {
                            TreeNode<K, V> p = new TreeNode<>(e.hash, e.key, e.val, null, null);
                            if ((p.prev = tl) == null) hd = p;
                            else tl.next = p;
                            tl = p;
                        }
                        tab[index] = new TreeBin<>(hd);
                    }
                }
            }
        }
    }

    /** Plain nodes with the same keys and values, in list order. */
    static <K, V> Node<K, V> untreeify(Node<K, V> b) {
        Node<K, V> hd = null, tl = null;
        for (Node<K, V> q = b; q != null; q = q.next) {
            Node<K, V> p = new Node<>(q.hash, q.key, q.val);
            if (tl == null) hd = p;
            else tl.next = p;
            tl = p;
        }
        return hd;
    }

    // ---- Map operations ----

    public int size() {
        long n = sumCount();
        return (n < 0L) ? 0 : (n > (long) Integer.MAX_VALUE) ? Integer.MAX_VALUE : (int) n;
    }

    public boolean isEmpty() {
        return sumCount() <= 0L;
    }

    public long mappingCount() {
        long n = sumCount();
        return (n < 0L) ? 0L : n;
    }

    final long sumCount() {
        synchronized (ctl) {
            return baseCount;
        }
    }

    public V get(Object key) {
        int h = spread(key.hashCode());
        Node<K, V>[] tab;
        Node<K, V> e;
        int n;
        if ((tab = table) != null && (n = tab.length) > 0 && (e = tab[(n - 1) & h]) != null) {
            int eh = e.hash;
            K ek;
            if (eh == h) {
                if ((ek = e.key) == key || (ek != null && key.equals(ek))) return e.val;
            } else if (eh < 0) {
                Node<K, V> p = e.find(h, key);
                return (p != null) ? p.val : null;
            }
            while ((e = e.next) != null) {
                if (e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) return e.val;
            }
        }
        return null;
    }

    public boolean containsKey(Object key) {
        return get(key) != null;
    }

    public boolean containsValue(Object value) {
        if (value == null) throw new NullPointerException();
        Node<K, V>[] t = table;
        if (t != null) {
            Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
            for (Node<K, V> p; (p = it.advance()) != null; ) {
                V v;
                if ((v = p.val) == value || (v != null && value.equals(v))) return true;
            }
        }
        return false;
    }

    public V put(K key, V value) {
        return putVal(key, value, false);
    }

    final V putVal(K key, V value, boolean onlyIfAbsent) {
        if (key == null || value == null) throw new NullPointerException();
        int hash = spread(key.hashCode());
        int binCount = 0;
        for (Node<K, V>[] tab = table;;) {
            Node<K, V> f;
            int n, i, fh;
            K fk;
            V fv;
            if (tab == null || (n = tab.length) == 0) {
                tab = initTable();
            } else if ((f = tab[i = (n - 1) & hash]) == null) {
                if (casEmpty(tab, i, new Node<>(hash, key, value))) break;
            } else if ((fh = f.hash) == MOVED) {
                tab = awaitTransfer(tab);
            } else if (onlyIfAbsent && fh == hash && ((fk = f.key) == key || (fk != null && key.equals(fk)))
                       && (fv = f.val) != null) {
                return fv;
            } else {
                V oldVal = null;
                synchronized (f) {
                    if (tab[i] == f) {
                        if (fh >= 0) {
                            binCount = 1;
                            for (Node<K, V> e = f;; ++binCount) {
                                K ek;
                                if (e.hash == hash && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    oldVal = e.val;
                                    if (!onlyIfAbsent) e.val = value;
                                    break;
                                }
                                Node<K, V> pred = e;
                                if ((e = e.next) == null) {
                                    pred.next = new Node<>(hash, key, value);
                                    break;
                                }
                            }
                        } else if (f instanceof TreeBin) {
                            binCount = 2;
                            TreeNode<K, V> p = ((TreeBin<K, V>) f).putTreeVal(hash, key, value);
                            if (p != null) {
                                oldVal = p.val;
                                if (!onlyIfAbsent) p.val = value;
                            }
                        } else if (f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                if (binCount != 0) {
                    if (binCount >= TREEIFY_THRESHOLD) treeifyBin(tab, i);
                    if (oldVal != null) return oldVal;
                    break;
                }
            }
        }
        addCount(1L, binCount);
        return null;
    }

    public void putAll(Map<? extends K, ? extends V> m) {
        tryPresize(m.size());
        for (Map.Entry<? extends K, ? extends V> e : m.entrySet()) putVal(e.getKey(), e.getValue(), false);
    }

    public V remove(Object key) {
        return replaceNode(key, null, null);
    }

    /** Replace the value of key by value (remove if value is null), if cv is null or equals the
     *  current value; the old value, or null. */
    final V replaceNode(Object key, V value, Object cv) {
        int hash = spread(key.hashCode());
        for (Node<K, V>[] tab = table;;) {
            Node<K, V> f;
            int n, i, fh;
            if (tab == null || (n = tab.length) == 0 || (f = tab[i = (n - 1) & hash]) == null) break;
            if ((fh = f.hash) == MOVED) {
                tab = awaitTransfer(tab);
                continue;
            }
            V oldVal = null;
            boolean validated = false;
            synchronized (f) {
                if (tab[i] == f) {
                    if (fh >= 0) {
                        validated = true;
                        for (Node<K, V> e = f, pred = null;;) {
                            K ek;
                            if (e.hash == hash && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                V ev = e.val;
                                if (cv == null || cv == ev || (ev != null && cv.equals(ev))) {
                                    oldVal = ev;
                                    if (value != null) e.val = value;
                                    else if (pred != null) pred.next = e.next;
                                    else tab[i] = e.next;
                                }
                                break;
                            }
                            pred = e;
                            if ((e = e.next) == null) break;
                        }
                    } else if (f instanceof TreeBin) {
                        validated = true;
                        TreeBin<K, V> t = (TreeBin<K, V>) f;
                        TreeNode<K, V> r, p;
                        if ((r = t.root) != null && (p = r.findTreeNode(hash, key)) != null) {
                            V pv = p.val;
                            if (cv == null || cv == pv || (pv != null && cv.equals(pv))) {
                                oldVal = pv;
                                if (value != null) p.val = value;
                                else if (t.removeTreeNode(p)) tab[i] = untreeify(t.first);
                            }
                        }
                    } else if (f instanceof ReservationNode) {
                        throw new IllegalStateException("Recursive update");
                    }
                }
            }
            if (validated) {
                if (oldVal != null) {
                    if (value == null) addCount(-1L, -1);
                    return oldVal;
                }
                break;
            }
        }
        return null;
    }

    public void clear() {
        long delta = 0L;
        int i = 0;
        Node<K, V>[] tab = table;
        while (tab != null && i < tab.length) {
            Node<K, V> f = tab[i];
            if (f == null) {
                ++i;
            } else if (f.hash == MOVED) {
                tab = awaitTransfer(tab);
                i = 0;
            } else {
                synchronized (f) {
                    if (tab[i] == f) {
                        Node<K, V> p = (f.hash >= 0) ? f : (f instanceof TreeBin) ? ((TreeBin<K, V>) f).first : null;
                        while (p != null) {
                            --delta;
                            p = p.next;
                        }
                        tab[i++] = null;
                    }
                }
            }
        }
        if (delta != 0L) addCount(delta, -1);
    }

    public KeySetView<K, V> keySet() {
        KeySetView<K, V> ks = keySet;
        if (ks != null) return ks;
        return keySet = new KeySetView<K, V>(this, null);
    }

    public KeySetView<K, V> keySet(V mappedValue) {
        if (mappedValue == null) throw new NullPointerException();
        return new KeySetView<K, V>(this, mappedValue);
    }

    public Collection<V> values() {
        ValuesView<K, V> vs = values;
        if (vs != null) return vs;
        return values = new ValuesView<K, V>(this);
    }

    public Set<Map.Entry<K, V>> entrySet() {
        EntrySetView<K, V> es = entrySet;
        if (es != null) return es;
        return entrySet = new EntrySetView<K, V>(this);
    }

    public static <K> KeySetView<K, Boolean> newKeySet() {
        return new KeySetView<K, Boolean>(new ConcurrentHashMap<K, Boolean>(), Boolean.TRUE);
    }

    public static <K> KeySetView<K, Boolean> newKeySet(int initialCapacity) {
        return new KeySetView<K, Boolean>(new ConcurrentHashMap<K, Boolean>(initialCapacity), Boolean.TRUE);
    }

    public int hashCode() {
        int h = 0;
        Node<K, V>[] t = table;
        if (t != null) {
            Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
            for (Node<K, V> p; (p = it.advance()) != null; ) h += p.key.hashCode() ^ p.val.hashCode();
        }
        return h;
    }

    public String toString() {
        Node<K, V>[] t = table;
        int f = (t == null) ? 0 : t.length;
        Traverser<K, V> it = new Traverser<>(t, f, 0, f);
        StringBuilder sb = new StringBuilder();
        sb.append('{');
        Node<K, V> p;
        if ((p = it.advance()) != null) {
            for (;;) {
                K k = p.key;
                V v = p.val;
                sb.append(k == this ? "(this Map)" : k);
                sb.append('=');
                sb.append(v == this ? "(this Map)" : v);
                if ((p = it.advance()) == null) break;
                sb.append(',').append(' ');
            }
        }
        return sb.append('}').toString();
    }

    public boolean equals(Object o) {
        if (o != this) {
            if (!(o instanceof Map)) return false;
            Map<?, ?> m = (Map<?, ?>) o;
            Node<K, V>[] t = table;
            int f = (t == null) ? 0 : t.length;
            Traverser<K, V> it = new Traverser<>(t, f, 0, f);
            for (Node<K, V> p; (p = it.advance()) != null; ) {
                V val = p.val;
                Object v = m.get(p.key);
                if (v == null || (v != val && !v.equals(val))) return false;
            }
            for (Map.Entry<?, ?> e : m.entrySet()) {
                Object mk, mv, v;
                if ((mk = e.getKey()) == null || (mv = e.getValue()) == null || (v = get(mk)) == null
                    || (mv != v && !mv.equals(v))) return false;
            }
        }
        return true;
    }

    // ---- ConcurrentMap / Map default-method overrides ----

    public V putIfAbsent(K key, V value) {
        return putVal(key, value, true);
    }

    public boolean remove(Object key, Object value) {
        if (key == null) throw new NullPointerException();
        return value != null && replaceNode(key, null, value) != null;
    }

    public boolean replace(K key, V oldValue, V newValue) {
        if (key == null || oldValue == null || newValue == null) throw new NullPointerException();
        return replaceNode(key, newValue, oldValue) != null;
    }

    public V replace(K key, V value) {
        if (key == null || value == null) throw new NullPointerException();
        return replaceNode(key, value, null);
    }

    public V getOrDefault(Object key, V defaultValue) {
        V v;
        return (v = get(key)) == null ? defaultValue : v;
    }

    public void forEach(BiConsumer<? super K, ? super V> action) {
        if (action == null) throw new NullPointerException();
        Node<K, V>[] t = table;
        if (t != null) {
            Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
            for (Node<K, V> p; (p = it.advance()) != null; ) action.accept(p.key, p.val);
        }
    }

    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        if (function == null) throw new NullPointerException();
        Node<K, V>[] t = table;
        if (t != null) {
            Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
            for (Node<K, V> p; (p = it.advance()) != null; ) {
                V oldValue = p.val;
                for (K key = p.key;;) {
                    V newValue = function.apply(key, oldValue);
                    if (newValue == null) throw new NullPointerException();
                    if (replaceNode(key, newValue, oldValue) != null || (oldValue = get(key)) == null) break;
                }
            }
        }
    }

    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        if (key == null || mappingFunction == null) throw new NullPointerException();
        int h = spread(key.hashCode());
        V val = null;
        int binCount = 0;
        for (Node<K, V>[] tab = table;;) {
            Node<K, V> f;
            int n, i, fh;
            K fk;
            V fv;
            if (tab == null || (n = tab.length) == 0) {
                tab = initTable();
            } else if ((f = tab[i = (n - 1) & h]) == null) {
                ReservationNode<K, V> r = new ReservationNode<>();
                synchronized (r) {
                    if (casEmpty(tab, i, r)) {
                        binCount = 1;
                        Node<K, V> node = null;
                        try {
                            if ((val = fn1(mappingFunction, key)) != null) node = new Node<>(h, key, val);
                        } finally {
                            tab[i] = node;
                        }
                    }
                }
                if (binCount != 0) break;
            } else if ((fh = f.hash) == MOVED) {
                tab = awaitTransfer(tab);
            } else if (fh == h && ((fk = f.key) == key || (fk != null && key.equals(fk))) && (fv = f.val) != null) {
                return fv;
            } else {
                boolean added = false;
                synchronized (f) {
                    if (tab[i] == f) {
                        if (fh >= 0) {
                            binCount = 1;
                            for (Node<K, V> e = f;; ++binCount) {
                                K ek;
                                if (e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    val = e.val;
                                    break;
                                }
                                Node<K, V> pred = e;
                                if ((e = e.next) == null) {
                                    if ((val = fn1(mappingFunction, key)) != null) {
                                        if (pred.next != null) throw new IllegalStateException("Recursive update");
                                        added = true;
                                        pred.next = new Node<>(h, key, val);
                                    }
                                    break;
                                }
                            }
                        } else if (f instanceof TreeBin) {
                            binCount = 2;
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> r, p;
                            if ((r = t.root) != null && (p = r.findTreeNode(h, key)) != null) {
                                val = p.val;
                            } else if ((val = fn1(mappingFunction, key)) != null) {
                                added = true;
                                t.putTreeVal(h, key, val);
                            }
                        } else if (f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                if (binCount != 0) {
                    if (binCount >= TREEIFY_THRESHOLD) treeifyBin(tab, i);
                    if (!added) return val;
                    break;
                }
            }
        }
        if (val != null) addCount(1L, binCount);
        return val;
    }

    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (key == null || remappingFunction == null) throw new NullPointerException();
        int h = spread(key.hashCode());
        V val = null;
        int delta = 0;
        int binCount = 0;
        for (Node<K, V>[] tab = table;;) {
            Node<K, V> f;
            int n, i, fh;
            if (tab == null || (n = tab.length) == 0) {
                tab = initTable();
            } else if ((f = tab[i = (n - 1) & h]) == null) {
                break;
            } else if ((fh = f.hash) == MOVED) {
                tab = awaitTransfer(tab);
            } else {
                synchronized (f) {
                    if (tab[i] == f) {
                        if (fh >= 0) {
                            binCount = 1;
                            for (Node<K, V> e = f, pred = null;; ++binCount) {
                                K ek;
                                if (e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    val = fn2(remappingFunction, key, e.val);
                                    if (val != null) {
                                        e.val = val;
                                    } else {
                                        delta = -1;
                                        Node<K, V> en = e.next;
                                        if (pred != null) pred.next = en;
                                        else tab[i] = en;
                                    }
                                    break;
                                }
                                pred = e;
                                if ((e = e.next) == null) break;
                            }
                        } else if (f instanceof TreeBin) {
                            binCount = 2;
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> r, p;
                            if ((r = t.root) != null && (p = r.findTreeNode(h, key)) != null) {
                                val = fn2(remappingFunction, key, p.val);
                                if (val != null) {
                                    p.val = val;
                                } else {
                                    delta = -1;
                                    if (t.removeTreeNode(p)) tab[i] = untreeify(t.first);
                                }
                            }
                        } else if (f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                if (binCount != 0) break;
            }
        }
        if (delta != 0) addCount((long) delta, binCount);
        return val;
    }

    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        if (key == null || remappingFunction == null) throw new NullPointerException();
        int h = spread(key.hashCode());
        V val = null;
        int delta = 0;
        int binCount = 0;
        for (Node<K, V>[] tab = table;;) {
            Node<K, V> f;
            int n, i, fh;
            if (tab == null || (n = tab.length) == 0) {
                tab = initTable();
            } else if ((f = tab[i = (n - 1) & h]) == null) {
                ReservationNode<K, V> r = new ReservationNode<>();
                synchronized (r) {
                    if (casEmpty(tab, i, r)) {
                        binCount = 1;
                        Node<K, V> node = null;
                        try {
                            if ((val = fn2(remappingFunction, key, null)) != null) {
                                delta = 1;
                                node = new Node<>(h, key, val);
                            }
                        } finally {
                            tab[i] = node;
                        }
                    }
                }
                if (binCount != 0) break;
            } else if ((fh = f.hash) == MOVED) {
                tab = awaitTransfer(tab);
            } else {
                synchronized (f) {
                    if (tab[i] == f) {
                        if (fh >= 0) {
                            binCount = 1;
                            for (Node<K, V> e = f, pred = null;; ++binCount) {
                                K ek;
                                if (e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    val = fn2(remappingFunction, key, e.val);
                                    if (val != null) {
                                        e.val = val;
                                    } else {
                                        delta = -1;
                                        Node<K, V> en = e.next;
                                        if (pred != null) pred.next = en;
                                        else tab[i] = en;
                                    }
                                    break;
                                }
                                pred = e;
                                if ((e = e.next) == null) {
                                    val = fn2(remappingFunction, key, null);
                                    if (val != null) {
                                        if (pred.next != null) throw new IllegalStateException("Recursive update");
                                        delta = 1;
                                        pred.next = new Node<>(h, key, val);
                                    }
                                    break;
                                }
                            }
                        } else if (f instanceof TreeBin) {
                            binCount = 1;
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> r, p;
                            if ((r = t.root) != null) p = r.findTreeNode(h, key);
                            else p = null;
                            V pv = (p == null) ? null : p.val;
                            val = fn2(remappingFunction, key, pv);
                            if (val != null) {
                                if (p != null) {
                                    p.val = val;
                                } else {
                                    delta = 1;
                                    t.putTreeVal(h, key, val);
                                }
                            } else if (p != null) {
                                delta = -1;
                                if (t.removeTreeNode(p)) tab[i] = untreeify(t.first);
                            }
                        } else if (f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                if (binCount != 0) {
                    if (binCount >= TREEIFY_THRESHOLD) treeifyBin(tab, i);
                    break;
                }
            }
        }
        if (delta != 0) addCount((long) delta, binCount);
        return val;
    }

    public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        if (key == null || value == null || remappingFunction == null) throw new NullPointerException();
        int h = spread(key.hashCode());
        V val = null;
        int delta = 0;
        int binCount = 0;
        for (Node<K, V>[] tab = table;;) {
            Node<K, V> f;
            int n, i, fh;
            if (tab == null || (n = tab.length) == 0) {
                tab = initTable();
            } else if ((f = tab[i = (n - 1) & h]) == null) {
                if (casEmpty(tab, i, new Node<>(h, key, value))) {
                    delta = 1;
                    val = value;
                    break;
                }
            } else if ((fh = f.hash) == MOVED) {
                tab = awaitTransfer(tab);
            } else {
                synchronized (f) {
                    if (tab[i] == f) {
                        if (fh >= 0) {
                            binCount = 1;
                            for (Node<K, V> e = f, pred = null;; ++binCount) {
                                K ek;
                                if (e.hash == h && ((ek = e.key) == key || (ek != null && key.equals(ek)))) {
                                    val = fn2(remappingFunction, e.val, value);
                                    if (val != null) {
                                        e.val = val;
                                    } else {
                                        delta = -1;
                                        Node<K, V> en = e.next;
                                        if (pred != null) pred.next = en;
                                        else tab[i] = en;
                                    }
                                    break;
                                }
                                pred = e;
                                if ((e = e.next) == null) {
                                    delta = 1;
                                    val = value;
                                    pred.next = new Node<>(h, key, val);
                                    break;
                                }
                            }
                        } else if (f instanceof TreeBin) {
                            binCount = 2;
                            TreeBin<K, V> t = (TreeBin<K, V>) f;
                            TreeNode<K, V> r = t.root;
                            TreeNode<K, V> p = (r == null) ? null : r.findTreeNode(h, key);
                            val = (p == null) ? value : fn2(remappingFunction, p.val, value);
                            if (val != null) {
                                if (p != null) {
                                    p.val = val;
                                } else {
                                    delta = 1;
                                    t.putTreeVal(h, key, val);
                                }
                            } else if (p != null) {
                                delta = -1;
                                if (t.removeTreeNode(p)) tab[i] = untreeify(t.first);
                            }
                        } else if (f instanceof ReservationNode) {
                            throw new IllegalStateException("Recursive update");
                        }
                    }
                }
                if (binCount != 0) {
                    if (binCount >= TREEIFY_THRESHOLD) treeifyBin(tab, i);
                    break;
                }
            }
        }
        if (delta != 0) addCount((long) delta, binCount);
        return val;
    }

    // ---- Hashtable-style legacy methods ----

    public boolean contains(Object value) {
        return containsValue(value);
    }

    public Enumeration<K> keys() {
        Node<K, V>[] t = table;
        int f = (t == null) ? 0 : t.length;
        return new KeyIterator<K, V>(t, f, 0, f, this);
    }

    public Enumeration<V> elements() {
        Node<K, V>[] t = table;
        int f = (t == null) ? 0 : t.length;
        return new ValueIterator<K, V>(t, f, 0, f, this);
    }

    // ---- bulk parallel operations: not modelled ----

    public void forEach(long parallelismThreshold, BiConsumer<? super K, ? super V> action) {
        throw ModelStuck.unsupported("ConcurrentHashMap.forEach(long, ...)");
    }

    public <U> U search(long parallelismThreshold, BiFunction<? super K, ? super V, ? extends U> searchFunction) {
        throw ModelStuck.unsupported("ConcurrentHashMap.search");
    }

    public <U> U reduce(long parallelismThreshold, BiFunction<? super K, ? super V, ? extends U> transformer,
                        BiFunction<? super U, ? super U, ? extends U> reducer) {
        throw ModelStuck.unsupported("ConcurrentHashMap.reduce");
    }

    public void forEachKey(long parallelismThreshold, Consumer<? super K> action) {
        throw ModelStuck.unsupported("ConcurrentHashMap.forEachKey");
    }

    public void forEachValue(long parallelismThreshold, Consumer<? super V> action) {
        throw ModelStuck.unsupported("ConcurrentHashMap.forEachValue");
    }

    public void forEachEntry(long parallelismThreshold, Consumer<? super Map.Entry<K, V>> action) {
        throw ModelStuck.unsupported("ConcurrentHashMap.forEachEntry");
    }

    // ---- traversal ----

    /** Visits every node of the table in slot order (a tree bin along its list); a forwarding
     *  marker at slot i of a table of length n stands for slots i and i + n of the next table,
     *  which are visited before slot i + 1. */
    static class Traverser<K, V> {
        Node<K, V>[] tab;
        Node<K, V> next;
        // saved positions in the tables the traversal came from
        Node<K, V>[][] stackTab = null;
        int[] stackLen = null, stackIdx = null;
        int depth = 0;
        int index;
        int baseIndex;
        int baseLimit;
        final int baseSize;

        Traverser(Node<K, V>[] tab, int size, int index, int limit) {
            this.tab = tab;
            this.baseSize = size;
            this.baseIndex = this.index = index;
            this.baseLimit = limit;
            this.next = null;
        }

        final Node<K, V> advance() {
            Node<K, V> e;
            if ((e = next) != null) e = e.next;
            for (;;) {
                Node<K, V>[] t;
                int i, n;
                if (e != null) return next = e;
                if (baseIndex >= baseLimit || (t = tab) == null || (n = t.length) <= (i = index) || i < 0) return next = null;
                if ((e = t[i]) != null && e.hash < 0) {
                    if (e instanceof ForwardingNode) {
                        tab = ((ForwardingNode<K, V>) e).nextTable;
                        e = null;
                        push(t, i, n);
                        continue;
                    } else if (e instanceof TreeBin) {
                        e = ((TreeBin<K, V>) e).first;
                    } else {
                        e = null;
                    }
                }
                if (depth > 0) recover(n);
                else if ((index = i + baseSize) >= n) index = ++baseIndex;
            }
        }

        private void push(Node<K, V>[] t, int i, int n) {
            if (stackTab == null) {
                stackTab = newTabs(4);
                stackLen = new int[4];
                stackIdx = new int[4];
            } else if (depth == stackLen.length) {
                Node<K, V>[][] nt = newTabs(depth * 2);
                int[] nl = new int[depth * 2], ni = new int[depth * 2];
                for (int k = 0; k < depth; k++) {
                    nt[k] = stackTab[k];
                    nl[k] = stackLen[k];
                    ni[k] = stackIdx[k];
                }
                stackTab = nt;
                stackLen = nl;
                stackIdx = ni;
            }
            stackTab[depth] = t;
            stackLen[depth] = n;
            stackIdx[depth] = i;
            depth++;
        }

        @SuppressWarnings("unchecked")
        private static <K, V> Node<K, V>[][] newTabs(int n) {
            return (Node<K, V>[][]) new Node<?, ?>[n][];
        }

        /** After slot index of the current table (length n): the next slot to visit. */
        private void recover(int n) {
            int len;
            while (depth > 0 && (index += (len = stackLen[depth - 1])) >= n) {
                n = len;
                index = stackIdx[depth - 1];
                tab = stackTab[depth - 1];
                stackTab[depth - 1] = null;
                depth--;
            }
            if (depth == 0 && (index += baseSize) >= n) index = ++baseIndex;
        }
    }

    static class BaseIterator<K, V> extends Traverser<K, V> {
        final ConcurrentHashMap<K, V> map;
        Node<K, V> lastReturned;

        BaseIterator(Node<K, V>[] tab, int size, int index, int limit, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit);
            this.map = map;
            advance();
        }

        public final boolean hasNext() {
            return next != null;
        }

        public final boolean hasMoreElements() {
            return next != null;
        }

        public final void remove() {
            Node<K, V> p;
            if ((p = lastReturned) == null) throw new IllegalStateException();
            lastReturned = null;
            map.replaceNode(p.key, null, null);
        }
    }

    static final class KeyIterator<K, V> extends BaseIterator<K, V> implements Iterator<K>, Enumeration<K> {
        KeyIterator(Node<K, V>[] tab, int size, int index, int limit, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit, map);
        }

        public final K next() {
            Node<K, V> p;
            if ((p = next) == null) throw new NoSuchElementException();
            K k = p.key;
            lastReturned = p;
            advance();
            return k;
        }

        public final K nextElement() {
            return next();
        }
    }

    static final class ValueIterator<K, V> extends BaseIterator<K, V> implements Iterator<V>, Enumeration<V> {
        ValueIterator(Node<K, V>[] tab, int size, int index, int limit, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit, map);
        }

        public final V next() {
            Node<K, V> e;
            if ((e = next) == null) throw new NoSuchElementException();
            V v = e.val;
            lastReturned = e;
            advance();
            return v;
        }

        public final V nextElement() {
            return next();
        }
    }

    static final class EntryIterator<K, V> extends BaseIterator<K, V> implements Iterator<Map.Entry<K, V>> {
        EntryIterator(Node<K, V>[] tab, int size, int index, int limit, ConcurrentHashMap<K, V> map) {
            super(tab, size, index, limit, map);
        }

        public final Map.Entry<K, V> next() {
            Node<K, V> e;
            if ((e = next) == null) throw new NoSuchElementException();
            K k = e.key;
            V v = e.val;
            lastReturned = e;
            advance();
            return new MapEntry<K, V>(k, v, map);
        }
    }

    /** An entry returned by the entry-set iterator: setValue writes through to the map. */
    static final class MapEntry<K, V> implements Map.Entry<K, V> {
        final K key;
        V val;
        final ConcurrentHashMap<K, V> map;

        MapEntry(K key, V val, ConcurrentHashMap<K, V> map) {
            this.key = key;
            this.val = val;
            this.map = map;
        }

        public K getKey() {
            return key;
        }

        public V getValue() {
            return val;
        }

        public int hashCode() {
            return key.hashCode() ^ val.hashCode();
        }

        public String toString() {
            return key + "=" + val;
        }

        public boolean equals(Object o) {
            Object k, v;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry) && (k = (e = (Map.Entry<?, ?>) o).getKey()) != null
                    && (v = e.getValue()) != null && (k == key || k.equals(key)) && (v == val || v.equals(val)));
        }

        public V setValue(V value) {
            if (value == null) throw new NullPointerException();
            V v = val;
            val = value;
            map.put(key, value);
            return v;
        }
    }

    // ---- views ----

    abstract static class CollectionView<K, V, E> extends AbstractCollection<E> implements Collection<E>, java.io.Serializable {
        final ConcurrentHashMap<K, V> map;

        CollectionView(ConcurrentHashMap<K, V> map) {
            this.map = map;
        }

        public ConcurrentHashMap<K, V> getMap() {
            return map;
        }

        public final void clear() {
            map.clear();
        }

        public final int size() {
            return map.size();
        }

        public final boolean isEmpty() {
            return map.isEmpty();
        }

        public abstract Iterator<E> iterator();

        public abstract boolean contains(Object o);

        public abstract boolean remove(Object o);

        public final String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append('[');
            Iterator<E> it = iterator();
            if (it.hasNext()) {
                for (;;) {
                    Object e = it.next();
                    sb.append(e == this ? "(this Collection)" : e);
                    if (!it.hasNext()) break;
                    sb.append(',').append(' ');
                }
            }
            return sb.append(']').toString();
        }

        public final boolean containsAll(Collection<?> c) {
            if (c != this) {
                for (Object e : c) {
                    if (e == null || !contains(e)) return false;
                }
            }
            return true;
        }

        public boolean removeAll(Collection<?> c) {
            if (c == null) throw new NullPointerException();
            boolean modified = false;
            Node<K, V>[] t;
            if ((t = map.table) == null) {
                return false;
            } else if (c instanceof Set<?> && c.size() > t.length) {
                for (Iterator<?> it = iterator(); it.hasNext(); ) {
                    if (c.contains(it.next())) {
                        it.remove();
                        modified = true;
                    }
                }
            } else {
                for (Object e : c) modified |= remove(e);
            }
            return modified;
        }

        public final boolean retainAll(Collection<?> c) {
            if (c == null) throw new NullPointerException();
            boolean modified = false;
            for (Iterator<E> it = iterator(); it.hasNext(); ) {
                if (!c.contains(it.next())) {
                    it.remove();
                    modified = true;
                }
            }
            return modified;
        }
    }

    public static final class KeySetView<K, V> extends CollectionView<K, V, K> implements Set<K>, java.io.Serializable {
        private final V value;

        KeySetView(ConcurrentHashMap<K, V> map, V value) {
            super(map);
            this.value = value;
        }

        public V getMappedValue() {
            return value;
        }

        public boolean contains(Object o) {
            return map.containsKey(o);
        }

        public boolean remove(Object o) {
            return map.remove(o) != null;
        }

        public Iterator<K> iterator() {
            Node<K, V>[] t;
            ConcurrentHashMap<K, V> m = map;
            int f = (t = m.table) == null ? 0 : t.length;
            return new KeyIterator<K, V>(t, f, 0, f, m);
        }

        public boolean add(K e) {
            V v;
            if ((v = value) == null) throw new UnsupportedOperationException();
            return map.putVal(e, v, true) == null;
        }

        public boolean addAll(Collection<? extends K> c) {
            boolean added = false;
            V v;
            if ((v = value) == null) throw new UnsupportedOperationException();
            for (K e : c) {
                if (map.putVal(e, v, true) == null) added = true;
            }
            return added;
        }

        public int hashCode() {
            int h = 0;
            for (K e : this) h += e.hashCode();
            return h;
        }

        public boolean equals(Object o) {
            Set<?> c;
            return ((o instanceof Set) && ((c = (Set<?>) o) == this || (containsAll(c) && c.containsAll(this))));
        }

        public void forEach(Consumer<? super K> action) {
            if (action == null) throw new NullPointerException();
            Node<K, V>[] t;
            if ((t = map.table) != null) {
                Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
                for (Node<K, V> p; (p = it.advance()) != null; ) action.accept(p.key);
            }
        }
    }

    static final class ValuesView<K, V> extends CollectionView<K, V, V> implements Collection<V>, java.io.Serializable {
        ValuesView(ConcurrentHashMap<K, V> map) {
            super(map);
        }

        public final boolean contains(Object o) {
            return map.containsValue(o);
        }

        public final boolean remove(Object o) {
            if (o != null) {
                for (Iterator<V> it = iterator(); it.hasNext(); ) {
                    if (o.equals(it.next())) {
                        it.remove();
                        return true;
                    }
                }
            }
            return false;
        }

        public final Iterator<V> iterator() {
            ConcurrentHashMap<K, V> m = map;
            Node<K, V>[] t;
            int f = (t = m.table) == null ? 0 : t.length;
            return new ValueIterator<K, V>(t, f, 0, f, m);
        }

        public final boolean add(V e) {
            throw new UnsupportedOperationException();
        }

        public final boolean addAll(Collection<? extends V> c) {
            throw new UnsupportedOperationException();
        }

        public boolean removeAll(Collection<?> c) {
            if (c == null) throw new NullPointerException();
            boolean modified = false;
            for (Iterator<V> it = iterator(); it.hasNext(); ) {
                if (c.contains(it.next())) {
                    it.remove();
                    modified = true;
                }
            }
            return modified;
        }

        public void forEach(Consumer<? super V> action) {
            if (action == null) throw new NullPointerException();
            Node<K, V>[] t;
            if ((t = map.table) != null) {
                Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
                for (Node<K, V> p; (p = it.advance()) != null; ) action.accept(p.val);
            }
        }
    }

    static final class EntrySetView<K, V> extends CollectionView<K, V, Map.Entry<K, V>>
            implements Set<Map.Entry<K, V>>, java.io.Serializable {
        EntrySetView(ConcurrentHashMap<K, V> map) {
            super(map);
        }

        public boolean contains(Object o) {
            Object k, v, r;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry) && (k = (e = (Map.Entry<?, ?>) o).getKey()) != null
                    && (r = map.get(k)) != null && (v = e.getValue()) != null && (v == r || v.equals(r)));
        }

        public boolean remove(Object o) {
            Object k, v;
            Map.Entry<?, ?> e;
            return ((o instanceof Map.Entry) && (k = (e = (Map.Entry<?, ?>) o).getKey()) != null
                    && (v = e.getValue()) != null && map.remove(k, v));
        }

        public Iterator<Map.Entry<K, V>> iterator() {
            ConcurrentHashMap<K, V> m = map;
            Node<K, V>[] t;
            int f = (t = m.table) == null ? 0 : t.length;
            return new EntryIterator<K, V>(t, f, 0, f, m);
        }

        public boolean add(Map.Entry<K, V> e) {
            return map.putVal(e.getKey(), e.getValue(), false) == null;
        }

        public boolean addAll(Collection<? extends Map.Entry<K, V>> c) {
            boolean added = false;
            for (Map.Entry<K, V> e : c) {
                if (add(e)) added = true;
            }
            return added;
        }

        public final int hashCode() {
            int h = 0;
            Node<K, V>[] t;
            if ((t = map.table) != null) {
                Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
                for (Node<K, V> p; (p = it.advance()) != null; ) h += p.hashCode();
            }
            return h;
        }

        public final boolean equals(Object o) {
            Set<?> c;
            return ((o instanceof Set) && ((c = (Set<?>) o) == this || (containsAll(c) && c.containsAll(this))));
        }

        public void forEach(Consumer<? super Map.Entry<K, V>> action) {
            if (action == null) throw new NullPointerException();
            Node<K, V>[] t;
            if ((t = map.table) != null) {
                Traverser<K, V> it = new Traverser<>(t, t.length, 0, t.length);
                for (Node<K, V> p; (p = it.advance()) != null; ) action.accept(new MapEntry<K, V>(p.key, p.val, map));
            }
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
            throw ModelStuck.unsupported("ConcurrentHashMap tree bin: is the key class C implements Comparable<C>?");
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
        throw ModelStuck.unsupported("ConcurrentHashMap tree bin: compareTo");
    }

    /** Keys with equal hashes that do not compare: by class name, then identity hash code. */
    static int tieBreakOrder(Object a, Object b) {
        int d;
        if (a == null || b == null || (d = a.getClass().getName().compareTo(b.getClass().getName())) == 0) {
            throw ModelStuck.unsupported("ConcurrentHashMap tree bin: order by identity hash code");
        }
        return d;
    }

    static final class TreeNode<K, V> extends Node<K, V> {
        TreeNode<K, V> parent;
        TreeNode<K, V> left;
        TreeNode<K, V> right;
        TreeNode<K, V> prev;
        boolean red;

        TreeNode(int hash, K key, V val, Node<K, V> next, TreeNode<K, V> parent) {
            super(hash, key, val, next);
            this.parent = parent;
        }

        Node<K, V> find(int h, Object k) {
            return findTreeNode(h, k);
        }

        /** The node of key k (hash h) in the subtree of this node, or null. */
        final TreeNode<K, V> findTreeNode(int h, Object k) {
            if (k != null) {
                TreeNode<K, V> p = this;
                Class<?> kc = null;
                do {
                    int ph, dir;
                    K pk;
                    TreeNode<K, V> q;
                    TreeNode<K, V> pl = p.left, pr = p.right;
                    if ((ph = p.hash) > h) {
                        p = pl;
                    } else if (ph < h) {
                        p = pr;
                    } else if ((pk = p.key) == k || (pk != null && k.equals(pk))) {
                        return p;
                    } else if (pl == null) {
                        p = pr;
                    } else if (pr == null) {
                        p = pl;
                    } else if ((kc != null || (kc = comparableClassFor(k)) != null)
                               && (dir = compareComparables(kc, k, pk)) != 0) {
                        p = (dir < 0) ? pl : pr;
                    } else if ((q = pr.findTreeNode(h, k)) != null) {
                        return q;
                    } else {
                        p = pl;
                    }
                } while (p != null);
            }
            return null;
        }
    }

    /** Head of a tree bin: the red-black tree and the bin's list ([first]). */
    static final class TreeBin<K, V> extends Node<K, V> {
        TreeNode<K, V> root;
        volatile TreeNode<K, V> first;

        /** The tree of the list starting at b (list order unchanged). */
        TreeBin(TreeNode<K, V> b) {
            super(TREEBIN, null, null);
            this.first = b;
            TreeNode<K, V> r = null;
            for (TreeNode<K, V> x = b, next; x != null; x = next) {
                next = (TreeNode<K, V>) x.next;
                x.left = x.right = null;
                if (r == null) {
                    x.parent = null;
                    x.red = false;
                    r = x;
                } else {
                    K k = x.key;
                    int h = x.hash;
                    Class<?> kc = null;
                    for (TreeNode<K, V> p = r;;) {
                        int dir, ph;
                        K pk = p.key;
                        if ((ph = p.hash) > h) dir = -1;
                        else if (ph < h) dir = 1;
                        else if ((kc == null && (kc = comparableClassFor(k)) == null)
                                 || (dir = compareComparables(kc, k, pk)) == 0) dir = tieBreakOrder(k, pk);
                        TreeNode<K, V> xp = p;
                        if ((p = (dir <= 0) ? p.left : p.right) == null) {
                            x.parent = xp;
                            if (dir <= 0) xp.left = x;
                            else xp.right = x;
                            r = balanceInsertion(r, x);
                            break;
                        }
                    }
                }
            }
            this.root = r;
        }

        /** Readers search along the list (results are the same as a tree search). */
        Node<K, V> find(int h, Object k) {
            if (k != null) {
                for (Node<K, V> e = first; e != null; e = e.next) {
                    K ek;
                    if (e.hash == h && ((ek = e.key) == k || (ek != null && k.equals(ek)))) return e;
                }
            }
            return null;
        }

        /** Insert (h, k, v); the existing node if the key is present, else null.  A new node is
         *  put at the front of the bin's list. */
        TreeNode<K, V> putTreeVal(int h, K k, V v) {
            Class<?> kc = null;
            boolean searched = false;
            for (TreeNode<K, V> p = root;;) {
                int dir, ph;
                K pk;
                if (p == null) {
                    first = root = new TreeNode<K, V>(h, k, v, null, null);
                    break;
                } else if ((ph = p.hash) > h) {
                    dir = -1;
                } else if (ph < h) {
                    dir = 1;
                } else if ((pk = p.key) == k || (pk != null && k.equals(pk))) {
                    return p;
                } else if ((kc == null && (kc = comparableClassFor(k)) == null)
                           || (dir = compareComparables(kc, k, pk)) == 0) {
                    if (!searched) {
                        TreeNode<K, V> q, ch;
                        searched = true;
                        if (((ch = p.left) != null && (q = ch.findTreeNode(h, k)) != null)
                            || ((ch = p.right) != null && (q = ch.findTreeNode(h, k)) != null)) return q;
                    }
                    dir = tieBreakOrder(k, pk);
                }
                TreeNode<K, V> xp = p;
                if ((p = (dir <= 0) ? p.left : p.right) == null) {
                    TreeNode<K, V> x, f = first;
                    first = x = new TreeNode<K, V>(h, k, v, f, xp);
                    if (f != null) f.prev = x;
                    if (dir <= 0) xp.left = x;
                    else xp.right = x;
                    if (!xp.red) x.red = true;
                    else root = balanceInsertion(root, x);
                    break;
                }
            }
            return null;
        }

        /** Remove p (a node of this bin); true if the bin is now too small for a tree (the
         *  caller replaces it by a list of [first]). */
        boolean removeTreeNode(TreeNode<K, V> p) {
            TreeNode<K, V> next = (TreeNode<K, V>) p.next;
            TreeNode<K, V> pred = p.prev;
            TreeNode<K, V> r, rl;
            if (pred == null) first = next;
            else pred.next = next;
            if (next != null) next.prev = pred;
            if (first == null) {
                root = null;
                return true;
            }
            if ((r = root) == null || r.right == null || (rl = r.left) == null || rl.left == null) return true;
            TreeNode<K, V> replacement;
            TreeNode<K, V> pl = p.left;
            TreeNode<K, V> pr = p.right;
            if (pl != null && pr != null) {
                // swap p with its successor s (positions and colours), then delete p there
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
                    if ((p.parent = sp) != null) {
                        if (s == sp.left) sp.left = p;
                        else sp.right = p;
                    }
                    if ((s.right = pr) != null) pr.parent = s;
                }
                p.left = null;
                if ((p.right = sr) != null) sr.parent = p;
                if ((s.left = pl) != null) pl.parent = s;
                if ((s.parent = pp) == null) r = s;
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
                if (pp == null) r = replacement;
                else if (p == pp.left) pp.left = replacement;
                else pp.right = replacement;
                p.left = p.right = p.parent = null;
            }
            root = (p.red) ? r : balanceDeletion(r, replacement);
            if (p == replacement) {   // p was a leaf: detach it
                TreeNode<K, V> pp;
                if ((pp = p.parent) != null) {
                    if (p == pp.left) pp.left = null;
                    else if (p == pp.right) pp.right = null;
                    p.parent = null;
                }
            }
            return false;
        }

        // red-black tree primitives (CLRS)

        static <K, V> TreeNode<K, V> rotateLeft(TreeNode<K, V> root, TreeNode<K, V> p) {
            TreeNode<K, V> r, pp, rl;
            if (p != null && (r = p.right) != null) {
                if ((rl = p.right = r.left) != null) rl.parent = p;
                if ((pp = r.parent = p.parent) == null) (root = r).red = false;
                else if (pp.left == p) pp.left = r;
                else pp.right = r;
                r.left = p;
                p.parent = r;
            }
            return root;
        }

        static <K, V> TreeNode<K, V> rotateRight(TreeNode<K, V> root, TreeNode<K, V> p) {
            TreeNode<K, V> l, pp, lr;
            if (p != null && (l = p.left) != null) {
                if ((lr = p.left = l.right) != null) lr.parent = p;
                if ((pp = l.parent = p.parent) == null) (root = l).red = false;
                else if (pp.right == p) pp.right = l;
                else pp.left = l;
                l.right = p;
                p.parent = l;
            }
            return root;
        }

        static <K, V> TreeNode<K, V> balanceInsertion(TreeNode<K, V> root, TreeNode<K, V> x) {
            x.red = true;
            for (TreeNode<K, V> xp, xpp, xppl, xppr;;) {
                if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                } else if (!xp.red || (xpp = xp.parent) == null) {
                    return root;
                }
                if (xp == (xppl = xpp.left)) {
                    if ((xppr = xpp.right) != null && xppr.red) {
                        xppr.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    } else {
                        if (x == xp.right) {
                            root = rotateLeft(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
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
                    if (xppl != null && xppl.red) {
                        xppl.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    } else {
                        if (x == xp.left) {
                            root = rotateRight(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
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

        static <K, V> TreeNode<K, V> balanceDeletion(TreeNode<K, V> root, TreeNode<K, V> x) {
            for (TreeNode<K, V> xp, xpl, xpr;;) {
                if (x == null || x == root) {
                    return root;
                } else if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                } else if (x.red) {
                    x.red = false;
                    return root;
                } else if ((xpl = xp.left) == x) {
                    if ((xpr = xp.right) != null && xpr.red) {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    if (xpr == null) {
                        x = xp;
                    } else {
                        TreeNode<K, V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) && (sl == null || !sl.red)) {
                            xpr.red = true;
                            x = xp;
                        } else {
                            if (sr == null || !sr.red) {
                                if (sl != null) sl.red = false;
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ? null : xp.right;
                            }
                            if (xpr != null) {
                                xpr.red = (xp == null) ? false : xp.red;
                                if ((sr = xpr.right) != null) sr.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                } else {
                    if (xpl != null && xpl.red) {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    if (xpl == null) {
                        x = xp;
                    } else {
                        TreeNode<K, V> sl = xpl.left, sr = xpl.right;
                        if ((sl == null || !sl.red) && (sr == null || !sr.red)) {
                            xpl.red = true;
                            x = xp;
                        } else {
                            if (sl == null || !sl.red) {
                                if (sr != null) sr.red = false;
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ? null : xp.left;
                            }
                            if (xpl != null) {
                                xpl.red = (xp == null) ? false : xp.red;
                                if ((sl = xpl.left) != null) sl.red = false;
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

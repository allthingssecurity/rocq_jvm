package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of the java.util.Collections model (all of its public static methods):
 *  the algorithms on RandomAccess and sequential lists around the JDK's thresholds, with lists
 *  and keys that log every call (get/set/size/listIterator, compareTo, comparators, equals),
 *  min/max, the unmodifiable/synchronized/checked views of lists, sets, sorted and navigable
 *  sets and maps, queues (class names, delegation, exceptions and messages), nCopies, the
 *  singletons and empty collections, enumeration/list, frequency/disjoint/addAll,
 *  newSetFromMap, asLifoQueue, reverseOrder, and the null checks of every static method. */
public final class CollOps2 {
    private CollOps2() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static StringBuilder log = new StringBuilder();
    static int calls;
    static int hash;

    static void log(String op, int a) {
        calls++;
        hash = hash * 31 + op.hashCode() * 7 + a;
    }

    static void reset() {
        calls = 0;
        hash = 17;
    }

    static String logged() {
        return "{" + calls + "/" + hash + "}";
    }

    /** The class name of a Collections wrapper (the entry classes of the maps themselves are not compared). */
    static String cn(Object o) {
        String n = o.getClass().getName();
        return n.startsWith("java.util.Collections") ? n : "-";
    }

    static String ex(Throwable e) {
        return "!" + e.getClass().getSimpleName() + ":" + e.getMessage();
    }

    static final class Key implements Comparable<Key> {
        final int k;
        final int id;
        Key(int k, int id) { this.k = k; this.id = id; }
        public int compareTo(Key o) {
            log("c", id * 1000 + o.id);
            return Integer.compare(k, o.k);
        }
        public boolean equals(Object o) {
            log("e", id * 1000 + (o instanceof Key ? ((Key) o).id : 999));
            return o instanceof Key && ((Key) o).k == k;
        }
        public int hashCode() { return k; }
        public String toString() { return k + "#" + id; }
    }

    /** A sequential list that logs its primitive operations (AbstractList's iterators). */
    static class LogList<E> extends AbstractList<E> {
        final ArrayList<E> a = new ArrayList<>();
        public E get(int i) { log("g", i); return a.get(i); }
        public E set(int i, E e) { log("s", i); return a.set(i, e); }
        public int size() { log("z", 0); return a.size(); }
        public void add(int i, E e) { log("a", i); a.add(i, e); }
        public E remove(int i) { log("r", i); return a.remove(i); }
    }

    static final class LogRAList<E> extends LogList<E> implements RandomAccess {
    }

    static Comparator<Key> comparator() {
        switch (r(4)) {
            case 0: return (x, y) -> { log("C", x.id * 1000 + y.id); return Integer.compare(x.k, y.k); };
            case 1: return (x, y) -> { log("C", x.id * 1000 + y.id); return Integer.compare(y.k, x.k); };
            case 2: return Comparator.nullsFirst((x, y) -> { log("C", x.id * 1000 + y.id); return x.k - y.k; });
            default: return null;
        }
    }

    /** A list of n Keys (sorted or not) of one of four kinds. */
    static List<Key> keyList(int n, boolean sorted, int kind) {
        List<Key> l = kind == 0 ? new ArrayList<>() : kind == 1 ? new LinkedList<>() : kind == 2 ? new LogList<>() : new LogRAList<>();
        int v = r(5);
        for (int i = 0; i < n; i++) {
            v = sorted ? v + r(3) : r(30);
            l.add(new Key(v, i));
        }
        return l;
    }

    static int size() {
        int k = r(10);
        return k < 3 ? r(6) : k < 7 ? 8 + r(30) : k < 9 ? 90 + r(30) : r(150);
    }

    public static String algos(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 5; round++) {
            reset();
            int n = size();
            int kind = r(4);
            try {
                switch (r(12)) {
                    case 0: {
                        List<Key> l = keyList(n, true, kind);
                        reset();
                        Key key = new Key(r(40), 999);
                        Comparator<Key> c = comparator();
                        int i = r(2) == 0 ? Collections.binarySearch(l, key) : Collections.binarySearch(l, key, c);
                        out.append(i);
                        break;
                    }
                    case 1: {
                        List<Key> l = keyList(n, false, kind);
                        reset();
                        Collections.reverse(l);
                        out.append(l);
                        break;
                    }
                    case 2: {
                        List<Key> l = keyList(n, false, kind);
                        reset();
                        Collections.fill(l, r(4) == 0 ? null : new Key(-1, 500));
                        out.append(l);
                        break;
                    }
                    case 3: {
                        List<Key> src = keyList(n, false, kind);
                        List<Key> dst = keyList(n + r(5) - 1, false, r(4));
                        reset();
                        Collections.copy(dst, src);
                        out.append(dst);
                        break;
                    }
                    case 4: {
                        List<Key> l = keyList(n, false, kind);
                        reset();
                        int d = r(5) == 0 ? (r(2) == 0 ? Integer.MIN_VALUE : Integer.MAX_VALUE) : r(2 * n + 3) - n - 1;
                        Collections.rotate(l, d);
                        out.append(d).append(l);
                        break;
                    }
                    case 5: {
                        List<Key> l = keyList(n, false, kind);
                        if (n > 0 && r(3) == 0) l.set(r(n), null);
                        reset();
                        Key old = r(4) == 0 ? null : new Key(r(30), 600);
                        boolean b = Collections.replaceAll(l, old, new Key(-2, 700));
                        out.append(b).append(l);
                        break;
                    }
                    case 6: case 7: {
                        List<Key> src = new ArrayList<>();
                        for (int i = 0; i < n; i++) src.add(new Key(r(3), i));
                        List<Key> tgt = new ArrayList<>();
                        int m = r(4);
                        for (int i = 0; i < m; i++) tgt.add(new Key(r(3), 100 + i));
                        List<Key> s2 = kind == 0 ? src : kind == 1 ? new LinkedList<>(src) : copyInto(new LogList<>(), src);
                        List<Key> t2 = r(2) == 0 ? tgt : new LinkedList<>(tgt);
                        reset();
                        out.append(Collections.indexOfSubList(s2, t2)).append(',').append(Collections.lastIndexOfSubList(s2, t2));
                        break;
                    }
                    case 8: {
                        List<Key> l = keyList(n, false, kind);
                        reset();
                        Collections.swap(l, r(n + 1), r(n + 1));
                        out.append(l);
                        break;
                    }
                    case 9: {
                        List<Key> l = keyList(n, false, kind);
                        reset();
                        Collections.shuffle(l, new Random(r(1000)));
                        out.append(l);
                        break;
                    }
                    case 10: {
                        List<Key> l = keyList(Math.min(n, 40), false, kind);
                        reset();
                        Comparator<Key> c = comparator();
                        if (r(2) == 0) Collections.sort(l); else Collections.sort(l, c);
                        out.append(l);
                        break;
                    }
                    default: {
                        // the iterator binarySearch above the 5000 threshold (sequential lists only)
                        if (r(10) != 0) { out.append('-'); break; }
                        List<Integer> l = r(2) == 0 ? new LinkedList<>() : new LogList<>();
                        int m = 5000 + r(3);
                        for (int i = 0; i < m; i++) l.add(i * 2);
                        reset();
                        out.append(Collections.binarySearch(l, r(10100) - 50)).append(Collections.binarySearch(l, r(10100), Comparator.reverseOrder()));
                        break;
                    }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(logged()).append(';');
        }
        return out.toString();
    }

    static <E> List<E> copyInto(List<E> d, List<E> src) {
        d.addAll(src);
        return d;
    }

    public static String minmax(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 6; round++) {
            reset();
            int n = r(12);
            try {
                Collection<Key> c;
                switch (r(4)) {
                    case 0: c = new ArrayList<>(); break;
                    case 1: c = new LinkedList<>(); break;
                    case 2: c = new ArrayDeque<>(); break;
                    default: c = new LogList<>(); break;
                }
                for (int i = 0; i < n; i++) c.add(r(15) == 0 && !(c instanceof ArrayDeque) ? null : new Key(r(6), i));
                reset();
                Comparator<Key> cmp = comparator();
                switch (r(4)) {
                    case 0: out.append(Collections.min(c)); break;
                    case 1: out.append(Collections.max(c)); break;
                    case 2: out.append(Collections.min(c, cmp)); break;
                    default: out.append(Collections.max(c, cmp)); break;
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(logged()).append(';');
        }
        List<Object> mixed = new ArrayList<>();
        int m = r(6);
        for (int i = 0; i < m; i++) mixed.add(r(4) == 0 ? (Object) ("s" + i) : (Object) Integer.valueOf(r(10)));
        try {
            out.append(r(2) == 0 ? Collections.min((Collection) mixed) : Collections.max((Collection) mixed));
        } catch (RuntimeException e) {
            out.append(ex(e));
        }
        Set<Integer> hs = new HashSet<>();
        for (int i = 0; i < m + 3; i++) hs.add(r(100) - 50);
        TreeSet<String> ts = new TreeSet<>(Comparator.reverseOrder());
        for (int i = 0; i < m + 2; i++) ts.add("t" + r(30));
        out.append(Collections.min(hs)).append(Collections.max(hs)).append(Collections.min(ts)).append(Collections.max(ts, Comparator.reverseOrder()));
        return out.toString();
    }

    /** Probes a list view: reads, writes (UnsupportedOperationException or a check), iterators. */
    @SuppressWarnings({"unchecked", "rawtypes"})
    static void probeList(StringBuilder out, List l) {
        out.append(l.getClass().getName()).append(l instanceof RandomAccess).append(l.size()).append(l).append(l.hashCode())
           .append(l.isEmpty()).append(l.contains(3)).append(l.indexOf(2)).append(l.lastIndexOf(2));
        String[] ops = new String[1];
        for (int k = 0; k < 5; k++) {
            try {
                switch (r(16)) {
                    case 0: out.append(l.get(r(l.size() + 2) - 1)); break;
                    case 1: out.append(l.set(r(l.size() + 1), r(3) == 0 ? "x" : (Object) Integer.valueOf(9))); break;
                    case 2: out.append(l.add(r(3) == 0 ? (Object) "y" : Integer.valueOf(8))); break;
                    case 3: l.add(r(l.size() + 1), 7); break;
                    case 4: out.append(l.remove(r(l.size() + 1))); break;
                    case 5: out.append(l.remove((Object) Integer.valueOf(2))); break;
                    case 6: out.append(l.addAll(Arrays.asList(5, r(2) == 0 ? "z" : (Object) 6))); break;
                    case 7: { ListIterator it = l.listIterator(r(l.size() + 1)); out.append(it.hasPrevious()).append(it.nextIndex());
                              if (it.hasNext()) { out.append(it.next()); it.set(r(2) == 0 ? "w" : (Object) 4); } it.add(3); break; }
                    case 8: { Iterator it = l.iterator(); if (it.hasNext()) out.append(it.next()); it.remove(); break; }
                    case 9: l.sort(null); out.append(l); break;
                    case 10: l.replaceAll(x -> x instanceof Integer ? (Object) ((Integer) x + 1) : "q"); out.append(l); break;
                    case 11: { List sub = l.subList(0, r(l.size() + 1)); out.append(sub.getClass().getName()).append(sub).append(sub instanceof RandomAccess); sub.clear(); break; }
                    case 12: out.append(l.removeIf(x -> x instanceof Integer && ((Integer) x) % 2 == 0)); break;
                    case 13: l.clear(); break;
                    case 14: out.append(l.equals(new ArrayList<>(l))).append(l.equals(l)).append(l.containsAll(Arrays.asList(1, 2))); break;
                    default: { StringBuilder b = new StringBuilder(); l.forEach(b::append); out.append(b).append(Arrays.toString(l.toArray()))
                              .append(Arrays.toString(l.toArray(new Object[r(5)]))); break; }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(',');
        }
        out.append(l);
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    static void probeNavSet(StringBuilder out, NavigableSet ns) {
        out.append(ns.getClass().getName()).append(ns).append(ns.size()).append(ns.hashCode());
        for (int k = 0; k < 5; k++) {
            int x = r(12);
            try {
                switch (r(14)) {
                    case 0: out.append(ns.first()).append(ns.last()); break;
                    case 1: out.append(ns.lower(x)).append(ns.floor(x)).append(ns.ceiling(x)).append(ns.higher(x)); break;
                    case 2: out.append(ns.pollFirst()); break;
                    case 3: out.append(ns.pollLast()); break;
                    case 4: { NavigableSet d = ns.descendingSet(); out.append(d.getClass().getName()).append(d); break; }
                    case 5: { Iterator it = ns.descendingIterator(); out.append(it.next()); it.remove(); break; }
                    case 6: { SortedSet ss = ns.subSet(x, x + 4); out.append(ss.getClass().getName()).append(ss); break; }
                    case 7: { NavigableSet ss = ns.subSet(x, r(2) == 0, x + 5, r(2) == 0); out.append(ss).append(ss.getClass().getName()); break; }
                    case 8: out.append(ns.headSet(x)).append(ns.tailSet(x)).append(ns.headSet(x, true)).append(ns.tailSet(x, false)); break;
                    case 9: out.append(ns.add(r(3) == 0 ? (Object) "s" : Integer.valueOf(x))); break;
                    case 10: out.append(ns.remove(x)); break;
                    case 11: out.append(ns.comparator() == null); break;
                    case 12: { SortedSet h = ns.headSet(x); out.append(h.add(x - 1)).append(h); break; }
                    default: out.append(ns.contains(x)).append(ns.equals(new TreeSet<>(ns))); break;
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(',');
        }
        out.append(ns);
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    static void probeNavMap(StringBuilder out, NavigableMap nm) {
        out.append(nm.getClass().getName()).append(nm).append(nm.size()).append(nm.hashCode());
        for (int k = 0; k < 5; k++) {
            int x = r(12);
            try {
                switch (r(16)) {
                    case 0: out.append(nm.firstKey()).append(nm.lastKey()); break;
                    case 1: out.append(nm.lowerKey(x)).append(nm.floorKey(x)).append(nm.ceilingKey(x)).append(nm.higherKey(x)); break;
                    case 2: { Map.Entry e = r(2) == 0 ? nm.floorEntry(x) : nm.firstEntry(); out.append(e); if (e != null) { out.append(cn(e)); e.setValue("v"); } break; }
                    case 3: out.append(nm.pollFirstEntry()); break;
                    case 4: { NavigableMap d = nm.descendingMap(); out.append(d.getClass().getName()).append(d); break; }
                    case 5: { NavigableSet ks = nm.navigableKeySet(); out.append(ks.getClass().getName()).append(ks); ks.remove(x); break; }
                    case 6: { SortedMap sm = nm.subMap(x, x + 4); out.append(sm.getClass().getName()).append(sm); break; }
                    case 7: out.append(nm.headMap(x)).append(nm.tailMap(x, false)).append(nm.subMap(x, true, x + 3, true)); break;
                    case 8: out.append(nm.put(x, r(3) == 0 ? (Object) "bad" : Integer.valueOf(x * 10))); break;
                    case 9: out.append(nm.remove(x)); break;
                    case 10: { Set es = nm.entrySet(); out.append(es.getClass().getName()).append(es).append(es.contains(new AbstractMap.SimpleEntry(x, x * 10)));
                               Iterator it = es.iterator(); if (it.hasNext()) { Map.Entry e = (Map.Entry) it.next(); out.append(cn(e)); e.setValue(r(2) == 0 ? (Object) 5 : "w"); } break; }
                    case 11: { Set ks = nm.keySet(); out.append(ks.getClass().getName()).append(ks); break; }
                    case 12: out.append(nm.values()).append(nm.values().getClass().getName()); break;
                    case 13: out.append(nm.computeIfAbsent(x, kk -> r(2) == 0 ? (Object) "c" : Integer.valueOf(1))); break;
                    case 14: out.append(nm.merge(x, 3, (a, b) -> r(2) == 0 ? (Object) "m" : Integer.valueOf(2))); break;
                    default: { nm.replaceAll((kk, v) -> r(4) == 0 ? (Object) "r" : Integer.valueOf(7)); break; }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(',');
        }
        out.append(nm).append(nm.equals(new TreeMap<>(nm)));
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String views(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 3; round++) {
            int n = r(7);
            try {
                switch (r(9)) {
                    case 0: case 1: {
                        List base = r(2) == 0 ? new ArrayList() : new LinkedList();
                        for (int i = 0; i < n; i++) base.add(r(5));
                        List v;
                        switch (r(4)) {
                            case 0: v = Collections.unmodifiableList(base); out.append(Collections.unmodifiableList(v) == v); break;
                            case 1: v = Collections.synchronizedList(base); break;
                            case 2: v = Collections.checkedList(base, (Class) Integer.class); break;
                            default: v = Collections.unmodifiableList(Collections.synchronizedList(base)); break;
                        }
                        probeList(out, v);
                        out.append(base);
                        break;
                    }
                    case 2: case 3: {
                        TreeSet base = new TreeSet();
                        for (int i = 0; i < n + 2; i++) base.add(r(12));
                        NavigableSet v;
                        switch (r(4)) {
                            case 0: v = Collections.unmodifiableNavigableSet(base); out.append(Collections.unmodifiableNavigableSet(v) == v); break;
                            case 1: v = Collections.synchronizedNavigableSet(base); break;
                            case 2: v = Collections.checkedNavigableSet(base, (Class) Integer.class); break;
                            default: v = (NavigableSet) Collections.emptyNavigableSet(); break;
                        }
                        probeNavSet(out, v);
                        out.append(base);
                        break;
                    }
                    case 4: case 5: {
                        TreeMap base = new TreeMap();
                        for (int i = 0; i < n + 2; i++) base.put(r(12), r(100));
                        NavigableMap v;
                        switch (r(4)) {
                            case 0: v = Collections.unmodifiableNavigableMap(base); out.append(Collections.unmodifiableNavigableMap(v) == v); break;
                            case 1: v = Collections.synchronizedNavigableMap(base); break;
                            case 2: v = Collections.checkedNavigableMap(base, (Class) Integer.class, (Class) Integer.class); break;
                            default: v = (NavigableMap) Collections.emptyNavigableMap(); break;
                        }
                        probeNavMap(out, v);
                        out.append(base);
                        break;
                    }
                    case 6: {
                        // sorted (not navigable) views
                        TreeSet bs = new TreeSet();
                        TreeMap bm = new TreeMap();
                        for (int i = 0; i < n + 1; i++) { bs.add(r(9)); bm.put(r(9), "v" + i); }
                        SortedSet ss = r(3) == 0 ? Collections.unmodifiableSortedSet(bs) : r(2) == 0 ? Collections.synchronizedSortedSet(bs)
                            : Collections.checkedSortedSet(bs, (Class) Integer.class);
                        SortedMap sm = r(3) == 0 ? Collections.unmodifiableSortedMap(bm) : r(2) == 0 ? Collections.synchronizedSortedMap(bm)
                            : Collections.checkedSortedMap(bm, (Class) Integer.class, (Class) String.class);
                        out.append(ss.getClass().getName()).append(ss).append(sm.getClass().getName()).append(sm);
                        int x = r(9);
                        SortedSet h = ss.headSet(x), t = ss.tailSet(x), sub = ss.subSet(x, x + 3);
                        out.append(h.getClass().getName()).append(h).append(t).append(sub).append(ss.first()).append(ss.last());
                        SortedMap hm = sm.headMap(x), tm = sm.tailMap(x), subm = sm.subMap(x, x + 3);
                        out.append(hm.getClass().getName()).append(hm).append(tm).append(subm).append(sm.firstKey()).append(sm.lastKey());
                        try { out.append(ss.add(r(2) == 0 ? (Object) "q" : 4)); } catch (RuntimeException e) { out.append(ex(e)); }
                        try { out.append(sm.put(4, r(2) == 0 ? (Object) 5 : "w")); } catch (RuntimeException e) { out.append(ex(e)); }
                        try { out.append(Collections.emptySortedSet().first()); } catch (RuntimeException e) { out.append(ex(e)); }
                        try { out.append(Collections.emptySortedMap().headMap(3)); } catch (RuntimeException e) { out.append(ex(e)); }
                        out.append(bs).append(bm);
                        break;
                    }
                    case 7: {
                        // collections, sets and maps (HashMap / LinkedHashMap / HashSet: deterministic orders)
                        Map base = r(2) == 0 ? new HashMap() : new LinkedHashMap();
                        for (int i = 0; i < n; i++) base.put("k" + r(9), r(3) == 0 ? null : (Object) Integer.valueOf(i));
                        Map v;
                        switch (r(3)) {
                            case 0: v = Collections.unmodifiableMap(base); out.append(Collections.unmodifiableMap(v) == v); break;
                            case 1: v = Collections.synchronizedMap(base); break;
                            default: v = Collections.checkedMap(base, (Class) String.class, (Class) Integer.class); break;
                        }
                        out.append(v.getClass().getName()).append(v).append(v.hashCode()).append(v.equals(base)).append(v.get("k1"))
                           .append(v.getOrDefault("k2", "d")).append(v.containsKey("k3")).append(v.containsValue(1));
                        out.append(v.keySet().getClass().getName()).append(v.keySet()).append(v.values().getClass().getName()).append(v.values())
                           .append(v.entrySet().getClass().getName()).append(v.entrySet()).append(v.keySet() == v.keySet()).append(v.entrySet() == v.entrySet());
                        for (int k = 0; k < 4; k++) {
                            try {
                                switch (r(10)) {
                                    case 0: out.append(v.put("k" + r(9), r(3) == 0 ? (Object) "bad" : Integer.valueOf(4))); break;
                                    case 1: out.append(v.remove("k" + r(9))); break;
                                    case 2: v.putAll(Map.of("p", r(2) == 0 ? (Object) 1 : "bad")); break;
                                    case 3: { Iterator<Map.Entry> it = v.entrySet().iterator(); if (it.hasNext()) { Map.Entry e = it.next(); out.append(e).append(cn(e)); e.setValue(r(2) == 0 ? (Object) 3 : "w"); } break; }
                                    case 4: out.append(Arrays.toString(v.entrySet().toArray())); break;
                                    case 5: { StringBuilder b = new StringBuilder(); v.forEach((a, c) -> b.append(a).append('=').append(c)); v.entrySet().forEach(e -> b.append(((Map.Entry) e).getKey())); out.append(b); break; }
                                    case 6: out.append(v.putIfAbsent("k" + r(9), 3)).append(v.replace("k" + r(9), 4)); break;
                                    case 7: out.append(v.compute("k" + r(9), (a, c) -> r(3) == 0 ? (Object) "c" : Integer.valueOf(2))); break;
                                    case 8: out.append(v.entrySet().contains(new AbstractMap.SimpleEntry("k1", 1))).append(v.entrySet().remove(new AbstractMap.SimpleEntry("k2", 2))); break;
                                    default: v.clear(); break;
                                }
                            } catch (RuntimeException e) {
                                out.append(ex(e));
                            }
                            out.append(',');
                        }
                        out.append(base);
                        break;
                    }
                    default: {
                        Collection base = r(2) == 0 ? new ArrayList() : r(2) == 0 ? new HashSet() : new ArrayDeque();
                        for (int i = 0; i < n; i++) base.add(r(6));
                        Collection v;
                        switch (r(7)) {
                            case 0: v = Collections.unmodifiableCollection(base); out.append(Collections.unmodifiableCollection(v) == v); break;
                            case 1: v = Collections.synchronizedCollection(base); break;
                            case 2: v = Collections.checkedCollection(base, (Class) Integer.class); break;
                            case 3: v = base instanceof Set ? Collections.unmodifiableSet((Set) base) : Collections.unmodifiableCollection(base); break;
                            case 4: v = base instanceof Set ? Collections.synchronizedSet((Set) base) : Collections.synchronizedCollection(base); break;
                            case 5: v = base instanceof Set ? Collections.checkedSet((Set) base, (Class) Integer.class) : Collections.checkedCollection(base, (Class) Integer.class); break;
                            default: v = base instanceof ArrayDeque ? Collections.checkedQueue((Queue) base, (Class) Integer.class) : Collections.unmodifiableCollection(base); break;
                        }
                        out.append(v.getClass().getName()).append(v).append(v.size()).append(v.contains(2)).append(v.containsAll(Arrays.asList(1, 2)));
                        for (int k = 0; k < 4; k++) {
                            try {
                                switch (r(9)) {
                                    case 0: out.append(v.add(r(3) == 0 ? (Object) "bad" : Integer.valueOf(r(6)))); break;
                                    case 1: out.append(v.remove(r(6))); break;
                                    case 2: out.append(v.addAll(r(2) == 0 ? Arrays.asList(1, 2) : r(2) == 0 ? Arrays.asList(3, "bad") : new LinkedList(Arrays.asList("x", 4)))); break;
                                    case 3: out.append(v.removeAll(Arrays.asList(1))).append(v.retainAll(Arrays.asList(2, 3, 4, 5))); break;
                                    case 4: { Iterator it = v.iterator(); if (it.hasNext()) out.append(it.next()); it.remove(); break; }
                                    case 5: out.append(v.removeIf(x -> x instanceof Integer && ((Integer) x) > 3)); break;
                                    case 6: out.append(Arrays.toString(v.toArray())).append(Arrays.toString(v.toArray(new Integer[0]))); break;
                                    case 7: if (v instanceof Queue) { Queue q = (Queue) v; out.append(q.offer(r(2) == 0 ? (Object) "o" : 9)).append(q.peek()).append(q.poll()).append(q.element()); } else v.clear(); break;
                                    default: out.append(v.equals(base)).append(v.hashCode() == base.hashCode()).append(v.stream().count()); break;
                                }
                            } catch (RuntimeException e) {
                                out.append(ex(e));
                            }
                            out.append(',');
                        }
                        out.append(base);
                        break;
                    }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(';');
        }
        return out.toString();
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String misc(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        // nCopies
        int n = r(8) - 1;
        Object e = r(4) == 0 ? null : "e";
        try {
            List c = Collections.nCopies(n, e);
            out.append(c).append(c.size()).append(c.hashCode()).append(c.indexOf("e")).append(c.lastIndexOf(null)).append(c.contains(e))
               .append(c.equals(new ArrayList(c))).append(c.equals(Collections.nCopies(n, e))).append(new ArrayList(c).equals(c))
               .append(Arrays.toString(c.toArray())).append(Arrays.toString(c.toArray(new String[r(8)])));
            out.append(c.stream().count());
            out.append(c.subList(r(3), r(n + 2)));
            out.append(c.get(r(n + 2) - 1));
        } catch (RuntimeException x) {
            out.append(ex(x));
        }
        out.append(';');
        // singletons
        Object one = r(3) == 0 ? null : Integer.valueOf(r(5));
        Set s1 = Collections.singleton(one);
        List l1 = Collections.singletonList(one);
        Map m1 = Collections.singletonMap(r(2) == 0 ? null : "k", one);
        out.append(s1).append(s1.hashCode()).append(s1.contains(one)).append(l1).append(l1.hashCode()).append(l1.indexOf(one))
           .append(m1).append(m1.hashCode()).append(m1.get("k")).append(m1.keySet()).append(m1.values()).append(m1.entrySet())
           .append(m1.containsValue(one)).append(m1.getOrDefault("z", "d")).append(m1.keySet() == m1.keySet()).append(m1.equals(new HashMap(m1)));
        try {
            switch (r(6)) {
                case 0: l1.get(r(3)); break;
                case 1: s1.add(1); break;
                case 2: m1.put("a", 1); break;
                case 3: s1.forEach(null); break;
                case 4: m1.forEach(null); break;
                default: m1.entrySet().iterator().next().hashCode(); l1.set(0, 1); break;
            }
        } catch (RuntimeException x) {
            out.append(ex(x));
        }
        out.append(';');
        // empties
        out.append(Collections.emptyList() == Collections.EMPTY_LIST).append(Collections.emptySet() == Collections.EMPTY_SET)
           .append(Collections.emptyMap() == Collections.EMPTY_MAP).append(Collections.emptyIterator() == Collections.emptyIterator())
           .append(Collections.emptyListIterator() == Collections.emptyListIterator()).append(Collections.emptyEnumeration() == Collections.emptyEnumeration())
           .append(Collections.emptySortedSet() == Collections.emptyNavigableSet()).append(Collections.emptySortedMap() == Collections.emptyNavigableMap())
           .append(Collections.emptyNavigableMap().navigableKeySet() == Collections.emptyNavigableSet())
           .append(Collections.emptyListIterator().hasPrevious()).append(Collections.emptyListIterator().nextIndex())
           .append(Collections.emptyListIterator().previousIndex()).append(Collections.emptyEnumeration().hasMoreElements())
           .append(Collections.emptyEnumeration().asIterator().hasNext()).append(Collections.emptyNavigableSet()).append(Collections.emptyNavigableMap())
           .append(Collections.emptySortedSet().getClass().getName()).append(Collections.emptySortedMap().getClass().getName());
        try {
            switch (r(7)) {
                case 0: Collections.emptyListIterator().previous(); break;
                case 1: Collections.emptyEnumeration().nextElement(); break;
                case 2: Collections.emptyListIterator().set(1); break;
                case 3: Collections.emptyNavigableSet().add(1); break;
                case 4: Collections.emptyNavigableMap().firstKey(); break;
                case 5: Collections.emptyList().toArray((Object[]) null); break;
                default: Collections.emptyIterator().remove(); break;
            }
        } catch (RuntimeException x) {
            out.append(ex(x));
        }
        out.append(';');
        // enumeration / list / frequency / disjoint / addAll
        List<Integer> a = new ArrayList<>();
        int k = r(8);
        for (int i = 0; i < k; i++) a.add(r(4) == 0 ? null : r(5));
        Enumeration<Integer> en = Collections.enumeration(a);
        out.append(en.getClass().getName()).append(Collections.list(en)).append(Collections.list(Collections.enumeration(new HashSet<>(a))));
        out.append(Collections.frequency(a, null)).append(Collections.frequency(a, 2)).append(Collections.frequency(new LinkedList<>(a), 3));
        reset();
        List<Key> ka = new ArrayList<>(), kb = new ArrayList<>();
        for (int i = 0; i < r(6); i++) ka.add(new Key(r(6), i));
        for (int i = 0; i < r(6); i++) kb.add(new Key(r(6), 10 + i));
        out.append(Collections.disjoint(ka, kb)).append(logged()).append(Collections.disjoint(new HashSet<>(ka), kb)).append(logged())
           .append(Collections.disjoint(ka, new HashSet<>(kb))).append(logged()).append(Collections.frequency(ka, ka.isEmpty() ? null : ka.get(0))).append(logged());
        List<Object> dst = r(2) == 0 ? new ArrayList<>() : new LinkedList<>();
        out.append(Collections.addAll(dst, 1, "two", null)).append(Collections.addAll(new HashSet<>(Arrays.asList(1)), 1)).append(dst);
        out.append(';');
        // newSetFromMap / asLifoQueue
        Map<Object, Boolean> back = r(2) == 0 ? new HashMap<>() : r(2) == 0 ? new LinkedHashMap<>() : new TreeMap<>();
        Set<Object> sfm = Collections.newSetFromMap(back);
        for (int i = 0; i < 5; i++) out.append(sfm.add(r(6)));
        out.append(sfm.remove(2)).append(sfm.contains(3)).append(sfm).append(back).append(sfm.hashCode()).append(sfm.equals(new HashSet<>(sfm)))
           .append(sfm.getClass().getName()).append(Arrays.toString(sfm.toArray()));
        try {
            Collections.newSetFromMap(back);
        } catch (RuntimeException x) {
            out.append(ex(x));
        }
        Deque<Integer> dq = r(2) == 0 ? new ArrayDeque<>() : new LinkedList<>();
        Queue<Integer> lifo = Collections.asLifoQueue(dq);
        for (int i = 0; i < 4; i++) lifo.add(r(9));
        out.append(lifo.offer(7)).append(lifo.peek()).append(lifo.poll()).append(lifo.remove()).append(lifo.element()).append(lifo).append(dq)
           .append(lifo.size()).append(lifo.getClass().getName()).append(lifo.contains(7)).append(lifo.remove((Object) 7));
        lifo.clear();
        try {
            lifo.remove();
        } catch (RuntimeException x) {
            out.append(ex(x));
        }
        out.append(';');
        // reverseOrder
        Comparator<Integer> ro = Collections.reverseOrder(), nat = Comparator.naturalOrder();
        Comparator<Integer> c2 = (x, y) -> x - y;
        out.append(Collections.reverseOrder((Comparator<Integer>) null) == ro).append(Collections.reverseOrder(ro) == (Comparator) nat).append(Collections.reverseOrder(nat) == ro)
           .append(Collections.reverseOrder(Collections.reverseOrder(c2)) == c2).append(ro.reversed() == (Comparator) nat)
           .append(ro.compare(1, 2)).append(Collections.reverseOrder(c2).compare(1, 5)).append(Collections.reverseOrder(c2).reversed() == c2)
           .append(Collections.reverseOrder(c2).equals(Collections.reverseOrder(c2)));
        try {
            out.append(r(2) == 0 ? ro.compare(1, null) : ((Comparator) nat).compare(null, 1));
        } catch (RuntimeException x) {
            out.append(ex(x));
        }
        return out.toString();
    }

    /** The null and argument checks of every static method of Collections. */
    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String nulls(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        List ln = null;
        Collection cn = null;
        for (int round = 0; round < 6; round++) {
            try {
                switch (r(46)) {
                    case 0: Collections.sort(ln); break;
                    case 1: Collections.sort(ln, Comparator.naturalOrder()); break;
                    case 2: Collections.binarySearch(ln, 1); break;
                    case 3: Collections.binarySearch(ln, 1, Comparator.naturalOrder()); break;
                    case 4: Collections.binarySearch(Arrays.asList(null, null, null), 1); break;
                    case 5: Collections.binarySearch(new LinkedList(Arrays.asList(1, null, 3)), 0); break;
                    case 6: Collections.reverse(ln); break;
                    case 7: Collections.fill(ln, 1); break;
                    case 8: Collections.copy(new ArrayList(), ln); break;
                    case 9: Collections.copy(ln, new ArrayList()); break;
                    case 10: Collections.copy(new ArrayList(Arrays.asList(1)), Arrays.asList(1, 2)); break;
                    case 11: Collections.min(cn); break;
                    case 12: Collections.max(cn, Comparator.naturalOrder()); break;
                    case 13: Collections.min(new ArrayList()); break;
                    case 14: Collections.max(Arrays.asList(1, null, 2)); break;
                    case 15: Collections.rotate(ln, 1); break;
                    case 16: Collections.replaceAll(ln, 1, 2); break;
                    case 17: Collections.indexOfSubList(ln, new ArrayList()); break;
                    case 18: Collections.lastIndexOfSubList(new ArrayList(), ln); break;
                    case 19: Collections.unmodifiableCollection(cn); break;
                    case 20: Collections.unmodifiableSet(null); break;
                    case 21: Collections.unmodifiableSortedSet(null); break;
                    case 22: Collections.unmodifiableNavigableSet(null); break;
                    case 23: Collections.unmodifiableList(null); break;
                    case 24: Collections.unmodifiableMap(null); break;
                    case 25: Collections.unmodifiableSortedMap(null); break;
                    case 26: Collections.unmodifiableNavigableMap(null); break;
                    case 27: Collections.synchronizedCollection(null); break;
                    case 28: Collections.synchronizedList(null); break;
                    case 29: Collections.synchronizedNavigableMap(null); break;
                    case 30: Collections.checkedCollection(null, String.class); break;
                    case 31: Collections.checkedList(new ArrayList(), null); break;
                    case 32: Collections.checkedMap(null, String.class, String.class); break;
                    case 33: Collections.checkedCollection(new ArrayList(), (Class) int.class).addAll(Arrays.asList(1)); break;
                    case 34: Collections.nCopies(-r(3) - 1, "a"); break;
                    case 35: Collections.enumeration(null); break;
                    case 36: Collections.list(null); break;
                    case 37: Collections.frequency(null, r(2) == 0 ? null : 1); break;
                    case 38: Collections.disjoint(r(2) == 0 ? null : new ArrayList(), r(2) == 0 ? null : new HashSet()); break;
                    case 39: Collections.disjoint(r(2) == 0 ? null : new HashSet(), r(2) == 0 ? null : new ArrayList(Arrays.asList(1))); break;
                    case 40: Collections.addAll(null, r(2) == 0 ? new Object[0] : new Object[]{1}); break;
                    case 41: Collections.addAll(new ArrayList(), (Object[]) null); break;
                    case 42: Collections.newSetFromMap(r(2) == 0 ? null : Map.of(1, true)); break;
                    case 43: Collections.asLifoQueue(null); break;
                    case 44: Collections.swap(ln, 0, 1); break;
                    default: Collections.shuffle(ln, new Random(1)); break;
                }
                out.append("ok");
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(';');
        }
        return out.toString();
    }
}

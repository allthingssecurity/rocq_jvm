package org.rocqjvm.jdkmodel;

import java.util.*;
import java.util.concurrent.*;

/** Differential tests of ConcurrentSkipListMap / ConcurrentSkipListSet, one thread: map
 *  operations, navigation, sub maps and descending views, weakly consistent iterators under
 *  modification, clone, equals, null / type / range errors. */
public final class SkipOps {
    private SkipOps() {
    }

    static final class Log {
        final StringBuilder sb = new StringBuilder();
        int s;

        Log(int seed) {
            s = seed;
        }

        int r(int n) {
            s = s * 1103515245 + 12345;
            return ((s >>> 8) & 0x7fffff) % n;
        }

        void a(Object o) {
            sb.append(o).append(';');
        }

        void e(Throwable t) {
            sb.append('!').append(t.getClass().getName()).append(':').append(t.getMessage()).append(';');
        }
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    static ConcurrentSkipListMap<Object, Object> make(Log t, int mode) {
        if (mode == 1) return new ConcurrentSkipListMap<>((a, b) -> Integer.compare((Integer) b, (Integer) a));
        return new ConcurrentSkipListMap<>();
    }

    static Object key(Log t, int mode) {
        if (mode == 2) return "k" + t.r(25);
        if (t.r(40) == 0) return null;
        return t.r(30) - 5;
    }

    /** A random navigable view of m (the map itself, descending, a sub/head/tail map, nested). */
    @SuppressWarnings("unchecked")
    static ConcurrentNavigableMap<Object, Object> view(Log t, ConcurrentSkipListMap<Object, Object> m, int mode) {
        ConcurrentNavigableMap<Object, Object> v = m;
        int depth = t.r(3);
        for (int i = 0; i < depth; i++) {
            Object a = key(t, mode), b = key(t, mode);
            if (a == null) a = mode == 2 ? "k5" : (Object) 3;
            if (b == null) b = mode == 2 ? "k20" : (Object) 18;
            boolean ai = t.r(2) == 0, bi = t.r(2) == 0;
            switch (t.r(5)) {
                case 0: v = v.descendingMap(); break;
                case 1: v = v.headMap(b, bi); break;
                case 2: v = v.tailMap(a, ai); break;
                case 3: v = v.subMap(a, ai, b, bi); break;
                default: v = v.subMap(a, b); break;
            }
        }
        return v;
    }

    static void ops(Log t, ConcurrentNavigableMap<Object, Object> m, int mode, int n) {
        for (int i = 0; i < n; i++) {
            Object k = key(t, mode);
            Integer v = t.r(6);
            try {
                switch (t.r(34)) {
                    case 0: case 1: case 2: case 3: t.a(m.put(k, v)); break;
                    case 4: t.a(m.get(k)); break;
                    case 5: t.a(m.remove(k)); break;
                    case 6: t.a(m.containsKey(k) + "," + m.containsValue(v)); break;
                    case 7: t.a(m.firstKey() + "," + m.lastKey()); break;
                    case 8: t.a(m.firstEntry() + "," + m.lastEntry()); break;
                    case 9: t.a(m.floorKey(k) + "," + m.ceilingKey(k) + "," + m.lowerKey(k) + "," + m.higherKey(k)); break;
                    case 10: t.a(m.floorEntry(k) + "," + m.higherEntry(k) + "," + m.lowerEntry(k) + "," + m.ceilingEntry(k)); break;
                    case 11: t.a(m.pollFirstEntry()); break;
                    case 12: t.a(m.pollLastEntry()); break;
                    case 13: t.a(m + "/" + m.size() + "/" + m.isEmpty()); break;
                    case 14: t.a(m.keySet() + "|" + m.values() + "|" + m.entrySet()); break;
                    case 15: t.a(m.putIfAbsent(k, v)); break;
                    case 16: t.a(m.computeIfAbsent(k, x -> v == 0 ? null : (Object) (v * 7))); break;
                    case 17: t.a(m.merge(k, v + 1, (a, b) -> (Integer) a > 3 ? null : (Object) ((Integer) a + (Integer) b))); break;
                    case 18: t.a(m.compute(k, (x, o) -> o == null ? (Object) 1 : null)); break;
                    case 19: t.a(m.replace(k, v) + "," + m.replace(k, v, 5)); break;
                    case 20: {
                        Iterator<Map.Entry<Object, Object>> it = m.entrySet().iterator();
                        while (it.hasNext()) {
                            Map.Entry<Object, Object> e = it.next();
                            if (t.r(3) == 0) it.remove();
                            else if (t.r(4) == 0) e.setValue(9);
                        }
                        t.a(m);
                        break;
                    }
                    case 21: t.a(m.remove(k, v) + "," + m.computeIfPresent(k, (x, o) -> (Integer) o > 2 ? null : (Object) ((Integer) o + 10))); break;
                    case 22: t.a(m.descendingMap() + "|" + m.descendingKeySet() + "|" + m.navigableKeySet().descendingSet()); break;
                    case 23: {
                        NavigableSet<Object> ks = m.keySet();
                        t.a(ks.first() + "," + ks.last() + "," + ks.floor(k) + "," + ks.higher(k) + "," + ks.pollFirst() + "," + ks.size());
                        break;
                    }
                    case 24: {
                        StringBuilder b = new StringBuilder();
                        m.forEach((a, c) -> b.append(a).append(':').append(c).append(' '));
                        t.a(b);
                        break;
                    }
                    case 25: m.replaceAll((a, c) -> (Integer) c + 1); t.a(m.values()); break;
                    case 26: t.a(m.values().removeIf(x -> (Integer) x % 3 == 0) + "," + m); break;
                    case 27: t.a(m.entrySet().removeIf(e -> e.getValue().equals(v)) + "," + m.keySet().removeIf(x -> x.hashCode() % 4 == 0) + "," + m); break;
                    case 28: t.a(m.headMap(k) + "|" + m.tailMap(k, false) + "|" + m.headMap(k, true).size()); break;
                    case 29: t.a(m.equals(new TreeMap<>(m)) + "," + m.hashCode() + "," + m.keySet().hashCode() + "," + m.entrySet().equals(new HashSet<>(m.entrySet()))); break;
                    case 30: t.a(m.getOrDefault(k, "d") + "," + m.keySet().contains(k) + "," + m.values().contains(v) + "," + m.entrySet().contains(new AbstractMap.SimpleEntry<>(k, v))); break;
                    case 31: t.a(Arrays.toString(m.keySet().toArray()) + Arrays.toString(m.values().toArray(new Integer[0])) + m.entrySet().toArray().length); break;
                    case 32: {
                        Iterator<Object> it = (t.r(2) == 0 ? m.keySet() : m.descendingKeySet()).iterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            Object x = it.next();
                            b.append(x).append(' ');
                            if (t.r(4) == 0) it.remove();
                        }
                        t.a(b + "" + m.size());
                        break;
                    }
                    default: if (t.r(6) == 0) { m.clear(); t.a("clr" + m.size()); } else t.a(m.isEmpty()); break;
                }
            } catch (RuntimeException e) {
                t.e(e);
            }
        }
    }

    /** Random operations on a map, a view of it, and both together. */
    public static String map(int seed) {
        Log t = new Log(seed);
        int mode = t.r(3);
        ConcurrentSkipListMap<Object, Object> m = make(t, mode);
        ops(t, m, mode, 20 + t.r(60));
        t.a(m);
        return t.sb.toString();
    }

    public static String views(int seed) {
        Log t = new Log(seed);
        int mode = t.r(3);
        ConcurrentSkipListMap<Object, Object> m = make(t, mode);
        for (int i = 0; i < 15; i++) {
            Object k = key(t, mode);
            if (k != null) m.put(k, t.r(6));
        }
        for (int j = 0; j < 3; j++) {
            try {
                ConcurrentNavigableMap<Object, Object> v = view(t, m, mode);
                t.a("V" + v);
                ops(t, v, mode, 5 + t.r(20));
                t.a(m);
            } catch (RuntimeException e) {
                t.e(e);
            }
        }
        return t.sb.toString();
    }

    /** Weakly consistent iteration: iterators of the map and its views interleaved with changes. */
    public static String iter(int seed) {
        Log t = new Log(seed);
        int mode = t.r(3);
        ConcurrentSkipListMap<Object, Object> m = make(t, mode);
        for (int i = 0; i < 12; i++) {
            Object k = key(t, mode);
            if (k != null) m.put(k, t.r(6));
        }
        List<Iterator<?>> its = new ArrayList<>();
        for (int step = 0; step < 60; step++) {
            try {
                switch (t.r(8)) {
                    case 0: {
                        ConcurrentNavigableMap<Object, Object> v = t.r(2) == 0 ? m : view(t, m, mode);
                        int w = t.r(3);
                        its.add(w == 0 ? v.keySet().iterator() : w == 1 ? v.values().iterator() : v.entrySet().iterator());
                        t.a("new" + its.size());
                        break;
                    }
                    case 1: case 2: {
                        if (its.isEmpty()) break;
                        Iterator<?> it = its.get(t.r(its.size()));
                        t.a(it.hasNext() ? it.next() : (Object) "end");
                        break;
                    }
                    case 3: {
                        Object k = key(t, mode);
                        if (k != null) t.a("p" + m.put(k, t.r(6)));
                        break;
                    }
                    case 4: {
                        Object k = key(t, mode);
                        if (k != null) t.a("r" + m.remove(k));
                        break;
                    }
                    case 5: {
                        if (its.isEmpty()) break;
                        its.get(t.r(its.size())).remove();
                        t.a("x" + m.size());
                        break;
                    }
                    case 6: t.a("f" + m.pollFirstEntry() + "," + m.pollLastEntry()); break;
                    default: if (t.r(8) == 0) { m.clear(); t.a("c"); } else t.a(m); break;
                }
            } catch (RuntimeException e) {
                t.e(e);
            }
        }
        return t.sb.toString();
    }

    /** ConcurrentSkipListSet, its views, clone and bulk operations. */
    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String set(int seed) {
        Log t = new Log(seed);
        int mode = t.r(3);
        ConcurrentSkipListSet<Object> s = mode == 1
            ? new ConcurrentSkipListSet<>((a, b) -> Integer.compare((Integer) b, (Integer) a)) : new ConcurrentSkipListSet<>();
        NavigableSet<Object> v = s;
        int n = 20 + t.r(50);
        for (int i = 0; i < n; i++) {
            Object k = key(t, mode);
            try {
                switch (t.r(20)) {
                    case 0: case 1: case 2: case 3: t.a(v.add(k)); break;
                    case 4: t.a(v.remove(k)); break;
                    case 5: t.a(v.contains(k)); break;
                    case 6: t.a(v.first() + "," + v.last()); break;
                    case 7: t.a(v.floor(k) + "," + v.ceiling(k) + "," + v.lower(k) + "," + v.higher(k)); break;
                    case 8: t.a(v.pollFirst() + "," + v.pollLast()); break;
                    case 9: t.a(v + "/" + v.size()); break;
                    case 10: {
                        Object a = key(t, mode), b = key(t, mode);
                        int w = t.r(4);
                        v = w == 0 ? s.subSet(a, b) : w == 1 ? s.headSet(b, t.r(2) == 0) : w == 2 ? s.tailSet(a) : s.descendingSet();
                        t.a("V" + v);
                        break;
                    }
                    case 11: v = s; t.a("S"); break;
                    case 12: {
                        ConcurrentSkipListSet<Object> c = s.clone();
                        c.add(mode == 2 ? "kc" : (Object) 99);
                        t.a(c + "|" + s + "|" + c.equals(s) + "|" + s.equals(new TreeSet<>(s)));
                        break;
                    }
                    case 13: t.a(s.removeAll(Arrays.asList(key(t, mode), key(t, mode))) + "," + s); break;
                    case 14: t.a(s.retainAll(new ArrayList<>(v)) + "," + s.addAll(Arrays.asList(key(t, mode))) + "," + s); break;
                    case 15: {
                        Iterator<Object> it = t.r(2) == 0 ? v.iterator() : v.descendingIterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            b.append(it.next()).append(' ');
                            if (t.r(3) == 0) it.remove();
                        }
                        t.a(b);
                        break;
                    }
                    case 16: t.a(s.hashCode() + "," + Arrays.toString(s.toArray()) + "," + s.isEmpty()); break;
                    case 17: t.a(new ConcurrentSkipListSet<>(s) + "|" + new ConcurrentSkipListSet<>(new ArrayList<>(s))); break;
                    case 18: t.a(v.removeIf(x -> x.hashCode() % 3 == 0) + "," + v); break;
                    default: t.a(v.descendingSet() + "|" + v.headSet(k) + "|" + v.tailSet(k, false)); break;
                }
            } catch (RuntimeException e) {
                t.e(e);
            }
        }
        t.a(s);
        return t.sb.toString();
    }

    /** Errors: nulls, types, ranges, empty maps; constructors; clone of an emptied map. */
    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String errors(int seed) {
        Log t = new Log(seed);
        ConcurrentSkipListMap<Object, Object> m = new ConcurrentSkipListMap<>();
        Object[] probes = { null, 1, "a", 2L };
        for (int i = 0; i < 40; i++) {
            Object k = probes[t.r(probes.length)];
            try {
                switch (t.r(22)) {
                    case 0: t.a(m.put(k, 1)); break;
                    case 1: t.a(m.put(1, null)); break;
                    case 2: t.a(m.get(k)); break;
                    case 3: t.a(m.remove(k)); break;
                    case 4: t.a(m.containsKey(k)); break;
                    case 5: t.a(m.containsValue(k)); break;
                    case 6: t.a(m.firstKey()); break;
                    case 7: t.a(m.lastKey()); break;
                    case 8: t.a(m.ceilingKey(k) + "," + m.floorEntry(k)); break;
                    case 9: t.a(m.subMap(k, probes[t.r(probes.length)])); break;
                    case 10: t.a(m.headMap(5).put(t.r(10), 1)); break;
                    case 11: t.a(m.tailMap(3, false).subMap(t.r(8), t.r(8))); break;
                    case 12: t.a(m.computeIfAbsent(k, null)); break;
                    case 13: t.a(m.merge(1, k, (a, b) -> b)); break;
                    case 14: t.a(m.remove(k, 1) + "," + m.replace(1, k)); break;
                    case 15: { Iterator<Object> it = m.keySet().iterator(); it.remove(); break; }
                    case 16: m.firstEntry().setValue(3); break;
                    case 17: t.a(m.pollFirstEntry() + "," + m.isEmpty()); break;
                    case 18: {
                        ConcurrentSkipListMap<Object, Object> c = m.clone();
                        c.put(1, "c");
                        t.a(m + "|" + m.size() + "|" + c + "|" + c.size());
                        break;
                    }
                    case 19: t.a(new ConcurrentSkipListMap<>(new TreeMap<>(m)) + "," + new ConcurrentSkipListMap<>(new HashMap<>(Map.of(1, 2)))); break;
                    case 20: t.a(m.descendingMap().headMap(k)); break;
                    default: if (m.isEmpty()) m.put(t.r(3), "v"); else m.clear(); t.a(m); break;
                }
            } catch (RuntimeException e) {
                t.e(e);
            }
        }
        try {
            new ConcurrentSkipListMap<Object, Object>((SortedMap<Object, Object>) null);
        } catch (RuntimeException e) {
            t.e(e);
        }
        try {
            new ConcurrentSkipListSet<Object>().add(null);
        } catch (RuntimeException e) {
            t.e(e);
        }
        try {
            new ConcurrentSkipListSet<Object>().remove(null);
        } catch (RuntimeException e) {
            t.e(e);
        }
        return t.sb.toString();
    }
}

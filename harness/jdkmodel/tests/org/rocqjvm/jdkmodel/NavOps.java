package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of the navigable views of TreeMap and TreeSet: subMap/headMap/tailMap,
 *  descendingMap, navigableKeySet/descendingKeySet, nested views, range checks and their
 *  messages, view iterators (remove, fail-fast), and TreeSet subSet/headSet/tailSet/
 *  descendingSet/descendingIterator. Exceptions are printed as class simple name ':' message. */
public final class NavOps {
    private NavOps() {
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

        boolean b() {
            return r(2) == 0;
        }

        void a(Object o) {
            sb.append(o).append(';');
        }

        void e(Throwable t) {
            sb.append('!').append(t.getClass().getSimpleName()).append(':').append(t.getMessage()).append(';');
        }
    }

    /** 0: natural Integer, 1: descending comparator, 2: natural String, 3: comparator with nulls first. */
    static Object key(Log t, int mode) {
        if (mode == 2) return t.r(25) == 0 ? (Object) Integer.valueOf(3) : "k" + (char) ('a' + t.r(20));
        if (t.r(25) == 0) return null;
        if (mode == 0 && t.r(30) == 0) return "str";
        return t.r(40) - 10;
    }

    static int cmpNullsFirst(Object a, Object b) {
        if (a == null) return b == null ? 0 : -1;
        if (b == null) return 1;
        return ((Integer) a).compareTo((Integer) b);
    }

    static int cmpDesc(Object a, Object b) {
        if (a == null || b == null) throw new IllegalStateException("null in cmpDesc");
        return Integer.compare((Integer) b, (Integer) a);
    }

    static TreeMap<Object, Object> make(int mode) {
        if (mode == 1) return new TreeMap<>(NavOps::cmpDesc);
        if (mode == 3) return new TreeMap<>(NavOps::cmpNullsFirst);
        return new TreeMap<>();
    }

    static String cmpInfo(Comparator<? super Object> c, int mode) {
        if (c == null) return "natural";
        if (mode == 2) return "c" + Integer.signum(c.compare("ka", "kb"));
        return "c" + Integer.signum(c.compare(1, 2));
    }

    /** A new view of m (or of the map itself). */
    static NavigableMap<Object, Object> view(Log t, NavigableMap<Object, Object> m, int mode) {
        Object a = key(t, mode), b = key(t, mode);
        switch (t.r(9)) {
            case 0: return m.subMap(a, t.b(), b, t.b());
            case 1: return m.headMap(a, t.b());
            case 2: return m.tailMap(a, t.b());
            case 3: return m.descendingMap();
            case 4: return (NavigableMap<Object, Object>) m.subMap(a, b);
            case 5: return (NavigableMap<Object, Object>) m.headMap(a);
            case 6: return (NavigableMap<Object, Object>) m.tailMap(a);
            default: return m;
        }
    }

    static String iter(Iterator<?> it) {
        StringBuilder b = new StringBuilder("<");
        while (it.hasNext()) b.append(it.next()).append(' ');
        return b.append('>').toString();
    }

    public static String fuzz(int seed) {
        Log t = new Log(seed);
        int mode = t.r(4);
        TreeMap<Object, Object> base = make(mode);
        for (int i = t.r(15); i > 0; i--) {
            try {
                base.put(key(t, mode), t.r(9));
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        NavigableMap<Object, Object> v = base;
        NavigableMap<Object, Object> v2 = base;
        int n = 25 + t.r(60);
        for (int i = 0; i < n; i++) {
            Object k = key(t, mode);
            Integer val = t.r(6);
            NavigableMap<Object, Object> w = t.r(4) == 0 ? v2 : v;
            try {
                switch (t.r(42)) {
                    case 0: v2 = v; v = view(t, base, mode); t.a("V" + v); break;
                    case 1: v2 = view(t, v, mode); t.a("W" + v2); break;
                    case 2: case 3: t.a(w.put(k, val)); break;
                    case 4: t.a(base.put(k, val)); break;
                    case 5: t.a(w.get(k) + "," + w.containsKey(k)); break;
                    case 6: t.a(w.remove(k)); break;
                    case 7: t.a(w.firstKey() + "," + w.lastKey()); break;
                    case 8: t.a(w.firstEntry() + "," + w.lastEntry()); break;
                    case 9: t.a(w.floorKey(k) + "," + w.ceilingKey(k) + "," + w.lowerKey(k) + "," + w.higherKey(k)); break;
                    case 10: t.a(w.floorEntry(k) + "," + w.ceilingEntry(k) + "," + w.lowerEntry(k) + "," + w.higherEntry(k)); break;
                    case 11: t.a(w.pollFirstEntry()); break;
                    case 12: t.a(w.pollLastEntry()); break;
                    case 13: t.a(w.size() + "/" + w.isEmpty() + "/" + w); break;
                    case 14: t.a(w.keySet() + "|" + w.values() + "|" + w.entrySet()); break;
                    case 15: t.a(w.navigableKeySet().descendingSet() + "|" + w.descendingKeySet() + "|" + iter(w.descendingKeySet().descendingIterator())); break;
                    case 16: t.a(w.putIfAbsent(k, val)); break;
                    case 17: t.a(w.computeIfAbsent(k, x -> val == 0 ? null : (Object) (val * 7))); break;
                    case 18: t.a(w.merge(k, val + 1, (p, q) -> (Integer) p > 3 ? null : (Object) ((Integer) p + (Integer) q))); break;
                    case 19: t.a(w.compute(k, (x, o) -> o == null ? (val == 0 ? null : (Object) 1) : null)); break;
                    case 20: t.a(w.computeIfPresent(k, (x, o) -> (Integer) o > 2 ? null : (Object) ((Integer) o + 10))); break;
                    case 21: t.a(w.replace(k, val) + "," + w.replace(k, val, 5) + "," + w.getOrDefault(k, "d")); break;
                    case 22: {
                        Iterator<Map.Entry<Object, Object>> it = w.entrySet().iterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            Map.Entry<Object, Object> e = it.next();
                            b.append(e.getKey()).append(' ');
                            if (t.r(3) == 0) it.remove();
                            else if (t.r(3) == 0) e.setValue(9);
                        }
                        t.a(b + "" + w);
                        break;
                    }
                    case 23: {
                        Iterator<Object> it = t.b() ? w.navigableKeySet().descendingIterator() : w.keySet().iterator();
                        StringBuilder b = new StringBuilder();
                        int rem = t.r(4);
                        while (it.hasNext()) {
                            b.append(it.next()).append(' ');
                            if (t.r(3) == 0) {
                                it.remove();
                                if (rem-- == 0) it.remove();   // IllegalStateException
                            }
                        }
                        t.a(b + "" + base);
                        break;
                    }
                    case 24: {
                        // modification of the backing map during iteration of a view: CME
                        Iterator<Object> it = w.keySet().iterator();
                        if (it.hasNext()) {
                            Object x = it.next();
                            if (t.b()) base.put(x, 7); else base.remove(x);
                            t.a(x + ":" + it.hasNext());
                            it.next();
                        }
                        break;
                    }
                    case 25: t.a(w.equals(new TreeMap<>(base)) + "," + w.hashCode() + "," + w.equals(new HashMap<>(w)) + "," + new HashMap<>(w).equals(w)); break;
                    case 26: t.a(w.entrySet().contains(new AbstractMap.SimpleEntry<>(k, val)) + "," + w.entrySet().remove(new AbstractMap.SimpleEntry<>(k, val)) + "," + w.values().contains(val)); break;
                    case 27: t.a(w.keySet().remove(k) + "," + w.navigableKeySet().contains(k) + "," + w.values().remove(val)); break;
                    case 28: if (t.r(4) == 0) { w.clear(); t.a("clr" + base); } else t.a(w.containsValue(val)); break;
                    case 29: t.a(cmpInfo(w.comparator(), mode) + "," + cmpInfo(w.descendingMap().comparator(), mode) + "," + cmpInfo(w.navigableKeySet().comparator(), mode)); break;
                    case 30: {
                        NavigableSet<Object> ks = w.navigableKeySet();
                        t.a(ks.floor(k) + "," + ks.ceiling(k) + "," + ks.lower(k) + "," + ks.higher(k) + "," + ks.size());
                        break;
                    }
                    case 31: {
                        NavigableSet<Object> ks = t.b() ? w.navigableKeySet() : w.descendingKeySet();
                        Object a = key(t, mode);
                        NavigableSet<Object> sub;
                        switch (t.r(4)) {
                            case 0: sub = ks.subSet(a, t.b(), k, t.b()); break;
                            case 1: sub = ks.headSet(k, t.b()); break;
                            case 2: sub = ks.tailSet(k, t.b()); break;
                            default: sub = ks.descendingSet(); break;
                        }
                        t.a(sub + "/" + sub.size() + "/" + sub.pollFirst() + "/" + sub.pollLast() + "/" + base.size());
                        break;
                    }
                    case 32: t.a(w.navigableKeySet().first() + "," + w.navigableKeySet().last()); break;
                    case 33: {
                        Map<Object, Object> other = new HashMap<>();
                        other.put(k, 1);
                        w.putAll(other);
                        t.a(w);
                        break;
                    }
                    case 34: {
                        StringBuilder b = new StringBuilder();
                        w.forEach((x, y) -> b.append(x).append('=').append(y).append(' '));
                        w.replaceAll((x, y) -> (Integer) y + 1);
                        t.a(b + "" + w);
                        break;
                    }
                    case 35: t.a(w.remove(k, val) + "," + w.size()); break;
                    case 36: t.a(w.navigableKeySet() == w.navigableKeySet() && w.descendingMap() == w.descendingMap() && w.descendingMap().descendingMap() != w && w.keySet() == w.navigableKeySet()); break;
                    case 37: {
                        Iterator<Object> it = w.values().iterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            Object x = it.next();
                            b.append(x);
                            if ((Integer) x == 2) it.remove();
                        }
                        t.a(b + "" + base);
                        break;
                    }
                    case 38: t.a(base.descendingKeySet() == base.descendingKeySet() && base.descendingMap() == base.descendingMap()); break;
                    case 39: if (t.b()) t.a(w.computeIfAbsent(k, null)); else t.a(w.compute(k, null)); break;
                    case 40: {
                        TreeMap<Object, Object> c = new TreeMap<>(w.comparator() == null || mode != 1 ? base.comparator() : w.comparator());
                        c.putAll(w);
                        @SuppressWarnings("unchecked")
                        TreeMap<Object, Object> d = (TreeMap<Object, Object>) base.clone();
                        d.put(k, -1);
                        t.a(c + "/" + new TreeMap<>(w) + "/" + d + "/" + d.equals(base));
                        break;
                    }
                    default: {
                        Iterator<Object> it = w.keySet().iterator();
                        try {
                            for (;;) it.next();
                        } catch (NoSuchElementException ex) {
                            t.e(ex);
                        }
                        break;
                    }
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        try {
            t.a(base);
            t.a(v);
        } catch (RuntimeException ex) {
            t.e(ex);
        }
        return t.sb.toString();
    }

    static Object elem(Log t, int mode) {
        if (mode == 1) return t.r(30) == 0 ? (Object) 5 : "s".repeat(1 + t.r(6));
        if (t.r(30) == 0) return null;
        return t.r(30) - 5;
    }

    static int cmpLen(Object a, Object b) {
        if (!(a instanceof String) || !(b instanceof String)) throw new ClassCastException("cmpLen");
        return ((String) a).length() - ((String) b).length();
    }

    static NavigableSet<Object> sview(Log t, NavigableSet<Object> s, int mode) {
        Object a = elem(t, mode), b = elem(t, mode);
        switch (t.r(8)) {
            case 0: return s.subSet(a, t.b(), b, t.b());
            case 1: return s.headSet(a, t.b());
            case 2: return s.tailSet(a, t.b());
            case 3: return s.descendingSet();
            case 4: return (NavigableSet<Object>) s.subSet(a, b);
            case 5: return (NavigableSet<Object>) s.headSet(a);
            case 6: return (NavigableSet<Object>) s.tailSet(a);
            default: return s;
        }
    }

    public static String set(int seed) {
        Log t = new Log(seed);
        int mode = t.r(2);
        TreeSet<Object> base = mode == 1 ? new TreeSet<>(NavOps::cmpLen) : new TreeSet<>();
        for (int i = t.r(12); i > 0; i--) {
            try {
                base.add(elem(t, mode));
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        NavigableSet<Object> v = base;
        int n = 20 + t.r(50);
        for (int i = 0; i < n; i++) {
            Object k = elem(t, mode);
            try {
                switch (t.r(24)) {
                    case 0: case 1: v = sview(t, t.b() ? base : v, mode); t.a("V" + v); break;
                    case 2: case 3: t.a(v.add(k)); break;
                    case 4: t.a(base.add(k)); break;
                    case 5: t.a(v.remove(k) + "," + v.contains(k)); break;
                    case 6: t.a(v.first() + "," + v.last()); break;
                    case 7: t.a(v.lower(k) + "," + v.floor(k) + "," + v.ceiling(k) + "," + v.higher(k)); break;
                    case 8: t.a(v.pollFirst() + "," + v.pollLast()); break;
                    case 9: t.a(v + "/" + v.size() + "/" + v.isEmpty()); break;
                    case 10: t.a(iter(v.descendingIterator()) + iter(v.descendingSet().descendingIterator())); break;
                    case 11: t.a(v.addAll(Arrays.asList(k, elem(t, mode))) + "," + v.size()); break;
                    case 12: t.a(v.removeAll(Arrays.asList(k)) + "," + v.retainAll(new ArrayList<>(base))); break;
                    case 13: {
                        Iterator<Object> it = t.b() ? v.iterator() : v.descendingIterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            b.append(it.next()).append(' ');
                            if (t.r(3) == 0) it.remove();
                        }
                        t.a(b + "" + base);
                        break;
                    }
                    case 14: t.a(v.equals(new HashSet<>(v)) + "," + v.hashCode() + "," + new TreeSet<>(v).equals(v)); break;
                    case 15: {
                        @SuppressWarnings("unchecked")
                        TreeSet<Object> c = (TreeSet<Object>) ((TreeSet<Object>) v).clone();
                        if (k != null) c.add(k);   // (null: Collections.reverseOrder() of the model is STUCK)
                        t.a(c + "," + cmpInfo(c, mode) + "," + v);
                        break;
                    }
                    case 16: t.a(new TreeSet<>((SortedSet<Object>) v) + "," + Arrays.toString(v.toArray()) + "," + Arrays.toString(v.toArray(new Object[0]))); break;
                    case 17: {
                        TreeSet<Object> c = new TreeSet<>(base.comparator());
                        t.a(c.addAll(v) + "," + c + "," + c.addAll(base) + "," + c);
                        break;
                    }
                    case 18: {
                        Iterator<Object> it = v.iterator();
                        if (it.hasNext()) {
                            it.next();
                            base.add(k);
                            it.next();
                        }
                        t.a(v);
                        break;
                    }
                    case 19: t.a(cmpInfo(v, mode) + "," + cmpInfo(v.descendingSet(), mode)); break;
                    case 20: { v.clear(); t.a(base); break; }
                    case 21: t.a(v.removeIf(x -> x == null || x.hashCode() % 3 == 0) + "," + base); break;
                    default: t.a(v.subSet(k, true, k, true) + "," + v.headSet(k) + "," + v.tailSet(k, false)); break;
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        try {
            t.a(base);
            t.a(v);
        } catch (RuntimeException ex) {
            t.e(ex);
        }
        return t.sb.toString();
    }

    static String cmpInfo(SortedSet<Object> s, int mode) {
        Comparator<? super Object> c = s.comparator();
        if (c == null) return "natural";
        if (mode == 1) return "c" + Integer.signum(c.compare("s", "ss"));
        return "c" + Integer.signum(c.compare(1, 2));
    }

    /** Typical uses: ranges of a schedule, top-k, windows, ordered events. */
    public static String common(int seed) {
        Log t = new Log(seed);
        StringBuilder b = new StringBuilder();
        TreeMap<Integer, String> m = new TreeMap<>();
        for (int i = 0; i < 12 + t.r(10); i++) m.put(t.r(100), "v" + i);
        int lo = t.r(50), hi = lo + t.r(50);
        b.append(m.subMap(lo, hi)).append('|').append(m.headMap(lo)).append('|').append(m.tailMap(hi, false)).append('|');
        b.append(m.descendingMap()).append('|').append(m.descendingKeySet()).append('|');
        SortedMap<Integer, String> window = m.subMap(lo, hi);
        window.keySet().removeIf(k -> k % 2 == 0);
        b.append(m).append('|').append(window.size()).append('|');
        try {
            window.put(hi + 1, "x");
        } catch (IllegalArgumentException e) {
            b.append(e.getMessage()).append('|');
        }
        try {
            m.subMap(hi + 1, lo);
        } catch (IllegalArgumentException e) {
            b.append(e.getMessage()).append('|');
        }
        NavigableMap<Integer, String> d = m.descendingMap().headMap(lo, true);
        b.append(d).append(d.firstKey()).append('|');
        for (Map.Entry<Integer, String> e : m.tailMap(lo).entrySet()) {
            if (e.getKey() > hi) break;
            b.append(e.getKey()).append(',');
        }
        TreeSet<String> words = new TreeSet<>(Arrays.asList("pear", "apple", "fig", "kiwi", "banana", "cherry", "date"));
        b.append(words.headSet("date")).append(words.tailSet("fig", false)).append(words.subSet("b", "e")).append(words.descendingSet());
        NavigableSet<String> top = words.descendingSet().headSet("cherry", true);
        b.append(top).append(top.first()).append(top.pollFirst()).append(words);
        Iterator<String> it = words.descendingIterator();
        while (it.hasNext()) if (it.next().length() == 4) it.remove();
        b.append(words);
        TreeSet<Integer> nums = new TreeSet<>();
        for (int i = 0; i < 20; i++) nums.add(t.r(60));
        NavigableSet<Integer> mid = nums.subSet(10, true, 40, false);
        mid.add(10);
        try {
            mid.add(45);
        } catch (IllegalArgumentException e) {
            b.append(e.getMessage());
        }
        b.append(mid).append(mid.descendingSet()).append(mid.headSet(25)).append(nums.ceiling(30)).append(mid.size());
        @SuppressWarnings("unchecked")
        TreeSet<Integer> copy = (TreeSet<Integer>) ((TreeSet<Integer>) nums.descendingSet()).clone();
        copy.add(-1);
        b.append(copy).append(copy.first());
        return b.toString();
    }
}

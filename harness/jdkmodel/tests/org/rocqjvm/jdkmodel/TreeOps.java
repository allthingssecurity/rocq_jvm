package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of TreeMap / TreeSet (natural order and comparators, navigation, views,
 *  iterators with remove, fail-fast iteration, null and type errors). */
public final class TreeOps {
    private TreeOps() {
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
            sb.append('!').append(t.getClass().getSimpleName()).append(';');
        }
    }

    static Object key(Log t, int mode) {
        if (mode == 2) return "k" + t.r(30);
        if (mode == 3 && t.r(15) == 0) return null;
        return t.r(40) - 10;
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    static TreeMap<Object, Object> make(Log t, int mode) {
        if (mode == 1) return new TreeMap<>((a, b) -> Integer.compare((Integer) b, (Integer) a));   // descending
        if (mode == 3) return new TreeMap<>((a, b) -> a == null ? (b == null ? 0 : -1) : b == null ? 1 : ((Integer) a).compareTo((Integer) b));
        return new TreeMap<>();
    }

    public static String map(int seed) {
        Log t = new Log(seed);
        int mode = t.r(4);
        TreeMap<Object, Object> m = make(t, mode);
        int n = 20 + t.r(80);
        for (int i = 0; i < n; i++) {
            Object k = key(t, mode);
            Integer v = t.r(6);
            try {
                switch (t.r(26)) {
                    case 0: case 1: case 2: case 3: t.a(m.put(k, v)); break;
                    case 4: t.a(m.get(k)); break;
                    case 5: t.a(m.remove(k)); break;
                    case 6: t.a(m.containsKey(k) + "," + m.containsValue(v)); break;
                    case 7: t.a(m.firstKey() + "," + m.lastKey()); break;
                    case 8: t.a(m.firstEntry() + "," + m.lastEntry()); break;
                    case 9: t.a(m.floorKey(k) + "," + m.ceilingKey(k) + "," + m.lowerKey(k) + "," + m.higherKey(k)); break;
                    case 10: t.a(m.floorEntry(k) + "," + m.higherEntry(k)); break;
                    case 11: t.a(m.pollFirstEntry()); break;
                    case 12: t.a(m.pollLastEntry()); break;
                    case 13: t.a(m); break;
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
                            else if (t.r(3) == 0) e.setValue(9);
                        }
                        t.a(m);
                        break;
                    }
                    case 21: {
                        Iterator<Object> it = m.navigableKeySet().descendingIterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            Object x = it.next();
                            b.append(x).append(' ');
                            if (t.r(4) == 0) it.remove();
                        }
                        t.a(b + "" + m.size());
                        break;
                    }
                    case 22: {
                        for (Object x : m.keySet()) if (t.r(3) == 0) m.put(x, 0);   // value change: no CME
                        for (Object x : m.keySet()) m.remove(x);                     // CME after the first
                        break;
                    }
                    case 23: t.a(m.equals(new HashMap<>(m)) + "," + m.hashCode() + "," + new TreeMap<>(m).equals(m)); break;
                    case 24: { Map.Entry<Object, Object> e = m.firstEntry(); if (e != null) e.setValue(1); break; }
                    default: t.a(m.size() + "/" + m.isEmpty()); if (t.r(8) == 0) m.clear(); break;
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(m);
        return t.sb.toString();
    }

    public static String set(int seed) {
        Log t = new Log(seed);
        int mode = t.r(3);
        TreeSet<Object> s = (mode == 1) ? new TreeSet<>((a, b) -> ((String) a).length() - ((String) b).length())
                                         : new TreeSet<>();
        int n = 20 + t.r(60);
        for (int i = 0; i < n; i++) {
            Object k = (mode == 0) ? (Object) (t.r(30) - 5) : "s".repeat(1 + t.r(5)) + t.r(3);
            try {
                switch (t.r(16)) {
                    case 0: case 1: case 2: t.a(s.add(k)); break;
                    case 3: t.a(s.remove(k)); break;
                    case 4: t.a(s.contains(k)); break;
                    case 5: t.a(s.first() + "," + s.last()); break;
                    case 6: t.a(s.lower(k) + "," + s.floor(k) + "," + s.ceiling(k) + "," + s.higher(k)); break;
                    case 7: t.a(s.pollFirst() + "," + s.pollLast()); break;
                    case 8: t.a(s); break;
                    case 9: t.a(s.addAll(Arrays.asList(k, k)) + "," + s.size()); break;
                    case 10: t.a(s.removeAll(Arrays.asList(k)) + "," + s.retainAll(new ArrayList<>(s))); break;
                    case 11: { Iterator<Object> it = s.iterator(); if (it.hasNext()) { it.next(); it.remove(); } try { it.remove(); } catch (IllegalStateException e) { t.e(e); } break; }
                    case 12: t.a(s.equals(new HashSet<>(s)) + "," + s.hashCode()); break;
                    case 13: t.a(new TreeSet<>(s) + "," + Arrays.toString(s.toArray())); break;
                    case 14: if (mode == 0) s.add("str"); else s.add(3); break;   // ClassCastException
                    default: if (mode == 0) s.add(null); else t.a(s.isEmpty()); break;
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(s);
        return t.sb.toString();
    }

    /** A subclass overriding navigation, as Camel's stream resequencer Sequence does. */
    static final class Seq extends TreeSet<Integer> {
        public Integer higher(Integer e) {
            return super.higher(e) == null ? null : super.higher(e) + 0;
        }
    }

    public static String subclass(int seed) {
        Log t = new Log(seed);
        Seq s = new Seq();
        int n = 5 + t.r(30);
        for (int i = 0; i < n; i++) s.add(t.r(50));
        StringBuilder b = new StringBuilder();
        Integer x = s.isEmpty() ? null : s.first();
        while (x != null) {
            b.append(x).append(',');
            x = s.higher(x);
        }
        return b + "|" + s.size() + "|" + s.lower(25) + "|" + s;
    }
}

package org.rocqjvm.jdkmodel;

import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

/** Differential tests of java.util.concurrent.ConcurrentHashMap (single thread): random
 *  operation sequences whose results, exceptions and iteration orders are logged as a String.
 *  Keys are Integers (bins chosen to collide, so that bins become trees and lists again and
 *  the table resizes) and Strings with equal hash codes ("Aa" / "BB" combinations). */
public final class ChmOps {
    private ChmOps() {
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

        public String toString() {
            return sb.toString();
        }
    }

    /** An Integer key: few distinct low bits (so that bins collide) or any value. */
    static Integer key(Log t, int mode) {
        switch (mode) {
            case 0: return t.r(40);
            case 1: return (t.r(24) << 7) | 3;          // all in one bin of tables up to 128
            case 2: return (t.r(16) << 10) | t.r(2);    // two bins, long chains, trees
            default: return t.r(1 << 20) - (1 << 19);
        }
    }

    static String skey(Log t) {
        // 2^4 Strings of 4 blocks "Aa"/"BB": all have the same hash code
        StringBuilder b = new StringBuilder();
        int x = t.r(16);
        for (int i = 0; i < 4; i++) b.append(((x >> i) & 1) == 0 ? "Aa" : "BB");
        if (t.r(4) == 0) b.append((char) ('a' + t.r(3)));
        return b.toString();
    }

    static ConcurrentHashMap<Object, Object> make(Log t) {
        switch (t.r(6)) {
            case 0: return new ConcurrentHashMap<>();
            case 1: return new ConcurrentHashMap<>(t.r(200));
            case 2: return new ConcurrentHashMap<>(t.r(70), 0.25f + t.r(8) * 0.25f);
            case 3: return new ConcurrentHashMap<>(t.r(40), 0.75f, 1 + t.r(40));
            case 4: {
                HashMap<Object, Object> m = new HashMap<>();
                int n = t.r(30);
                for (int i = 0; i < n; i++) m.put(key(t, 0), i);
                return new ConcurrentHashMap<>(m);
            }
            default: return new ConcurrentHashMap<>(64);
        }
    }

    static void step(Log t, ConcurrentHashMap<Object, Object> m, int mode) {
        Object k = (mode == 4) ? skey(t) : key(t, mode);
        Integer v = t.r(5);
        try {
            switch (t.r(22)) {
                case 0: case 1: case 2: case 3: t.a(m.put(k, v)); break;
                case 4: t.a(m.putIfAbsent(k, v)); break;
                case 5: case 6: t.a(m.get(k)); break;
                case 7: case 8: t.a(m.remove(k)); break;
                case 9: t.a(m.remove(k, v)); break;
                case 10: t.a(m.replace(k, v)); break;
                case 11: t.a(m.replace(k, v, t.r(5))); break;
                case 12: t.a(m.containsKey(k)); break;
                case 13: t.a(m.containsValue(v)); break;
                case 14: t.a(m.getOrDefault(k, -1)); break;
                case 15: t.a(m.size() + "/" + m.mappingCount() + "/" + m.isEmpty()); break;
                case 16: t.a(m); break;
                case 17: t.a(m.keySet()); break;
                case 18: t.a(m.hashCode()); break;
                case 19: if (t.r(10) == 0) { m.clear(); t.a("clr"); } else t.a(m.values()); break;
                case 20: {
                    Map<Object, Object> o = new HashMap<>();
                    int n = t.r(6);
                    for (int i = 0; i < n; i++) o.put((mode == 4) ? skey(t) : key(t, mode), i);
                    m.putAll(o);
                    t.a("pa" + m.size());
                    break;
                }
                default: t.a(m.equals(new HashMap<>(m)) + "," + new HashMap<>(m).equals(m) + "," + m.equals(new ConcurrentHashMap<>(m))); break;
            }
        } catch (RuntimeException ex) {
            t.e(ex);
        }
    }

    /** Random operations on Integer keys; mode chooses the key distribution. */
    public static String ops(int seed) {
        Log t = new Log(seed);
        int mode = t.r(4);
        ConcurrentHashMap<Object, Object> m = make(t);
        int n = 20 + t.r(120);
        for (int i = 0; i < n; i++) step(t, m, mode);
        t.a(m);
        return t.toString();
    }

    /** Colliding keys: long chains, tree bins (Integer and String keys), removal back to lists. */
    public static String trees(int seed) {
        Log t = new Log(seed);
        int mode = 1 + t.r(2);
        if (t.r(3) == 0) mode = 4;
        ConcurrentHashMap<Object, Object> m = (t.r(2) == 0) ? new ConcurrentHashMap<>(64) : new ConcurrentHashMap<>();
        int n = 30 + t.r(150);
        for (int i = 0; i < n; i++) {
            if (t.r(3) == 0) {
                Object k = (mode == 4) ? skey(t) : key(t, mode);
                try {
                    t.a(m.remove(k));
                } catch (RuntimeException ex) {
                    t.e(ex);
                }
            } else {
                step(t, m, mode);
            }
        }
        t.a(m);
        return t.toString();
    }

    /** computeIfAbsent / computeIfPresent / compute / merge, with functions that return null. */
    public static String compute(int seed) {
        Log t = new Log(seed);
        int mode = t.r(5);
        ConcurrentHashMap<Object, Object> m = make(t);
        int n = 20 + t.r(120);
        for (int i = 0; i < n; i++) {
            Object k = (mode == 4) ? skey(t) : key(t, mode);
            int c = t.r(5);
            try {
                switch (t.r(6)) {
                    case 0: t.a(m.computeIfAbsent(k, x -> c == 0 ? null : (Object) (c * 10))); break;
                    case 1: t.a(m.computeIfPresent(k, (x, o) -> c == 0 ? null : (Object) ((Integer) o + c))); break;
                    case 2: t.a(m.compute(k, (x, o) -> c == 0 ? null : (Object) (o == null ? -c : (Integer) o * 2))); break;
                    case 3: t.a(m.merge(k, c + 1, (a, b) -> c == 1 ? null : (Object) ((Integer) a + (Integer) b))); break;
                    case 4: step(t, m, mode); break;
                    default: {
                        int d = t.r(3);
                        m.replaceAll((x, o) -> (Object) ((Integer) o + d));
                        t.a("ra");
                        break;
                    }
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(m);
        return t.toString();
    }

    /** A mapping function that changes the map: "Recursive update" or a successful nested call. */
    public static String recursive(int seed) {
        Log t = new Log(seed);
        ConcurrentHashMap<Object, Object> m = new ConcurrentHashMap<>(t.r(3) == 0 ? 2 : 16);
        int pre = t.r(6);
        for (int i = 0; i < pre; i++) m.put(key(t, 0), i);
        int n = 1 + t.r(6);
        for (int i = 0; i < n; i++) {
            Object k = key(t, 0);
            Object k2 = (t.r(2) == 0) ? (Object) ((Integer) k + 16 * (1 + t.r(3))) : key(t, 0);
            int w = t.r(4);
            try {
                Object r;
                if (w == 0) r = m.computeIfAbsent(k, x -> { m.put(k2, 1); return 2; });
                else if (w == 1) r = m.compute(k, (x, o) -> { m.remove(k2); return 3; });
                else if (w == 2) r = m.computeIfPresent(k, (x, o) -> { m.putIfAbsent(k2, 4); return 5; });
                else r = m.merge(k, 6, (a, b) -> { m.computeIfAbsent(k2, z -> 7); return 8; });
                t.a(r);
            } catch (RuntimeException ex) {
                t.e(ex);
            }
            t.a(m);
        }
        return t.toString();
    }

    /** Key set, values, entry set: iterators with remove, view operations, entry setValue,
     *  keySet(mapped value), newKeySet, Enumerations. */
    public static String views(int seed) {
        Log t = new Log(seed);
        int mode = t.r(5);
        ConcurrentHashMap<Object, Object> m = make(t);
        int pre = t.r(40);
        for (int i = 0; i < pre; i++) step(t, m, mode);
        int n = 10 + t.r(40);
        for (int i = 0; i < n; i++) {
            Object k = (mode == 4) ? skey(t) : key(t, mode);
            try {
                switch (t.r(18)) {
                    case 0: {
                        Iterator<Object> it = m.keySet().iterator();
                        int c = 0;
                        while (it.hasNext()) {
                            Object x = it.next();
                            if (t.r(3) == 0) { it.remove(); c++; }
                            t.a(x);
                        }
                        t.a("rmk" + c);
                        try { it.next(); } catch (NoSuchElementException ex) { t.e(ex); }
                        break;
                    }
                    case 1: {
                        Iterator<Map.Entry<Object, Object>> it = m.entrySet().iterator();
                        while (it.hasNext()) {
                            Map.Entry<Object, Object> e = it.next();
                            if (t.r(4) == 0) t.a(e.setValue(9));
                            t.a(e + "#" + e.hashCode() + e.equals(new AbstractMap.SimpleEntry<>(e.getKey(), e.getValue())));
                        }
                        break;
                    }
                    case 2: {
                        Iterator<Object> it = m.values().iterator();
                        try { it.remove(); } catch (IllegalStateException ex) { t.e(ex); }
                        if (it.hasNext()) { t.a(it.next()); it.remove(); try { it.remove(); } catch (IllegalStateException ex) { t.e(ex); } }
                        break;
                    }
                    case 3: t.a(m.keySet().contains(k) + "," + m.keySet().remove(k)); break;
                    case 4: t.a(m.values().contains(t.r(5)) + "," + m.values().remove(t.r(5))); break;
                    case 5: t.a(m.entrySet().contains(new AbstractMap.SimpleEntry<>(k, t.r(5))) + "," + m.entrySet().remove(new AbstractMap.SimpleEntry<>(k, t.r(5)))); break;
                    case 6: t.a(m.keySet().removeAll(Arrays.asList(k, key(t, mode)))); break;
                    case 7: t.a(m.values().removeAll(Arrays.asList(0, 1))); break;
                    case 8: t.a(m.keySet().retainAll(new HashSet<>(Arrays.asList(key(t, mode), key(t, mode), k)))); break;
                    case 9: t.a(Arrays.toString(m.keySet().toArray()) + Arrays.toString(m.values().toArray(new Object[2]))); break;
                    case 10: t.a(m.entrySet() + "|" + m.entrySet().hashCode() + "|" + m.keySet().hashCode()); break;
                    case 11: {
                        Set<Object> ks = m.keySet(42);
                        t.a(ks.add(k) + "," + ks.addAll(Arrays.asList(key(t, mode))) + "," + m.get(k));
                        break;
                    }
                    case 12: m.keySet().add(k); break;
                    case 13: t.a(m.entrySet().add(new AbstractMap.SimpleEntry<>(k, 3)) + "," + m.get(k)); break;
                    case 14: {
                        StringBuilder b = new StringBuilder();
                        for (Enumeration<Object> e = m.keys(); e.hasMoreElements(); ) b.append(e.nextElement()).append(',');
                        for (Enumeration<Object> e = m.elements(); e.hasMoreElements(); ) b.append(e.nextElement()).append(',');
                        t.a(b);
                        break;
                    }
                    case 15: {
                        Set<Object> s = ConcurrentHashMap.newKeySet(t.r(10));
                        s.add(k);
                        s.addAll(m.keySet());
                        t.a(s + "" + s.equals(m.keySet()) + m.keySet().equals(s) + s.size());
                        break;
                    }
                    case 16: t.a(m.keySet().containsAll(Arrays.asList(k)) + "," + m.keySet().isEmpty() + m.values().size() + m.keySet().getMappedValue()); break;
                    default: {
                        StringBuilder b = new StringBuilder();
                        m.forEach((x, y) -> b.append(x).append('=').append(y).append(' '));
                        m.keySet().forEach(x -> b.append(x));
                        m.values().forEach(x -> b.append(x));
                        m.entrySet().forEach(x -> b.append(x));
                        t.a(b);
                        break;
                    }
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(m);
        return t.toString();
    }

    /** Null keys/values/functions, bad constructor arguments, a map holding itself. */
    public static String errors(int seed) {
        Log t = new Log(seed);
        ConcurrentHashMap<Object, Object> m = new ConcurrentHashMap<>();
        m.put(1, 2);
        int n = 5 + t.r(10);
        for (int i = 0; i < n; i++) {
            try {
                switch (t.r(20)) {
                    case 0: m.put(null, 1); break;
                    case 1: m.put(1, null); break;
                    case 2: t.a(m.get(null)); break;
                    case 3: t.a(m.containsKey(null)); break;
                    case 4: t.a(m.containsValue(null)); break;
                    case 5: t.a(m.remove(null)); break;
                    case 6: t.a(m.remove(1, null)); break;
                    case 7: t.a(m.remove(null, 1)); break;
                    case 8: t.a(m.replace(1, null)); break;
                    case 9: t.a(m.replace(1, 2, null)); break;
                    case 10: t.a(m.computeIfAbsent(null, x -> 1)); break;
                    case 11: t.a(m.computeIfAbsent(2, null)); break;
                    case 12: t.a(m.merge(1, null, (a, b) -> a)); break;
                    case 13: t.a(new ConcurrentHashMap<>(-1)); break;
                    case 14: t.a(new ConcurrentHashMap<>(4, 0.0f)); break;
                    case 15: t.a(new ConcurrentHashMap<>(4, 0.75f, 0)); break;
                    case 16: t.a(m.keySet(null)); break;
                    case 17: { ConcurrentHashMap<Object, Object> s = new ConcurrentHashMap<>(); s.put(s, s); s.put(1, s); t.a(s); t.a(s.keySet()); break; }
                    case 18: t.a(m.getOrDefault(null, 1)); break;
                    default: t.a(m.putIfAbsent(1, 3) + "," + m.putIfAbsent(5, 6) + "," + m); break;
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        return t.toString();
    }

    /** Through the ConcurrentMap interface (invokeinterface on the model's interface). */
    public static String iface(int seed) {
        Log t = new Log(seed);
        ConcurrentMap<Object, Object> m = new ConcurrentHashMap<>();
        int n = 10 + t.r(60);
        for (int i = 0; i < n; i++) {
            Object k = key(t, 0);
            int c = t.r(4);
            switch (t.r(6)) {
                case 0: t.a(m.putIfAbsent(k, c)); break;
                case 1: t.a(m.merge(k, c + 1, (a, b) -> (Integer) a + (Integer) b)); break;
                case 2: t.a(m.computeIfAbsent(k, x -> (Integer) x * 2)); break;
                case 3: t.a(m.replace(k, c, c + 1)); break;
                case 4: t.a(m.getOrDefault(k, "d")); break;
                default: Map<Object, Object> mm = m; t.a(mm.remove(k)); break;
            }
        }
        t.a(m);
        return t.toString();
    }
}

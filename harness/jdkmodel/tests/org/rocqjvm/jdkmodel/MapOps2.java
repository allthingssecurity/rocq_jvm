package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of IdentityHashMap (identity semantics, resize, removal with probe-sequence
 *  repair, iterator removal; results that do not depend on identity hash codes only), WeakHashMap
 *  (no GC: a plain hash map with the JDK's table and iteration order), Hashtable (bucket order,
 *  Enumerations, synchronized views, null checks and their messages, compute family, self
 *  references) and Properties (defaults, property names, the ConcurrentHashMap-backed map).
 *  Exceptions are printed as class simple name ':' message. */
public final class MapOps2 {
    private MapOps2() {
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

    /** A key with a chosen hash code and equality by id (collisions on demand). */
    static final class Key {
        final int id;
        final int h;

        Key(int id, int h) {
            this.id = id;
            this.h = h;
        }

        public int hashCode() {
            return h;
        }

        public boolean equals(Object o) {
            return o instanceof Key && ((Key) o).id == id;
        }

        public String toString() {
            return "K" + id;
        }
    }

    /** An object without equals/hashCode overrides (identity), with a stable name. */
    static final class Obj {
        final String name;

        Obj(String name) {
            this.name = name;
        }

        public String toString() {
            return name;
        }
    }

    // ---- IdentityHashMap ----

    static String name(Object o) {
        if (o == null) return "null";
        if (o instanceof String) return "s" + o;
        return String.valueOf(o);
    }

    /** Sorted names of the elements of c (order-independent). */
    static String names(Collection<?> c) {
        List<String> l = new ArrayList<>();
        for (Object o : c) l.add(name(o));
        Collections.sort(l);
        return l.toString();
    }

    static String entryNames(Map<?, ?> m) {
        List<String> l = new ArrayList<>();
        for (Map.Entry<?, ?> e : m.entrySet()) l.add(name(e.getKey()) + "=" + name(e.getValue()));
        Collections.sort(l);
        return l.toString();
    }

    static List<Object> firstHalf(Object[] keys) {
        List<Object> l = new ArrayList<>();
        for (int i = 0; i < keys.length / 2; i++) l.add(keys[i]);
        return l;
    }

    public static String identity(int seed) {
        Log t = new Log(seed);
        int nk = 6 + t.r(40);
        Object[] keys = new Object[nk];
        String[] base = {"a", "b", "c"};
        for (int i = 0; i < nk; i++) {
            switch (i % 5) {
                case 0: keys[i] = base[i % 3]; break;                     // literal (shared)
                case 1: keys[i] = new String(base[i % 3]); break;         // equal, not identical
                case 2: keys[i] = null; break;
                default: keys[i] = new Obj("o" + i); break;
            }
        }
        Object[] vals = {new Obj("v0"), new Obj("v1"), "x", new String("x"), null};
        IdentityHashMap<Object, Object> m;
        try {
            switch (t.r(4)) {
                case 0: m = new IdentityHashMap<>(t.r(20) - 2); break;
                case 1: {
                    HashMap<Object, Object> h = new HashMap<>();
                    for (int i = t.r(10); i > 0; i--) h.put(keys[t.r(nk)], vals[t.r(5)]);
                    m = new IdentityHashMap<>(h);
                    break;
                }
                default: m = new IdentityHashMap<>(); break;
            }
        } catch (RuntimeException ex) {
            t.e(ex);
            m = new IdentityHashMap<>();
        }
        int n = 20 + t.r(45);
        for (int i = 0; i < n; i++) {
            Object k = keys[t.r(nk)];
            Object v = vals[t.r(5)];
            try {
                switch (t.r(24)) {
                    case 0: case 1: case 2: case 3: case 4: t.a(name(m.put(k, v))); break;
                    case 5: t.a(name(m.get(k)) + "," + m.containsKey(k) + "," + m.containsValue(v)); break;
                    case 6: case 7: t.a(name(m.remove(k))); break;
                    case 8: t.a(m.remove(k, v) + "," + m.replace(k, v, vals[0]) + "," + name(m.replace(k, v))); break;
                    case 9: t.a(name(m.putIfAbsent(k, v)) + "," + name(m.getOrDefault(k, "d"))); break;
                    case 10: t.a(m.size() + "," + m.isEmpty()); break;
                    case 11: t.a(names(m.keySet()) + names(m.values())); break;
                    case 12: t.a(entryNames(m)); break;
                    case 13: {
                        Iterator<Object> it = m.keySet().iterator();
                        List<String> seen = new ArrayList<>();
                        while (it.hasNext()) {
                            Object x = it.next();
                            seen.add(name(x));
                            if (name(x).length() % 2 == 0 || x == null) it.remove();
                        }
                        Collections.sort(seen);
                        t.a(seen + "" + names(m.keySet()) + m.size());
                        break;
                    }
                    case 14: {
                        Iterator<Map.Entry<Object, Object>> it = m.entrySet().iterator();
                        List<String> seen = new ArrayList<>();
                        int salt = t.r(6);
                        while (it.hasNext()) {
                            Map.Entry<Object, Object> e = it.next();
                            seen.add(name(e.getKey()));
                            int d = Math.floorMod(name(e.getKey()).hashCode() + salt, 6);   // by key, not by position
                            if (d < 2) {
                                it.remove();
                                try {
                                    e.getValue();
                                } catch (IllegalStateException ex) {
                                    seen.add(ex.getMessage());
                                }
                            } else if (d == 2) {
                                e.setValue(vals[1]);
                            }
                        }
                        Collections.sort(seen);
                        t.a(seen + entryNames(m));
                        break;
                    }
                    case 15: {
                        Iterator<Object> it = m.values().iterator();
                        if (it.hasNext()) {
                            it.next();
                            if (t.b()) m.put(new Obj("new"), v); else m.put(k, v);
                            it.hasNext();   // (the answer depends on the identity hash order)
                            it.next();
                        }
                        break;
                    }
                    case 16: {
                        @SuppressWarnings("unchecked")
                        IdentityHashMap<Object, Object> c = (IdentityHashMap<Object, Object>) m.clone();
                        c.put(k, "cl");
                        t.a(c.equals(m) + "," + m.equals(c) + "," + entryNames(c) + "," + new IdentityHashMap<>(m).equals(m));
                        break;
                    }
                    case 17: {
                        HashMap<Object, Object> h = new HashMap<>();
                        for (Object x : keys) if (m.containsKey(x) && !h.containsKey(x)) h.put(x, m.get(x));
                        t.a(m.equals(h) + "," + h.equals(m) + "," + h.size());
                        break;
                    }
                    case 18: t.a(m.keySet().contains(k) + "," + m.entrySet().contains(new AbstractMap.SimpleEntry<>(k, v)) + "," + m.entrySet().remove(new AbstractMap.SimpleEntry<>(k, v)) + "," + m.values().contains(v)); break;   // (values().remove: the first in identity-hash order)
                    case 19: t.a(m.keySet().removeAll(Arrays.asList(k, keys[0])) + "," + m.size() + "," + m.keySet().retainAll(firstHalf(keys)) + "," + m.size()); break;
                    case 20: t.a(m.keySet().toArray().length + "," + m.values().toArray(new Object[0]).length + "," + m.entrySet().toArray(new Object[50]).length); break;
                    case 21: {
                        int[] cnt = {0};
                        m.forEach((x, y) -> cnt[0]++);
                        m.replaceAll((x, y) -> y == null ? vals[0] : y);
                        t.a(cnt[0] + entryNames(m));
                        break;
                    }
                    case 22: {
                        Map<Object, Object> other = new HashMap<>();
                        for (int j = t.r(20); j > 0; j--) other.put(new Obj("p" + j), v);
                        m.putAll(other);
                        t.a(m.size());
                        break;
                    }
                    default: if (t.r(5) == 0) { m.clear(); t.a("clr" + m.size()); } else t.a(m.containsKey(new String("a")) + "," + m.containsKey("a")); break;
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(entryNames(m));
        t.a(m.size() == m.entrySet().size() && m.size() == m.keySet().size());
        return t.sb.toString();
    }

    // ---- WeakHashMap ----

    /** Strong references to every key given to a WeakHashMap: HotSpot's collector would
     *  otherwise clear entries at unpredictable times (the model never clears them). */
    static final List<Object> HOLD = new ArrayList<>();

    static <T> T hold(T k) {
        HOLD.add(k);
        return k;
    }

    static Object wkey(Log t, int mode) {
        switch (mode) {
            case 0: return t.r(80) - 20;
            case 1: return hold("w" + t.r(40));
            case 2: { int id = t.r(30); return hold(new Key(id, id % 10)); }   // collisions (3 per hash: no HashMap tree bins)
            default: return t.r(12) == 0 ? null : (Object) (t.r(50) - 5);
        }
    }

    public static String weak(int seed) {
        Log t = new Log(seed);
        HOLD.clear();
        int mode = t.r(4);
        boolean ordered = mode != 3;   // a null key's bucket depends on an identity hash code
        WeakHashMap<Object, Object> m;
        try {
            switch (t.r(5)) {
                case 0: m = new WeakHashMap<>(t.r(40) - 3); break;
                case 1: {
                    int lf = t.r(5);
                    m = new WeakHashMap<>(t.r(20), lf == 0 ? -1f : lf == 1 ? 0.5f : lf == 2 ? 2f : lf == 3 ? Float.NaN : 0f);
                    break;
                }
                case 2: {
                    Map<Object, Object> h = new LinkedHashMap<>();
                    for (int i = t.r(20); i > 0; i--) h.put(wkey(t, mode), t.r(9));
                    m = new WeakHashMap<>(h);
                    break;
                }
                default: m = new WeakHashMap<>(); break;
            }
        } catch (RuntimeException ex) {
            t.e(ex);
            m = new WeakHashMap<>();
        }
        int n = 20 + t.r(50);
        for (int i = 0; i < n; i++) {
            Object k = wkey(t, mode);
            Integer v = t.r(7);
            try {
                switch (t.r(22)) {
                    case 0: case 1: case 2: case 3: case 4: t.a(m.put(k, v)); break;
                    case 5: t.a(m.get(k) + "," + m.containsKey(k) + "," + m.containsValue(v) + "," + m.containsValue(null)); break;
                    case 6: case 7: t.a(m.remove(k)); break;
                    case 8: t.a(m.size() + "," + m.isEmpty()); break;
                    case 9: t.a(ordered ? m.toString() : entryNames(m)); break;
                    case 10: t.a(ordered ? m.keySet() + "|" + m.values() : names(m.keySet()) + names(m.values())); break;
                    case 11: {
                        Iterator<Map.Entry<Object, Object>> it = m.entrySet().iterator();
                        StringBuilder b = new StringBuilder();
                        int cnt = 0;
                        int salt = t.r(6);
                        while (it.hasNext()) {
                            Map.Entry<Object, Object> e = it.next();
                            cnt++;
                            if (ordered) b.append(e).append(' ');
                            int d = Math.floorMod(name(e.getKey()).hashCode() + salt, 6);   // by key, not by position
                            if (d < 2) it.remove();
                            else if (d == 2) e.setValue(9);
                        }
                        t.a(b + "" + cnt + (ordered ? m.toString() : entryNames(m)));
                        break;
                    }
                    case 12: {
                        Iterator<Object> it = m.keySet().iterator();
                        if (it.hasNext()) {
                            it.next();
                            if (t.b()) m.put(k, v); else m.remove(k);
                            boolean hn = it.hasNext();
                            if (ordered) t.a(hn);
                            it.next();
                        }
                        break;
                    }
                    case 13: t.a(m.hashCode() + "," + m.equals(new HashMap<>(m)) + "," + new HashMap<>(m).equals(m)); break;
                    case 14: {
                        Map<Object, Object> other = new HashMap<>();
                        for (int j = t.r(20); j > 0; j--) other.put(wkey(t, mode), j);
                        m.putAll(other);
                        t.a(m.size() + (ordered ? m.toString() : ""));
                        break;
                    }
                    case 15: t.a(m.entrySet().contains(new AbstractMap.SimpleEntry<>(k, v)) + "," + m.entrySet().remove(new AbstractMap.SimpleEntry<>(k, v)) + "," + m.keySet().remove(k)); break;
                    case 16: t.a(m.computeIfAbsent(k, x -> v == 0 ? null : (Object) (v * 3)) + "," + m.merge(k, 1, (p, q) -> (Integer) p > 5 ? null : (Object) ((Integer) p + (Integer) q))); break;
                    case 17: {
                        int[] cnt = {0};
                        m.forEach((x, y) -> cnt[0] += (Integer) y);
                        m.replaceAll((x, y) -> (Integer) y + 1);
                        t.a(cnt[0] + (ordered ? m.toString() : ""));
                        break;
                    }
                    // values().remove(v) removes the first entry in iteration order: with a null key
                    // (mode 3) that order depends on the null key's identity hash code
                    case 18: t.a((ordered ? m.values().remove(v) + "," : "") + m.values().contains(v) + "," + m.size()); break;
                    case 19: t.a(m.entrySet().toArray().length + "," + (ordered ? Arrays.toString(m.entrySet().toArray(new Object[0])) : "")); break;
                    case 20: if (t.r(5) == 0) { m.clear(); t.a("clr" + m); } else t.a(m.getOrDefault(k, "d")); break;
                    default: { Map<Object, Object> h = new HashMap<>(); m.putAll(null); t.a(h); break; }
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(ordered ? m.toString() : entryNames(m));
        return t.sb.toString();
    }

    // ---- Hashtable ----

    static Object hkey(Log t, int mode) {
        if (t.r(20) == 0) return null;
        switch (mode) {
            case 0: return t.r(60) - 10;
            case 1: return "h" + t.r(40);
            default: { int id = t.r(30); return new Key(id, id % 5 * 11); }
        }
    }

    static String enumStr(Enumeration<?> e) {
        StringBuilder b = new StringBuilder("<");
        while (e.hasMoreElements()) b.append(e.nextElement()).append(' ');
        return b.append('>').toString();
    }

    public static String table(int seed) {
        Log t = new Log(seed);
        int mode = t.r(3);
        Hashtable<Object, Object> m;
        try {
            switch (t.r(5)) {
                case 0: m = new Hashtable<>(t.r(30) - 3); break;
                case 1: {
                    int lf = t.r(5);
                    m = new Hashtable<>(t.r(20), lf == 0 ? -1f : lf == 1 ? 0.5f : lf == 2 ? 3f : lf == 3 ? Float.NaN : -0.5f);
                    break;
                }
                case 2: {
                    Map<Object, Object> h = new TreeMap<>();
                    for (int i = t.r(20); i > 0; i--) {
                        Object k = hkey(t, 0);
                        if (k != null) h.put(k, t.r(9));
                    }
                    m = new Hashtable<>(h);
                    break;
                }
                default: m = new Hashtable<>(); break;
            }
        } catch (RuntimeException ex) {
            t.e(ex);
            m = new Hashtable<>();
        }
        int n = 20 + t.r(50);
        for (int i = 0; i < n; i++) {
            Object k = hkey(t, mode);
            Object v = t.r(15) == 0 ? null : (Object) t.r(7);
            try {
                switch (t.r(30)) {
                    case 0: case 1: case 2: case 3: case 4: t.a(m.put(k, v)); break;
                    case 5: t.a(m.get(k) + "," + m.containsKey(k)); break;
                    case 6: t.a(m.contains(v) + "," + m.containsValue(v)); break;
                    case 7: case 8: t.a(m.remove(k)); break;
                    case 9: t.a(m + "/" + m.size() + "/" + m.isEmpty()); break;
                    case 10: t.a(enumStr(m.keys()) + enumStr(m.elements())); break;
                    case 11: t.a(m.keySet() + "|" + m.values() + "|" + m.entrySet()); break;
                    case 12: {
                        Iterator<Map.Entry<Object, Object>> it = m.entrySet().iterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            Map.Entry<Object, Object> e = it.next();
                            b.append(e).append(' ');
                            if (t.r(3) == 0) {
                                it.remove();
                                if (t.r(5) == 0) it.remove();   // IllegalStateException
                            } else if (t.r(3) == 0) {
                                e.setValue(t.r(6) == 0 ? null : (Object) 9);
                            }
                        }
                        t.a(b + "" + m);
                        break;
                    }
                    case 13: {
                        Iterator<Object> it = t.b() ? m.keySet().iterator() : m.values().iterator();
                        if (it.hasNext()) {
                            it.next();
                            if (t.b()) m.put(t.r(100) + 100, 1); else m.put(it.hasNext() ? k : 0, 2);
                            t.a(it.hasNext());
                            it.next();
                        }
                        break;
                    }
                    case 14: {
                        Enumeration<Object> e = m.keys();
                        StringBuilder b = new StringBuilder();
                        if (e.hasMoreElements()) {
                            b.append(e.nextElement());
                            m.put(1000 + t.r(5), 3);   // Enumerations are not fail-fast
                            while (e.hasMoreElements()) b.append(',').append(e.nextElement());
                        }
                        t.a(b);
                        e.nextElement();
                        break;
                    }
                    case 15: t.a(m.hashCode() + "," + m.equals(new HashMap<>(m)) + "," + new HashMap<>(m).equals(m) + "," + m.equals(m.clone())); break;
                    case 16: {
                        @SuppressWarnings("unchecked")
                        Hashtable<Object, Object> c = (Hashtable<Object, Object>) m.clone();
                        c.put(-99, -1);
                        t.a(c + "/" + m + "/" + c.keySet());
                        break;
                    }
                    case 17: t.a(m.putIfAbsent(k, v) + "," + m.getOrDefault(k, "d")); break;
                    case 18: t.a(m.computeIfAbsent(k, x -> t.r(4) == 0 ? null : (Object) 5)); break;
                    case 19: t.a(m.computeIfPresent(k, (x, y) -> (Integer) y > 3 ? null : (Object) ((Integer) y + 1))); break;
                    case 20: t.a(m.compute(k, (x, y) -> y == null ? (t.b() ? null : (Object) 1) : (t.r(3) == 0 ? null : (Object) ((Integer) y * 2)))); break;
                    case 21: t.a(m.merge(k, v, (p, q) -> (Integer) p > 4 ? null : (Object) ((Integer) p + (Integer) q))); break;
                    case 22: t.a(m.replace(k, v) + "," + m.replace(k, 1, 6) + "," + m.remove(k, v)); break;
                    case 23: {
                        StringBuilder b = new StringBuilder();
                        m.forEach((x, y) -> b.append(x).append('=').append(y).append(' '));
                        m.replaceAll((x, y) -> (Integer) y > 5 ? null : (Object) ((Integer) y + 1));
                        t.a(b + "" + m);
                        break;
                    }
                    case 24: t.a(m.entrySet().contains(new AbstractMap.SimpleEntry<>(k, v)) + "," + m.entrySet().remove(new AbstractMap.SimpleEntry<>(k, v)) + "," + m.keySet().remove(k) + "," + m.keySet().contains(k)); break;
                    case 25: {
                        Map<Object, Object> other = new LinkedHashMap<>();
                        for (int j = t.r(25); j > 0; j--) other.put(hkey(t, mode), t.r(4) == 0 ? null : (Object) j);
                        m.putAll(other);
                        t.a(m);
                        break;
                    }
                    case 26: {
                        Hashtable<Object, Object> s = new Hashtable<>();
                        s.put(1, s);
                        s.put(s, 2);
                        s.put("k", m);
                        t.a(s.toString().length() + "," + s.hashCode() + "," + s.size());
                        break;
                    }
                    case 27: t.a(m.values().remove(v) + "," + m.values().removeIf(y -> (Integer) y == 3) + "," + m.keySet().removeAll(Arrays.asList(k, 1, 2)) + "," + m); break;
                    case 28: {
                        Iterator<Object> it = m.keys().asIterator();
                        if (it.hasNext()) {
                            it.next();
                            it.remove();
                        }
                        break;
                    }
                    default: if (t.r(5) == 0) { m.clear(); t.a("clr" + m + enumStr(m.keys())); } else t.a(m.keySet().equals(new HashSet<>(m.keySet())) + "," + m.entrySet().hashCode()); break;
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(m);
        return t.sb.toString();
    }

    // ---- Properties ----

    public static String props(int seed) {
        Log t = new Log(seed);
        Properties top = new Properties();
        Properties mid = new Properties(top);
        Properties p;
        try {
            p = t.r(4) == 0 ? new Properties(t.r(10) - 2) : new Properties(t.b() ? mid : top);
        } catch (RuntimeException ex) {
            t.e(ex);
            p = new Properties(mid);
        }
        Properties[] all = {p, mid, top};
        int n = 20 + t.r(45);
        for (int i = 0; i < n; i++) {
            Properties w = all[t.r(5) == 0 ? 1 + t.r(2) : 0];
            String k = t.r(25) == 0 ? null : "p" + t.r(20);
            String v = t.r(25) == 0 ? null : "v" + t.r(6);
            try {
                switch (t.r(26)) {
                    case 0: case 1: case 2: case 3: t.a(w.setProperty(k, v)); break;
                    case 4: t.a(p.getProperty(k) + "," + p.getProperty(k, "def") + "," + mid.getProperty(k)); break;
                    case 5: t.a(w.put(t.b() ? k : (Object) t.r(5), t.b() ? v : (Object) t.r(3))); break;
                    case 6: t.a(w.get(k) + "," + w.containsKey(k) + "," + w.contains(v) + "," + w.containsValue(v)); break;
                    case 7: t.a(w.remove(k)); break;
                    case 8: t.a(w + "/" + w.size() + "/" + w.isEmpty()); break;
                    case 9: t.a(p.stringPropertyNames() + "," + mid.stringPropertyNames()); break;
                    case 10: t.a(enumStr(p.propertyNames())); break;
                    case 11: t.a(enumStr(w.keys()) + enumStr(w.elements())); break;
                    case 12: t.a(w.keySet() + "|" + w.values() + "|" + w.entrySet()); break;
                    case 13: {
                        Iterator<Map.Entry<Object, Object>> it = w.entrySet().iterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            Map.Entry<Object, Object> e = it.next();
                            b.append(e).append(' ');
                            if (t.r(3) == 0) it.remove();
                            else if (t.r(3) == 0) e.setValue("set");
                        }
                        t.a(b + "" + w);
                        break;
                    }
                    case 14: t.a(w.equals(new HashMap<>(w)) + "," + w.hashCode() + "," + w.equals(w.clone()) + "," + p.equals(mid)); break;
                    case 15: {
                        Properties c = (Properties) w.clone();
                        c.setProperty("clone", "c");
                        t.a(c + "/" + w + "/" + c.getProperty(k));
                        break;
                    }
                    case 16: t.a(w.putIfAbsent(k, v) + "," + w.getOrDefault(k, "d") + "," + w.replace(k, "r") + "," + w.remove(k, "r")); break;
                    case 17: t.a(w.computeIfAbsent(k, x -> "c" + x) + "," + w.merge(k, "m", (a, b) -> a + "" + b) + "," + w.compute(k, (x, y) -> y == null ? null : y + "!")); break;
                    case 18: {
                        StringBuilder b = new StringBuilder();
                        w.forEach((x, y) -> b.append(x).append(' '));
                        w.replaceAll((x, y) -> y + "+");
                        t.a(b + "" + w);
                        break;
                    }
                    case 19: { Map<Object, Object> h = new HashMap<>(); h.put(k, v); w.putAll(h); t.a(w); break; }
                    case 20: t.a(w.keySet().remove(k) + "," + w.values().contains(v) + "," + w.entrySet().contains(new AbstractMap.SimpleEntry<>(k, v))); break;
                    case 21: if (t.r(4) == 0) { w.clear(); t.a("clr" + w); } else t.a(w.keySet().size()); break;
                    case 22: t.a(w.entrySet().add(new AbstractMap.SimpleEntry<>("x", "y"))); break;
                    case 23: t.a(w.propertyNames().hasMoreElements() + "," + w.stringPropertyNames().contains(k)); break;
                    default: t.a(w.computeIfPresent(k, (x, y) -> t.b() ? null : y + "?") + "," + w.replace(k, "a", "b")); break;
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(p);
        t.a(mid);
        t.a(top);
        return t.sb.toString();
    }

    /** Typical uses: identity-keyed visited sets, caches keyed by objects, legacy tables,
     *  configuration with defaults. */
    public static String common(int seed) {
        Log t = new Log(seed);
        StringBuilder out = new StringBuilder();
        // visited set of a graph walk keyed by identity
        Obj[] nodes = new Obj[20];
        for (int i = 0; i < nodes.length; i++) nodes[i] = new Obj("n" + i);
        IdentityHashMap<Obj, Integer> depth = new IdentityHashMap<>();
        Deque<Obj> work = new ArrayDeque<>();
        work.add(nodes[0]);
        depth.put(nodes[0], 0);
        while (!work.isEmpty()) {
            Obj x = work.poll();
            int d = depth.get(x);
            int id = Integer.parseInt(x.name.substring(1));
            for (int c : new int[] {(id * 3 + 1) % 20, (id + t.r(5)) % 20}) {
                if (!depth.containsKey(nodes[c])) {
                    depth.put(nodes[c], d + 1);
                    work.add(nodes[c]);
                }
            }
        }
        out.append(depth.size()).append(entryNames(depth)).append('|');
        IdentityHashMap<Object, Boolean> seen = new IdentityHashMap<>();
        String s1 = "same", s2 = new String("same");
        out.append(seen.put(s1, true)).append(seen.put(s2, true)).append(seen.put(s1, true)).append(seen.size()).append(seen.keySet().contains("same")).append('|');
        // cache
        WeakHashMap<String, Integer> cache = new WeakHashMap<>();
        HOLD.clear();
        for (int i = 0; i < 40; i++) cache.computeIfAbsent(hold("k" + t.r(25)), String::length);
        out.append(cache.size()).append(cache).append('|');
        // legacy table
        Hashtable<String, Integer> ht = new Hashtable<>();
        for (int i = 0; i < 25; i++) ht.merge("w" + t.r(12), 1, Integer::sum);
        out.append(ht).append(enumStr(ht.keys())).append(ht.hashCode()).append('|');
        // configuration
        Properties defaults = new Properties();
        defaults.setProperty("host", "localhost");
        defaults.setProperty("port", "8080");
        Properties conf = new Properties(defaults);
        conf.setProperty("port", "9" + t.r(1000));
        conf.setProperty("user", "u" + t.r(10));
        conf.put("retries", 3);
        out.append(conf.getProperty("host")).append(conf.getProperty("port")).append(conf.getProperty("retries", "none"))
            .append(conf.getProperty("missing", "dflt")).append(conf.stringPropertyNames()).append(enumStr(conf.propertyNames())).append(enumStr(defaults.propertyNames()))
            .append(conf).append(conf.size());
        return out.toString();
    }
}

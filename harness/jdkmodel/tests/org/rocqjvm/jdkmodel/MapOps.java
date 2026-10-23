package org.rocqjvm.jdkmodel;

import java.util.*;

/**
 * Differential tests of HashMap / LinkedHashMap: a seed drives a random sequence of operations
 * (every Map method that is modelled, the three views, their iterators, fail-fast behaviour);
 * every observable result (return values, iteration order, sizes, exception classes) is folded
 * into the int result, which must be the same on HotSpot (real java.util) and on the Rocq
 * machine (model classes).
 */
public final class MapOps {
    private MapOps() {
    }

    /** LRU cache in the style used by Camel: access order + removeEldestEntry. */
    static final class Lru extends LinkedHashMap<Object, Object> {
        final int max;

        Lru(int cap, int max, boolean accessOrder) {
            super(cap, 0.75f, accessOrder);
            this.max = max;
        }

        protected boolean removeEldestEntry(Map.Entry<Object, Object> eldest) {
            return size() > max;
        }
    }

    /** Key generator: family 0 = K with hash mode, 1 = Integer, 2 = String (Aa/BB),
     *  3 = Long with colliding hash codes; 3% null. */
    static Object key(T t, int fam, int mode, int range) {
        if (t.chance(3)) return null;
        switch (fam) {
            case 0: return t.key(mode, range);
            case 1: return t.intKey(mode % 5, range);
            case 2: return t.strKey(range);
            default: return t.longKey(range);
        }
    }

    static Object val(T t) {
        if (t.chance(5)) return null;
        return t.r(60) - 5;
    }

    static int iv(Object v) {
        return v == null ? 0 : (Integer) v;
    }

    /** Fold the iteration order of all three views. */
    static void foldViews(T t, Map<Object, Object> m) {
        for (Object k : m.keySet()) t.fo(k);
        for (Object v : m.values()) t.fo(v);
        for (Map.Entry<Object, Object> e : m.entrySet()) t.f(T.code(e));
        t.f(m.size());
    }

    static Map<Object, Object> newMap(T t, int kind) {
        switch (kind) {
            case 0: return new HashMap<>();
            case 1: return new HashMap<>(t.r(70));
            case 2: return new HashMap<>(t.r(20), t.chance(50) ? 0.5f : (t.chance(50) ? 1.0f : 3.0f));
            case 3: return new LinkedHashMap<>();
            case 4: return new LinkedHashMap<>(t.r(40), 0.75f, true);
            case 5: return new Lru(t.r(8), 3 + t.r(12), t.chance(50));
            default: return new LinkedHashMap<>(t.r(30));
        }
    }

    /** One random operation on m. */
    static void step(T t, Map<Object, Object> m, int fam, int mode, int range) {
        int op = t.r(34);
        try {
            switch (op) {
                case 0: case 1: case 2: case 3:
                    t.fo(m.put(key(t, fam, mode, range), val(t)));
                    break;
                case 4: case 5:
                    t.fo(m.get(key(t, fam, mode, range)));
                    break;
                case 6: case 7:
                    t.fo(m.remove(key(t, fam, mode, range)));
                    break;
                case 8:
                    t.f(m.containsKey(key(t, fam, mode, range)));
                    break;
                case 9:
                    t.f(m.containsValue(val(t)));
                    break;
                case 10:
                    t.fo(m.putIfAbsent(key(t, fam, mode, range), val(t)));
                    break;
                case 11:
                    t.fo(m.getOrDefault(key(t, fam, mode, range), -1));
                    break;
                case 12:
                    t.f(m.remove(key(t, fam, mode, range), val(t)));
                    break;
                case 13:
                    t.fo(m.replace(key(t, fam, mode, range), val(t)));
                    break;
                case 14:
                    t.f(m.replace(key(t, fam, mode, range), val(t), val(t)));
                    break;
                case 15: {
                    final int salt = t.r(4);
                    t.fo(m.computeIfAbsent(key(t, fam, mode, range),
                        k -> ((T.code(k) + salt) % 3 == 0) ? null : (Object) ((T.code(k) + salt) % 41)));
                    break;
                }
                case 16:
                    t.fo(m.computeIfPresent(key(t, fam, mode, range),
                        (k, v) -> (iv(v) % 3 == 0) ? null : (Object) (iv(v) + 1)));
                    break;
                case 17:
                    t.fo(m.compute(key(t, fam, mode, range),
                        (k, v) -> v == null ? ((T.code(k) & 1) == 0 ? null : (Object) 5)
                                            : (iv(v) % 4 == 0 ? null : (Object) (iv(v) * 2))));
                    break;
                case 18:
                    t.fo(m.merge(key(t, fam, mode, range), val(t),
                        (a, b) -> (iv(a) % 5 == 0) ? null : (Object) (iv(a) + iv(b))));
                    break;
                case 19:
                    t.f(m.size());
                    t.f(m.isEmpty());
                    break;
                case 20:
                    foldViews(t, m);
                    break;
                case 21: {   // iterator walk with remove at random positions
                    int which = t.r(3);
                    Iterator<?> it = which == 0 ? m.keySet().iterator()
                                   : which == 1 ? m.values().iterator() : m.entrySet().iterator();
                    while (it.hasNext()) {
                        Object x = it.next();
                        t.fo(x);
                        if (t.chance(30)) it.remove();
                    }
                    t.f(m.size());
                    if (t.chance(30)) it.next();          // NoSuchElementException
                    break;
                }
                case 22: {   // iterator misuse: remove before next / twice
                    Iterator<Object> it = m.keySet().iterator();
                    if (t.chance(50)) it.remove();          // IllegalStateException
                    if (it.hasNext()) {
                        t.fo(it.next());
                        it.remove();
                        it.remove();                        // IllegalStateException
                    }
                    break;
                }
                case 23: {   // fail-fast: modify during iteration
                    Iterator<Map.Entry<Object, Object>> it = m.entrySet().iterator();
                    int n = t.r(4);
                    for (int i = 0; i < n && it.hasNext(); i++) t.f(T.code(it.next()));
                    int how = t.r(6);
                    Object k = key(t, fam, mode, range);
                    if (how == 0) t.fo(m.put(k, val(t)));
                    else if (how == 1) t.fo(m.remove(k));
                    else if (how == 2) t.fo(m.get(k));      // structural only in access order
                    else if (how == 3) m.clear();
                    else if (how == 4) t.fo(m.putIfAbsent(k, val(t)));
                    else t.fo(m.getOrDefault(k, 3));
                    t.f(it.hasNext());
                    t.f(T.code(it.next()));
                    it.remove();
                    t.f(m.size());
                    break;
                }
                case 24: {   // entry setValue through the entry set
                    for (Map.Entry<Object, Object> e : m.entrySet()) {
                        if (t.chance(40)) t.fo(e.setValue(val(t)));
                    }
                    foldViews(t, m);
                    break;
                }
                case 25: {
                    Object k = key(t, fam, mode, range);
                    int w = t.r(5);
                    if (w == 0) t.f(m.keySet().remove(k));
                    else if (w == 1) t.f(m.values().remove(val(t)));
                    else if (w == 2) t.f(m.entrySet().remove(new AbstractMap.SimpleEntry<>(k, val(t))));
                    else if (w == 3) t.f(m.entrySet().contains(new AbstractMap.SimpleImmutableEntry<>(k, val(t))));
                    else t.f(m.keySet().contains(k) ? 3 : (m.values().contains(val(t)) ? 4 : 5));
                    break;
                }
                case 26:
                    if (t.chance(25)) {
                        m.clear();
                        t.f(m.size());
                    }
                    break;
                case 27: {
                    final T tt = t;
                    m.forEach((k, v) -> tt.f(T.code(k) * 7 + T.code(v)));
                    break;
                }
                case 28:
                    m.replaceAll((k, v) -> (iv(v) % 7 == 0) ? null : (Object) (iv(v) + T.code(k) % 5));
                    foldViews(t, m);
                    break;
                case 29: {
                    HashMap<Object, Object> copy = new HashMap<>(m);
                    t.f(copy.equals(m));
                    t.f(m.equals(copy));
                    t.f(copy.hashCode() == m.hashCode());
                    t.f(m.hashCode());
                    foldViews(t, copy);
                    if (!copy.isEmpty() && t.chance(50)) copy.put(key(t, fam, mode, range), -99);
                    t.f(m.equals(copy));
                    break;
                }
                case 30: {
                    HashMap<Object, Object> other = new HashMap<>();
                    int n = t.r(6);
                    for (int i = 0; i < n; i++) other.put(key(t, fam, mode, range), val(t));
                    m.putAll(other);
                    t.f(m.size());
                    break;
                }
                case 31: {
                    final int salt = t.r(5);
                    int w = t.r(3);
                    if (w == 0) t.f(m.keySet().removeIf(k -> (T.code(k) + salt) % 4 == 0));
                    else if (w == 1) t.f(m.values().removeIf(v -> (T.code(v) + salt) % 3 == 0));
                    else t.f(m.entrySet().removeIf(e -> (T.code(e) + salt) % 5 == 0));
                    t.f(m.size());
                    break;
                }
                case 32: {   // a mapping function that modifies the map: ConcurrentModificationException
                    final Map<Object, Object> mm = m;
                    final Object extra = key(t, fam, mode, range);
                    t.fo(m.computeIfAbsent(key(t, fam, mode, range), k -> {
                        mm.put(extra, 1);
                        return 2;
                    }));
                    break;
                }
                default: {
                    HashSet<Object> ks = new HashSet<>();
                    int n = t.r(5);
                    for (int i = 0; i < n; i++) ks.add(key(t, fam, mode, range));
                    if (t.chance(50)) t.f(m.keySet().removeAll(ks));
                    else t.f(m.keySet().retainAll(ks));
                    t.f(m.size());
                    break;
                }
            }
        } catch (RuntimeException e) {
            t.fe(e);
        }
    }

    static int run(int seed, int kind, int steps) {
        T t = new T(seed);
        int fam = t.r(4);
        int mode = t.r(8);
        int range = 4 + t.r(fam == 2 ? 28 : 60);
        Map<Object, Object> m = newMap(t, kind);
        for (int i = 0; i < steps; i++) step(t, m, fam, mode, range);
        foldViews(t, m);
        return t.acc;
    }

    /** HashMap(), HashMap(n), HashMap(n, lf): 40 random operations. */
    public static int hashMap(int seed) {
        T t = new T(seed ^ 0x5bd1e995);
        return run(seed, t.r(3), 40);
    }

    /** LinkedHashMap: insertion order, access order, LRU subclass (removeEldestEntry). */
    public static int linkedHashMap(int seed) {
        T t = new T(seed ^ 0x27d4eb2d);
        return run(seed, 3 + t.r(4), 40);
    }

    /** Many insertions of colliding keys: tree bins (treeify, insert, remove, split on
     *  resize, untreeify), then lookups, removals and iteration order. */
    public static int treeBins(int seed) {
        T t = new T(seed);
        int fam = t.r(10);
        fam = fam < 6 ? 0 : fam < 8 ? 2 : 3;
        int mode = fam == 0 ? new int[] {1, 2, 2, 7, 4, 0}[t.r(6)] : 0;
        int range = fam == 0 ? 20 + t.r(140) : fam == 2 ? 16 + t.r(48) : 40 + t.r(60);
        int kind = t.r(5);
        Map<Object, Object> m = kind == 0 ? new HashMap<>(64)
                              : kind == 1 ? new HashMap<>()
                              : kind == 2 ? new LinkedHashMap<>(64)
                              : kind == 3 ? new HashMap<>(t.r(300), 0.75f)
                              : new LinkedHashMap<>(16, 0.75f, true);
        ArrayList<Map.Entry<Object, Object>> held = new ArrayList<>();
        int n = 20 + t.r(60);
        for (int i = 0; i < n; i++) {
            Object k = treeKey(t, fam, mode, range);
            try {
                int w = t.r(10);
                if (w < 6) t.fo(m.put(k, i));
                else if (w == 6) t.fo(m.remove(k));
                else if (w == 7) t.fo(m.computeIfAbsent(k, x -> 3));
                else if (w == 8) t.fo(m.merge(k, 1, (a, b) -> (Integer) a + (Integer) b));
                else t.fo(m.get(k));
                if (i % 16 == 5 && !m.isEmpty()) held.add(m.entrySet().iterator().next());
            } catch (RuntimeException e) {
                t.fe(e);
            }
        }
        foldViews(t, m);
        // removal phase (direct removes, iterator removes) with iteration in between
        int r = 10 + t.r(40);
        for (int i = 0; i < r; i++) {
            Object k = treeKey(t, fam, mode, range);
            try {
                int w = t.r(6);
                if (w < 3) t.fo(m.remove(k));
                else if (w == 3) t.f(m.containsKey(k));
                else if (w == 4) {
                    Iterator<Object> it = m.keySet().iterator();
                    int skip = t.r(m.size() + 1);
                    for (int j = 0; j < skip && it.hasNext(); j++) t.fo(it.next());
                    if (it.hasNext()) {
                        t.fo(it.next());
                        it.remove();
                    }
                } else foldViews(t, m);
            } catch (RuntimeException e) {
                t.fe(e);
            }
        }
        // entries taken earlier: still the map's entries only if no treeify/untreeify replaced them
        for (Map.Entry<Object, Object> e : held) {
            t.fo(e.getKey());
            t.fo(e.setValue(-7));
            t.fo(m.get(e.getKey()));
        }
        foldViews(t, m);
        return t.acc;
    }

    static Object treeKey(T t, int fam, int mode, int range) {
        if (t.chance(2)) return null;
        if (fam == 0) return t.key(mode, range);
        if (fam == 2) return t.strKeyLong(range);
        return t.longKey(range);
    }

    /** toString of the collections (iteration order, nesting, null, self-reference). */
    public static String strings(int seed) {
        T t = new T(seed);
        int fam = t.r(4);
        int mode = t.r(8);
        int range = 4 + t.r(30);
        Map<Object, Object> m = t.chance(50) ? new HashMap<>() : new LinkedHashMap<>();
        int n = t.r(12);
        for (int i = 0; i < n; i++) m.put(key(t, fam, mode, range), val(t));
        StringBuilder sb = new StringBuilder();
        sb.append(m.toString()).append('|').append(m.keySet().toString()).append('|');
        sb.append(m.values().toString()).append('|').append(m.entrySet().toString()).append('|');
        sb.append(new HashSet<>(m.values()).toString()).append('|');
        sb.append(Collections.unmodifiableMap(m).toString()).append(Arrays.asList((Object) 1, null, "x").toString()).append('|');
        ArrayList<Object> l = new ArrayList<>(m.keySet());
        if (t.chance(30)) l.add(l);
        if (t.chance(30)) m.put(1, m);
        sb.append(l.toString()).append('|').append(m.toString());
        return sb.toString();
    }

    /** Copies and bulk operations: HashMap(Map)/LinkedHashMap(Map) pre-sizing, putAll into
     *  empty and non-empty maps, equals/hashCode between kinds, views' bulk operations. */
    public static int copies(int seed) {
        T t = new T(seed);
        int fam = t.r(2);
        int mode = t.r(8);
        int range = 8 + t.r(120);
        Map<Object, Object> a = t.chance(50) ? new HashMap<>(t.r(10)) : new LinkedHashMap<>();
        int n = t.r(45);
        for (int i = 0; i < n; i++) a.put(key(t, fam, mode, range), val(t));
        foldViews(t, a);
        Map<Object, Object> b = t.chance(50) ? new HashMap<>(a) : new LinkedHashMap<>(a);
        foldViews(t, b);
        t.f(a.equals(b));
        t.f(b.equals(a));
        t.f(a.hashCode());
        Map<Object, Object> c = new HashMap<>(t.r(4));
        int pre = t.r(10);
        for (int i = 0; i < pre; i++) c.put(key(t, fam, mode, range), val(t));
        c.putAll(a);
        foldViews(t, c);
        HashMap<Object, Object> d = new HashMap<>();
        d.putAll(a);
        foldViews(t, d);
        for (int i = 0; i < 6; i++) step(t, b, fam, mode, range);
        t.f(a.equals(b));
        t.f(b.equals(a));
        t.f(a.keySet().equals(b.keySet()));
        t.f(a.entrySet().equals(b.entrySet()));
        t.f(a.keySet().hashCode());
        t.f(a.entrySet().hashCode());
        t.f(b.keySet().containsAll(a.keySet()));
        t.f(a.values().containsAll(b.values()));
        Object[] arr = a.keySet().toArray();
        t.f(arr.length);
        for (Object o : arr) t.fo(o);
        Object[] arr2 = a.values().toArray(new Object[a.size() + 2]);
        t.f(arr2.length);
        for (Object o : arr2) t.fo(o);
        t.f(a.keySet() == a.keySet());
        t.f(a.entrySet() == a.entrySet());
        t.f(a.values() == a.values());
        return t.acc;
    }

    /** The documented STUCK case: more than 8 keys with EQUAL hash codes, of one class that is
     *  not Comparable, in one bin of a table with >= 64 slots.  The JDK orders such a tree bin
     *  by System.identityHashCode, so its iteration order is not a function of the program; the
     *  model calls System.identityHashCode, which has no model: the machine is STUCK. */
    public static int tieBreak(int seed) {
        T t = new T(seed);
        HashMap<Object, Object> m = new HashMap<>(64);
        int n = 9 + t.r(8);
        for (int i = 0; i < n; i++) m.put(new K(i, 42), i);
        for (Object k : m.keySet()) t.fo(k);
        return t.acc;
    }

    /** Constructor argument checks and capacity corner cases (inputs from the generator). */
    public static int ctor(int cap, int lfSel) {
        T t = new T(cap ^ lfSel);
        float lf = (lfSel & 7) == 0 ? 0f : (lfSel & 7) == 1 ? -1f : (lfSel & 7) == 2 ? Float.NaN
                 : (lfSel & 7) == 3 ? 0.1f : (lfSel & 7) == 4 ? 0.75f : (lfSel & 7) == 5 ? 2.5f
                 : (lfSel & 7) == 6 ? 0.05f : 100f;
        int c = (cap >= 0 && cap < 1000) ? cap : (cap & 0xff) - (cap < 0 ? 300 : 0);
        Map<Object, Object> m;
        try {
            m = ((lfSel >> 3) & 1) == 0 ? new HashMap<>(c, lf) : new LinkedHashMap<>(c, lf, ((lfSel >> 4) & 1) == 1);
        } catch (RuntimeException e) {
            t.fe(e);
            try {
                m = new HashMap<>(c);
            } catch (RuntimeException e2) {
                t.fe(e2);
                return t.acc;
            }
        }
        int n = t.r(40);
        for (int i = 0; i < n; i++) t.fo(m.put(t.key(i % 2 == 0 ? 1 : 3, 50), i));
        foldViews(t, m);
        return t.acc;
    }
}

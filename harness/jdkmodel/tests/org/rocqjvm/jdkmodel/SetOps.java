package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of HashSet / LinkedHashSet (and AbstractSet / AbstractCollection bulk
 *  operations through them). */
public final class SetOps {
    private SetOps() {
    }

    static Set<Object> newSet(T t, int kind, Collection<Object> src) {
        switch (kind) {
            case 0: return new HashSet<>();
            case 1: return new HashSet<>(t.r(40));
            case 2: return new HashSet<>(src);
            case 3: return new LinkedHashSet<>();
            case 4: return new LinkedHashSet<>(src);
            case 5: return new HashSet<>(t.r(10), t.chance(50) ? 0.5f : 2f);
            default: return new LinkedHashSet<>(t.r(10));
        }
    }

    static void fold(T t, Collection<Object> s) {
        for (Object o : s) t.fo(o);
        t.f(s.size());
    }

    public static int sets(int seed) {
        T t = new T(seed);
        int fam = t.r(3);
        int mode = t.r(8);
        int range = 4 + t.r(fam == 2 ? 28 : 80);
        ArrayList<Object> src = new ArrayList<>();
        int n0 = t.r(30);
        for (int i = 0; i < n0; i++) src.add(MapOps.key(t, fam, mode, range));
        Set<Object> s = newSet(t, t.r(7), src);
        fold(t, s);
        for (int step = 0; step < 40; step++) {
            try {
                int op = t.r(16);
                Object k = MapOps.key(t, fam, mode, range);
                switch (op) {
                    case 0: case 1: case 2: case 3:
                        t.f(s.add(k));
                        break;
                    case 4: case 5:
                        t.f(s.remove(k));
                        break;
                    case 6:
                        t.f(s.contains(k));
                        break;
                    case 7:
                        fold(t, s);
                        break;
                    case 8: {
                        Iterator<Object> it = s.iterator();
                        while (it.hasNext()) {
                            t.fo(it.next());
                            if (t.chance(25)) it.remove();
                        }
                        if (t.chance(20)) it.remove();
                        break;
                    }
                    case 9: {
                        Iterator<Object> it = s.iterator();
                        if (it.hasNext()) t.fo(it.next());
                        if (t.chance(50)) s.add(k);
                        else s.remove(k);
                        t.f(it.hasNext());
                        t.fo(it.next());
                        break;
                    }
                    case 10: {
                        ArrayList<Object> c = new ArrayList<>();
                        int n = t.r(8);
                        for (int i = 0; i < n; i++) c.add(MapOps.key(t, fam, mode, range));
                        int w = t.r(4);
                        if (w == 0) t.f(s.addAll(c));
                        else if (w == 1) t.f(s.removeAll(c));
                        else if (w == 2) t.f(s.retainAll(c));
                        else t.f(s.containsAll(c));
                        t.f(s.size());
                        break;
                    }
                    case 11: {
                        Set<Object> other = t.chance(50) ? new HashSet<>(s) : new LinkedHashSet<>(s);
                        t.f(other.equals(s));
                        t.f(s.equals(other));
                        t.f(s.hashCode());
                        if (t.chance(50)) other.add(k);
                        else other.remove(k);
                        t.f(s.equals(other));
                        fold(t, other);
                        break;
                    }
                    case 12: {
                        final int salt = t.r(5);
                        t.f(s.removeIf(o -> (T.code(o) + salt) % 3 == 0));
                        fold(t, s);
                        break;
                    }
                    case 13: {
                        Object[] a = s.toArray();
                        t.f(a.length);
                        for (Object o : a) t.fo(o);
                        Object[] b = s.toArray(new Object[t.r(s.size() + 3)]);
                        t.f(b.length);
                        for (Object o : b) t.fo(o);
                        break;
                    }
                    case 14: {
                        final T tt = t;
                        s.forEach(o -> tt.fo(o));
                        if (t.chance(10)) s.clear();
                        break;
                    }
                    default:
                        t.f(s.isEmpty());
                        t.f(s.size());
                        break;
                }
            } catch (RuntimeException e) {
                t.fe(e);
            }
        }
        fold(t, s);
        return t.acc;
    }
}

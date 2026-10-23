package org.rocqjvm.jdkmodel;

import java.util.*;
import java.util.function.Consumer;

/** Bulk traversals that may modify the collection being traversed: forEach of maps and of
 *  their views (fail-fast check at the end), forEachRemaining of iterators (ArrayList's own,
 *  the default for HashMap/LinkedHashMap iterators), replaceAll, removeIf. */
public final class ViewOps {
    private ViewOps() {
    }

    public static int views(int seed) {
        T t = new T(seed);
        int fam = t.r(4);
        int mode = t.r(8);
        int range = 4 + t.r(40);
        int kind = t.r(4);
        Map<Object, Object> m = kind == 0 ? new HashMap<>() : kind == 1 ? new LinkedHashMap<>()
                              : kind == 2 ? new LinkedHashMap<>(8, 0.75f, true) : new HashMap<>(4);
        int n = t.r(30);
        for (int i = 0; i < n; i++) m.put(MapOps.key(t, fam, mode, range), MapOps.val(t));
        for (int round = 0; round < 6; round++) {
            final T tt = t;
            final Map<Object, Object> mm = m;
            final int when = t.r(Math.max(1, m.size() + 2));
            final int how = t.r(5);
            final Object k = MapOps.key(t, fam, mode, range);
            final int[] count = {0};
            Runnable modify = () -> {
                if (count[0]++ == when) {
                    if (how == 0) mm.put(k, 1);
                    else if (how == 1) mm.remove(k);
                    else if (how == 2) mm.get(k);
                    else if (how == 3) mm.putIfAbsent(k, 2);
                    else mm.replace(k, 3);
                }
            };
            try {
                switch (t.r(9)) {
                    case 0: m.forEach((a, b) -> { tt.fo(a); modify.run(); }); break;
                    case 1: m.keySet().forEach(a -> { tt.fo(a); modify.run(); }); break;
                    case 2: m.values().forEach(a -> { tt.fo(a); modify.run(); }); break;
                    case 3: m.entrySet().forEach(e -> { tt.f(T.code(e)); modify.run(); }); break;
                    case 4: m.replaceAll((a, b) -> { modify.run(); return b == null ? (Object) 4 : b; }); break;
                    case 5: {
                        Iterator<Object> it = m.keySet().iterator();
                        if (it.hasNext()) t.fo(it.next());
                        it.forEachRemaining(a -> { tt.fo(a); modify.run(); });
                        break;
                    }
                    case 6: {
                        Iterator<Map.Entry<Object, Object>> it = m.entrySet().iterator();
                        it.forEachRemaining(e -> { tt.f(T.code(e)); modify.run(); });
                        t.f(it.hasNext());
                        it.remove();
                        break;
                    }
                    case 7: t.f(m.values().removeIf(v -> { modify.run(); return T.code(v) % 3 == 0; })); break;
                    default: t.f(m.keySet().removeIf(a -> { modify.run(); return T.code(a) % 4 == 1; })); break;
                }
            } catch (RuntimeException e) {
                t.fe(e);
            }
            t.f(count[0]);
            MapOps.foldViews(t, m);
        }
        // ArrayList / HashSet traversals with modification
        ArrayList<Object> l = new ArrayList<>(m.keySet());
        Set<Object> s = t.chance(50) ? new HashSet<>(l) : new LinkedHashSet<>(l);
        for (int round = 0; round < 4; round++) {
            final T tt = t;
            final int when = t.r(Math.max(1, l.size() + 2));
            final int how = t.r(3);
            final int[] count = {0};
            final ArrayList<Object> ll = l;
            final Set<Object> ss = s;
            Consumer<Object> c = o -> {
                tt.fo(o);
                if (count[0]++ == when) {
                    if (how == 0) ll.add(5);
                    else if (how == 1) ss.add(6);
                    else if (!ll.isEmpty()) ll.set(0, 7);
                }
            };
            try {
                switch (t.r(4)) {
                    case 0: {
                        Iterator<Object> it = l.iterator();
                        if (it.hasNext() && t.chance(50)) t.fo(it.next());
                        it.forEachRemaining(c);
                        t.f(it.hasNext());
                        it.remove();
                        break;
                    }
                    case 1: s.forEach(c); break;
                    case 2: {
                        Iterator<Object> it = s.iterator();
                        it.forEachRemaining(c);
                        break;
                    }
                    default: l.forEach(c); break;
                }
            } catch (RuntimeException e) {
                t.fe(e);
            }
            t.f(count[0]);
            ListOps.fold(t, l);
            for (Object o : s) t.fo(o);
        }
        return t.acc;
    }
}

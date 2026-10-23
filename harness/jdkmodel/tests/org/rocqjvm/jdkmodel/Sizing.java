package org.rocqjvm.jdkmodel;

import java.util.*;

/** Table-length corner cases: the iteration order of keys with hash i << s reveals the table
 *  length, so these tests check the pre-sizing of HashMap(Map), putAll, HashSet(Collection),
 *  HashMap(n)/HashSet(n) and the resize thresholds for sizes taken from the input. */
public final class Sizing {
    private Sizing() {
    }

    public static int sizing(int n0, int sel) {
        T t = new T(n0 * 31 + sel);
        int n = (n0 >= 0 && n0 < 200) ? n0 : ((n0 >>> 3) % 200);
        int s = 1 + ((sel & 0x7fffffff) % 6);           // hash = i << s
        int what = (sel >>> 8) & 7;
        LinkedHashMap<Object, Object> src = new LinkedHashMap<>();
        for (int i = 0; i < n; i++) src.put(new K(i, i << s), i);
        Collection<Object> out;
        switch (what) {
            case 0: out = new HashMap<>(src).keySet(); break;
            case 1: out = new HashSet<>(src.keySet()); break;
            case 2: {
                HashMap<Object, Object> m = new HashMap<>();
                int pre = (sel >>> 12) & 31;
                for (int i = 0; i < pre; i++) m.put(new K(1000 + i, (1000 + i) << s), i);
                m.putAll(src);
                out = m.keySet();
                break;
            }
            case 3: {
                HashMap<Object, Object> m = new HashMap<>(n);
                for (int i = 0; i < n; i++) m.put(new K(i, i << s), i);
                out = m.keySet();
                break;
            }
            case 4: {
                HashSet<Object> h = new HashSet<>(n);
                h.addAll(src.keySet());
                out = h;
                break;
            }
            case 5: {
                HashMap<Object, Object> m = new HashMap<>((sel >>> 12) & 63, 0.75f);
                m.putAll(src);
                out = m.keySet();
                break;
            }
            case 6: {   // compute* resize before inserting; put resizes after
                HashMap<Object, Object> m = new HashMap<>();
                for (int i = 0; i < n; i++) {
                    K k = new K(i, i << s);
                    if (((sel >>> 12) + i) % 3 == 0) m.computeIfAbsent(k, x -> 1);
                    else if (((sel >>> 12) + i) % 3 == 1) m.merge(k, 1, (a, b) -> a);
                    else m.put(k, 1);
                }
                out = m.keySet();
                break;
            }
            default: {
                HashMap<Object, Object> m = new HashMap<>(src);
                HashMap<Object, Object> m2 = new HashMap<>(m);
                m2.putAll(m);
                out = m2.keySet();
                break;
            }
        }
        for (Object o : out) t.fo(o);
        t.f(out.size());
        return t.acc;
    }
}

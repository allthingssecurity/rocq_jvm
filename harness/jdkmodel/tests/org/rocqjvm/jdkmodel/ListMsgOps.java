package org.rocqjvm.jdkmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;

/** Differential tests of ArrayList (and the AbstractList views of Arrays.asList and the
 *  Collections lists): exception messages, sub lists (nested, co-modification), clone. */
public final class ListMsgOps {
    private ListMsgOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static String el() {
        return r(8) == 0 ? null : "e" + r(5);
    }

    static String ex(RuntimeException e) {
        return "!" + e.getClass().getSimpleName() + ":" + e.getMessage();
    }

    public static String arrayList(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        ArrayList<String> l = new ArrayList<>();
        for (int i = r(5); i > 0; i--) l.add(el());
        List<String> sub = null, sub2 = null;
        int ops = 8 + r(14);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(26)) {
                    case 0: case 1: l.add(el()); break;
                    case 2: l.add(r(6) - 1, el()); break;
                    case 3: out.append(l.get(r(6) - 1)); break;
                    case 4: out.append(l.set(r(6) - 1, el())); break;
                    case 5: out.append(l.remove(r(6) - 1)); break;
                    case 6: out.append(l.addAll(r(6) - 1, Arrays.asList("a", "b"))); break;
                    case 7: l.listIterator(r(7) - 1); break;
                    case 8: sub = l.subList(r(3) - 1, r(6) - 1); out.append(sub); break;
                    case 9: if (sub != null) { sub.add(el()); out.append(sub).append(sub.size()); } break;
                    case 10: if (sub != null) out.append(sub.get(r(4) - 1)); break;
                    case 11: if (sub != null) out.append(sub.remove(r(4) - 1)); break;
                    case 12: if (sub != null) { sub.add(r(5) - 1, "z"); out.append(sub); } break;
                    case 13: if (sub != null) { sub2 = sub.subList(0, r(3)); out.append(sub2); } break;
                    case 14: if (sub2 != null) { sub2.clear(); out.append(sub).append(l); } break;
                    case 15: if (sub != null) { out.append(sub.removeIf(x -> x == null || x.endsWith("1"))); out.append(sub); } break;
                    case 16: if (sub != null) { out.append(sub.retainAll(Arrays.asList("e2", "e3", null))); out.append(sub); } break;
                    case 17: if (sub != null) { ListIterator<String> it = sub.listIterator(); while (it.hasNext()) { String x = it.next(); if (x == null) it.remove(); else it.set(x + "'"); } it.add("q"); out.append(sub); } break;
                    case 18: if (sub != null) { out.append(sub.equals(new ArrayList<>(sub))).append(sub.hashCode()).append(sub.indexOf(el())).append(sub.lastIndexOf(el())); } break;
                    case 19: if (sub != null) { sub.replaceAll(x -> x + "#"); sub.sort(null); out.append(sub); } break;
                    case 20: { @SuppressWarnings("unchecked") ArrayList<String> c = (ArrayList<String>) l.clone(); c.add("cl"); out.append(c).append(c.equals(l)); break; }
                    case 21: out.append(Arrays.toString(l.toArray(new String[r(3)]))); if (sub != null) out.append(Arrays.toString(sub.toArray(new String[0]))).append(Arrays.toString(sub.toArray())); break;
                    case 22: new ArrayList<String>(r(3) - 2); break;
                    case 23: { Iterator<String> it = l.iterator(); it.remove(); break; }
                    case 24: if (sub != null) { for (String x : sub) out.append(x); } break;
                    default: out.append(l.removeAll(Arrays.asList(el()))); break;
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(l).append(';');
        }
        return out.toString();
    }

    public static String views(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                List<String> base;
                switch (r(4)) {
                    case 0: base = Arrays.asList("a", "b", "c", "d"); break;
                    case 1: base = Collections.singletonList("x"); break;
                    case 2: base = Collections.emptyList(); break;
                    default: base = Collections.unmodifiableList(new ArrayList<>(Arrays.asList("p", "q", "r"))); break;
                }
                switch (r(6)) {
                    case 0: out.append(base.get(r(5) - 1)); break;
                    case 1: { List<String> v = base.subList(r(3) - 1, r(4)); out.append(v).append(v.size()); out.append(v.get(r(3) - 1)); break; }
                    case 2: { List<String> v = base.subList(0, base.size()); out.append(v.subList(0, Math.min(1, v.size()))); v.set(0, "S"); out.append(base); break; }
                    case 3: base.listIterator(r(6) - 1); break;
                    case 4: out.append(base.indexOf("c")).append(base.lastIndexOf("a")); base.add("n"); break;
                    default: { List<String> v = base.subList(0, Math.min(2, base.size())); out.append(v.hashCode()).append(v.equals(base)); v.remove(0); break; }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String clones(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        HashMap<String, Integer> m = new HashMap<>();
        for (int i = 0; i < 2 + r(4); i++) m.put("k" + r(6), i);
        @SuppressWarnings("unchecked") HashMap<String, Integer> mc = (HashMap<String, Integer>) m.clone();
        mc.put("new", 1);
        HashSet<String> st = new HashSet<>(m.keySet());
        @SuppressWarnings("unchecked") HashSet<String> sc = (HashSet<String>) st.clone();
        sc.remove("k1");
        out.append(m).append(mc).append(st).append(sc);
        return out.toString();
    }
}

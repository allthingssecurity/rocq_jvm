package org.rocqjvm.jdkmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

/** Differential tests of the immutable collections (List.of/copyOf, Set.of/copyOf, Map.of/ofEntries/
 *  entry/copyOf): null checks, duplicates, unsupported operations, indexes, sub lists, iterators,
 *  equality and hash codes, class names. Iteration order of Set.of/Map.of depends on a per-run salt,
 *  so set and map iteration results are sorted (the order itself is checked by the salt-free tests). */
public final class ImmOps {
    private ImmOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static Object el() {
        switch (r(8)) {
            case 0: return null;
            case 1: return "k" + r(6);
            case 2: return r(6);
            default: return "e" + r(9);
        }
    }

    static Object[] els(int n) {
        Object[] a = new Object[n];
        for (int i = 0; i < n; i++) a[i] = el();
        return a;
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    static List list(Object[] a) {
        switch (a.length) {
            case 0: return List.of();
            case 1: return List.of(a[0]);
            case 2: return List.of(a[0], a[1]);
            case 3: return r(2) == 0 ? List.of(a[0], a[1], a[2]) : List.of(a);
            default: return r(3) == 0 ? List.of(a[0], a[1], a[2], a[3]) : List.of(a);
        }
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    static Set set(Object[] a) {
        switch (a.length) {
            case 0: return Set.of();
            case 1: return Set.of(a[0]);
            case 2: return Set.of(a[0], a[1]);
            case 3: return r(2) == 0 ? Set.of(a[0], a[1], a[2]) : Set.of(a);
            default: return Set.of(a);
        }
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    static Map map(Object[] a) {
        switch (a.length) {
            case 0: return Map.of();
            case 1: return Map.of(a[0], "v");
            case 2: return Map.of(a[0], "v0", a[1], "v1");
            case 3: return Map.of(a[0], "v0", a[1], "v1", a[2], "v2");
            default:
                Map.Entry[] es = new Map.Entry[a.length];
                for (int i = 0; i < a.length; i++) es[i] = Map.entry(a[i], r(5) == 0 ? null : "w" + i);
                return Map.ofEntries(es);
        }
    }

    /** sorted string form, independent of the iteration order */
    static String sorted(Collection<?> c) {
        List<String> l = new ArrayList<>();
        for (Object o : c) l.add(String.valueOf(o));
        Collections.sort(l);
        return l.toString();
    }

    static String cls(Object o) {
        return o.getClass().getName().replace("java.util.ImmutableCollections$", "IC$");
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String lists(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int rounds = 4 + r(5);
        for (int k = 0; k < rounds; k++) {
            try {
                List l = list(els(r(6)));
                out.append(cls(l)).append(l.size()).append(l).append(l.hashCode()).append(',');
                switch (r(14)) {
                    case 0: out.append(l.contains(el())); break;
                    case 1: out.append(l.indexOf(el())).append(l.lastIndexOf(el())); break;
                    case 2: out.append(l.get(r(5) - 1)); break;
                    case 3: l.add("x"); break;
                    case 4: l.set(0, "x"); break;
                    case 5: { int a = r(5) - 1, b = r(6) - 1; List sub = l.subList(a, b);
                              out.append(cls(sub)).append(sub).append(sub.size());
                              if (r(2) == 0) out.append(sub.get(r(4) - 1)); else out.append(sub.subList(0, r(3))); break; }
                    case 6: { ListIterator it = l.listIterator(r(4)); out.append(it.hasPrevious()).append(it.nextIndex());
                              while (it.hasNext()) out.append(it.next()); out.append(it.previous()); it.set("z"); break; }
                    case 7: { Iterator it = l.iterator(); while (it.hasNext()) out.append(it.next()); it.next(); break; }
                    case 8: out.append(l.equals(Arrays.asList(els(r(4))))).append(l.equals(new ArrayList<>(l))); break;
                    case 9: { List c = List.copyOf(r(2) == 0 ? l : Arrays.asList(els(r(4)))); out.append(cls(c)).append(c).append(c == l); break; }
                    case 10: out.append(Arrays.toString(l.toArray())).append(Arrays.toString(l.toArray(new String[r(5)]))); break;
                    case 11: l.removeIf(o -> true); break;
                    case 12: l.sort(null); break;
                    default: out.append(l.iterator().hasNext()).append(l.isEmpty()); l.iterator().remove(); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String sets(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int rounds = 4 + r(5);
        for (int k = 0; k < rounds; k++) {
            try {
                Set st = set(els(r(6)));
                out.append(cls(st)).append(st.size()).append(st.hashCode()).append(st.isEmpty()).append(',');
                switch (r(9)) {
                    case 0: out.append(st.contains(el())); break;
                    case 1: st.add("x"); break;
                    case 2: st.remove("x"); break;
                    case 3: out.append(st.equals(new HashSet<>(Arrays.asList(els(r(4)))))); break;
                    case 4: { Set c = Set.copyOf(r(2) == 0 ? st : Arrays.asList(els(r(5)))); out.append(cls(c)).append(c.size()).append(c == st); break; }
                    case 5: out.append(st.containsAll(Arrays.asList(els(r(3))))); break;
                    case 6: st.clear(); break;
                    case 7: out.append(st.equals(Set.of())).append(Set.of().equals(st)); break;
                    default: out.append(st.size() == 1 ? st.iterator().next() : "n"); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String maps(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int rounds = 4 + r(5);
        for (int k = 0; k < rounds; k++) {
            try {
                Map m = map(els(r(6)));
                out.append(cls(m)).append(m.size()).append(m.hashCode()).append(',');
                switch (r(11)) {
                    case 0: out.append(m.get(el())); break;
                    case 1: out.append(m.containsKey(el())).append(m.containsValue(r(2) == 0 ? null : "v0")); break;
                    case 2: m.put("a", "b"); break;
                    case 3: out.append(m.getOrDefault(el(), "dflt")); break;
                    case 4: m.computeIfAbsent("q", x -> "y"); break;
                    case 5: { Map c = Map.copyOf(r(2) == 0 ? m : new HashMap(Map.of("p", 1))); out.append(cls(c)).append(c.size()).append(c == m); break; }
                    case 6: out.append(m.equals(new HashMap<>(m))).append(new HashMap<>(Map.of("k1", "v")).equals(m)); break;
                    case 7: { Map.Entry e = Map.entry(el(), el()); out.append(e).append(e.hashCode()).append(e.equals(Map.entry("k1", "e1"))); e.setValue("z"); break; }
                    case 8: out.append(m.remove("k1")); break;
                    case 9: { LinkedHashMap lm = new LinkedHashMap(); lm.put("a", r(3)); lm.put("b", el());
                              Map c = Map.copyOf(lm); out.append(cls(c)).append(c.get("a")); break; }
                    default: out.append(m.size() == 1 ? m.entrySet().iterator().next() : "n"); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    /** Iteration of sets and maps with two or more elements: only salt-independent views (sorted). */
    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String iteration(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 4; k++) {
            try {
                Set st = set(els(2 + r(4)));
                out.append(sorted(st)).append(sorted(Arrays.asList(st.toArray()))).append(new HashSet<>(st).equals(st));
                Map m = map(els(2 + r(4)));
                out.append(sorted(m.keySet())).append(sorted(m.values())).append(sorted(m.entrySet()));
                out.append(new HashMap<>(m).equals(m)).append(m.toString().length());
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }
}

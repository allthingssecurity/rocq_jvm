package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of Collections.empty and singleton and unmodifiable factories, and of
 *  Arrays.asList (together with the Rocq models of Arrays.fill/copyOf, which must still be
 *  reached although java/util/Arrays is a loaded class). */
public final class CollOps {
    private CollOps() {
    }

    static void listProbe(T t, List<Object> l, int in) {
        try { t.f(l.size()); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(l.get(ListOps.idx(t, l, in))); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(l.set(ListOps.idx(t, l, in), 5)); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.add(6)); } catch (RuntimeException e) { t.fe(e); }
        try { l.add(0, 6); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(l.remove(0)); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.remove((Object) 3)); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.contains(3)); t.f(l.indexOf(null)); t.f(l.lastIndexOf(3)); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.hashCode()); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.equals(new ArrayList<>(l))); t.f(new ArrayList<>(l).equals(l)); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.isEmpty()); } catch (RuntimeException e) { t.fe(e); }
        try { l.clear(); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.addAll(Arrays.asList(1, 2))); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.addAll(new ArrayList<>())); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.removeAll(Arrays.asList(3))); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.retainAll(Arrays.asList(3))); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(l.removeIf(o -> T.code(o) == 3)); } catch (RuntimeException e) { t.fe(e); }
        try { l.replaceAll(o -> o); } catch (RuntimeException e) { t.fe(e); }
        try {
            Iterator<Object> it = l.iterator();
            while (it.hasNext()) t.fo(it.next());
            try { it.next(); } catch (RuntimeException e) { t.fe(e); }
            it.remove();
        } catch (RuntimeException e) { t.fe(e); }
        try {
            ListIterator<Object> it = l.listIterator(ListOps.idx(t, l, in));
            if (it.hasPrevious()) t.fo(it.previous());
            t.f(it.nextIndex());
            if (it.hasNext()) t.fo(it.next());
            it.set(4);
        } catch (RuntimeException e) { t.fe(e); }
        try { Object[] a = l.toArray(); t.f(a.length); for (Object o : a) t.fo(o); } catch (RuntimeException e) { t.fe(e); }
        try { final T tt = t; l.forEach(o -> tt.fo(o)); } catch (RuntimeException e) { t.fe(e); }
        try { for (Object o : l) t.fo(o); } catch (RuntimeException e) { t.fe(e); }
    }

    static void mapProbe(T t, Map<Object, Object> m) {
        try { t.f(m.size()); t.f(m.isEmpty()); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.get(1)); t.f(m.containsKey(1)); t.f(m.containsValue(2)); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.getOrDefault(9, 8)); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.put(1, 2)); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.remove(1)); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.remove(77)); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.putIfAbsent(1, 2)); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.computeIfAbsent(1, k -> 2)); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.merge(1, 2, (a, b) -> a)); } catch (RuntimeException e) { t.fe(e); }
        try { t.fo(m.replace(1, 2)); } catch (RuntimeException e) { t.fe(e); }
        try { m.putAll(new HashMap<>()); } catch (RuntimeException e) { t.fe(e); }
        try { m.clear(); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(m.hashCode()); t.f(m.equals(new HashMap<>(m))); t.f(new HashMap<>(m).equals(m)); } catch (RuntimeException e) { t.fe(e); }
        try { MapOps.foldViews(t, m); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(m.keySet().remove(2)); } catch (RuntimeException e) { t.fe(e); }
        try { t.f(m.values().remove(2)); } catch (RuntimeException e) { t.fe(e); }
        try { m.keySet().clear(); } catch (RuntimeException e) { t.fe(e); }
        try {
            for (Map.Entry<Object, Object> e : m.entrySet()) {
                t.f(T.code(e));
                t.f(e.hashCode());
                t.f(e.equals(new AbstractMap.SimpleEntry<>(e.getKey(), e.getValue())));
                t.fo(e.setValue(3));
            }
        } catch (RuntimeException e) { t.fe(e); }
        try {
            Iterator<Object> it = m.keySet().iterator();
            if (it.hasNext()) t.fo(it.next());
            it.remove();
        } catch (RuntimeException e) { t.fe(e); }
        try {
            t.f(m.entrySet().contains(new AbstractMap.SimpleEntry<>(1, 2)));
            t.f(m.entrySet().containsAll(new HashMap<>(m).entrySet()));
            t.f(m.entrySet().equals(new HashMap<>(m).entrySet()));
            t.f(m.keySet().equals(new HashSet<>(m.keySet())));
        } catch (RuntimeException e) { t.fe(e); }
        try { final T tt = t; m.forEach((k, v) -> tt.f(T.code(k) + 3 * T.code(v))); } catch (RuntimeException e) { t.fe(e); }
    }

    public static int collections(int seed, int in) {
        T t = new T(seed);
        int which = t.r(12);
        List<Object> base = new ArrayList<>();
        int n = t.r(6);
        for (int i = 0; i < n; i++) base.add(ListOps.elem(t));
        Map<Object, Object> mbase = t.chance(50) ? new HashMap<>() : new LinkedHashMap<>();
        for (int i = 0; i < n; i++) mbase.put(t.r(5), MapOps.val(t));
        switch (which) {
            case 0: listProbe(t, Collections.emptyList(), in); break;
            case 1: listProbe(t, Collections.singletonList(ListOps.elem(t)), in); break;
            case 2: {
                List<Object> u = Collections.unmodifiableList(base);
                t.f(Collections.unmodifiableList(u) == u);
                listProbe(t, u, in);
                base.add(7);   // the view follows its list
                listProbe(t, u, in);
                break;
            }
            case 3: mapProbe(t, Collections.emptyMap()); break;
            case 4: {
                Map<Object, Object> u = Collections.unmodifiableMap(mbase);
                t.f(Collections.unmodifiableMap(u) == u);
                mapProbe(t, u);
                mbase.put(3, 4);
                mapProbe(t, u);
                break;
            }
            case 5: {
                t.f(Collections.emptyList() == Collections.emptyList());
                t.f(Collections.emptyMap().equals(new HashMap<>()));
                t.f(Collections.emptyList().equals(new ArrayList<>()));
                t.f(Collections.emptyList().hashCode());
                t.f(Collections.emptySet().hashCode());
                t.f(Collections.emptySet().equals(new HashSet<>()));
                Iterator<Object> it = Collections.emptyIterator();
                t.f(it.hasNext());
                try { it.next(); } catch (RuntimeException e) { t.fe(e); }
                try { it.remove(); } catch (RuntimeException e) { t.fe(e); }
                try { Collections.unmodifiableList(null); } catch (RuntimeException e) { t.fe(e); }
                try { Collections.unmodifiableMap(null); } catch (RuntimeException e) { t.fe(e); }
                Set<Object> s1 = Collections.singleton(ListOps.elem(t));
                t.f(s1.size());
                t.f(s1.contains(3));
                t.f(s1.hashCode());
                for (Object o : s1) t.fo(o);
                try { s1.add(1); } catch (RuntimeException e) { t.fe(e); }
                try { s1.remove(1); } catch (RuntimeException e) { t.fe(e); }
                break;
            }
            case 6: case 7: {   // Arrays.asList
                Object[] arr = new Object[n];
                for (int i = 0; i < n; i++) arr[i] = ListOps.elem(t);
                List<Object> l = Arrays.asList(arr);
                listProbe(t, l, in);
                for (Object o : arr) t.fo(o);     // writes went through to the array
                arr[0 % Math.max(1, n)] = 33;
                if (n > 0) t.fo(l.get(0));
                break;
            }
            case 8: {   // asList of a String[]: storing a non-String is an ArrayStoreException
                String[] sa = {"x", "y", "z"};
                List<String> l = Arrays.asList(sa);
                try { ((List) l).set(1, 5); } catch (RuntimeException e) { t.fe(e); }
                try { l.set(in, "w"); } catch (RuntimeException e) { t.fe(e); }
                t.f(l.indexOf("z"));
                t.f(l.contains("q"));
                t.f(l.hashCode());
                t.f(l.toArray().length);
                t.f(l.toArray().getClass() == Object[].class);
                String[] small = l.toArray(new String[in & 3]);
                t.f(small.length);
                t.f(small.getClass() == String[].class);
                for (String x : small) t.fo(x);
                ArrayList<String> al = new ArrayList<>(l);
                String[] s2 = al.toArray(new String[0]);
                t.f(s2.length + (s2.getClass() == String[].class ? 100 : 0));
                HashSet<String> hs = new HashSet<>(l);
                String[] s3 = hs.toArray(new String[(in >>> 3) & 7]);
                t.f(s3.length);
                for (String x : s3) t.fo(x);
                t.f(new ArrayList<>(l).equals(l));
                break;
            }
            case 9: {   // the Rocq models of Arrays.fill / copyOf still work beside asList
                int[] a = new int[1 + t.r(6)];
                Arrays.fill(a, in);
                int[] b = Arrays.copyOf(a, t.r(9));
                t.f(b.length);
                for (int x : b) t.f(x);
                List<Integer> l = Arrays.asList(1, 2, in);
                t.f(l.size());
                t.f(l.get(2));
                t.f(l.hashCode());
                break;
            }
            case 10: listProbe(t, Collections.unmodifiableList(Arrays.asList(1, null, 3)), in); break;
            default: {
                Map<Object, Object> u = Collections.unmodifiableMap(Collections.emptyMap());
                mapProbe(t, u);
                listProbe(t, Collections.unmodifiableList(Collections.singletonList(3)), in);
                break;
            }
        }
        return t.acc;
    }
}

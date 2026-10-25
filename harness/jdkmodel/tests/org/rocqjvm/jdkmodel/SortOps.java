package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of sorting (List.sort, ArrayList.sort, Collections.sort, Arrays.sort) and of
 *  the Comparator combinators; identity hash codes are checked only for consistency. */
public final class SortOps {
    private SortOps() {
    }

    static final class E {
        final int key; final String name; final int seq;
        E(int key, String name, int seq) { this.key = key; this.name = name; this.seq = seq; }
        int getKey() { return key; }
        String getName() { return name; }
        public String toString() { return name + key + "#" + seq; }
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    public static String sorts(int seed) {
        s = seed;
        int n = r(25);
        List<E> base = new ArrayList<>();
        for (int i = 0; i < n; i++) base.add(new E(r(6), r(5) == 0 ? null : "n" + r(4), i));
        StringBuilder out = new StringBuilder();
        Comparator<E> byKey = Comparator.comparingInt(E::getKey);
        Comparator<E> byName = Comparator.comparing(E::getName, Comparator.nullsFirst(Comparator.naturalOrder()));
        List<Comparator<E>> cs = Arrays.asList(byKey, byKey.reversed(), byName, byName.thenComparing(byKey),
            byKey.thenComparing(E::getName, Comparator.nullsLast(Comparator.reverseOrder())),
            Collections.reverseOrder(byKey), Comparator.comparing(E::getKey).thenComparingInt(e -> -e.seq),
            Comparator.comparingLong(e -> (long) e.key * 1000 - e.seq));
        for (Comparator<E> c : cs) {
            List<E> l = new ArrayList<>(base);
            try {
                l.sort(c);
                out.append(l);
            } catch (RuntimeException ex) {
                out.append('!').append(ex.getClass().getSimpleName());
            }
            out.append('|');
        }
        List<E> l2 = Arrays.asList(base.toArray(new E[0]));
        Collections.sort(l2, byKey);
        out.append(l2).append('|');
        List<Integer> ints = new ArrayList<>();
        for (int i = 0; i < n; i++) ints.add(r(100) - 50);
        Collections.sort(ints);
        out.append(ints).append('|');
        ints.sort(Collections.reverseOrder());
        out.append(ints).append('|');
        Integer[] arr = ints.toArray(new Integer[0]);
        Arrays.sort(arr);
        out.append(Arrays.toString(arr)).append('|');
        String[] strs = { "b", "a", "c", "ab" };
        Arrays.sort(strs, 1, 4);
        out.append(Arrays.toString(strs));
        Arrays.sort(strs, Comparator.comparing(String::length).thenComparing(Comparator.reverseOrder()));
        out.append(Arrays.toString(strs)).append('|');
        try { Arrays.sort(strs, 3, 1); } catch (IllegalArgumentException e) { out.append(e.getMessage()); }
        try { Arrays.sort(strs, 0, 9); } catch (ArrayIndexOutOfBoundsException e) { out.append(e.getMessage()); }
        Object[] mixed = { 1, "x", 2 };
        try { Arrays.sort(mixed); } catch (ClassCastException e) { out.append(" CCE"); }
        List<Integer> mod = new ArrayList<>(Arrays.asList(3, 1, 2));
        try { mod.sort((a, b) -> { mod.add(0); return a - b; }); } catch (ConcurrentModificationException e) { out.append(" CME"); }
        List<Integer> view = Arrays.asList(5, 3, 4);
        view.sort(null);
        out.append(' ').append(view);
        return out.toString();
    }

    /** Default Object.hashCode/toString and System.identityHashCode: consistency only. */
    public static String identity(int seed) {
        Object a = new Object(), b = new E(seed, "x", 0);
        int ha = a.hashCode(), hb = b.hashCode();
        boolean c1 = ha == System.identityHashCode(a) && hb == System.identityHashCode(b);
        boolean c2 = a.toString().equals("java.lang.Object@" + Integer.toHexString(ha));
        boolean c3 = b.toString().startsWith("x");   // E overrides toString
        boolean c4 = ha == a.hashCode() && System.identityHashCode(null) == 0;
        Set<Object> set = new HashSet<>();
        set.add(a); set.add(b); set.add(a);
        Map<Object, Integer> m = new HashMap<>();
        m.put(a, 1); m.put(b, 2);
        return c1 + " " + c2 + " " + c3 + " " + c4 + " " + set.size() + " " + m.get(a) + m.get(b)
            + " " + Integer.toHexString(seed) + " " + Long.toHexString(-seed) + " " + Integer.toBinaryString(seed & 1023)
            + " " + Integer.toOctalString(seed);
    }
}

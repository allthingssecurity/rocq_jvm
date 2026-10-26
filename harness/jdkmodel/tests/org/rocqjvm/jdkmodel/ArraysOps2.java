package org.rocqjvm.jdkmodel;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Collectors;

/** Differential tests of the java.util.Arrays model (all of its public static methods): sorts of
 *  every array type (TimSort's call sequence with logging comparators and Comparable keys,
 *  contract violations, comparators that throw, NaN/-0.0 orders), binarySearch probe sequences,
 *  copyOf/copyOfRange (identities, newType, messages), fill/setAll, equals/compare/mismatch over
 *  ranges, parallelPrefix/parallelSetAll/parallelSort, with nulls and bad ranges. */
public final class ArraysOps2 {
    private ArraysOps2() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    /** Comparator / compareTo log: a call count and a hash of the sequence of (receiver, argument) ids. */
    static int calls;
    static int hash;
    static int limit;   // throw on call number limit (0: never)

    static void log(int a, int b) {
        calls++;
        hash = hash * 31 + a * 1009 + b;
        if (limit != 0 && calls == limit) throw new IllegalStateException("stop at " + calls);
    }

    static void reset() {
        calls = 0;
        hash = 17;
        limit = 0;
    }

    static String logged() {
        return "{" + calls + "/" + hash + "}";
    }

    static final class Key implements Comparable<Key> {
        final int k;
        final int id;
        Key(int k, int id) { this.k = k; this.id = id; }
        public int compareTo(Key o) {
            log(id, o.id);
            return Integer.compare(k, o.k);
        }
        public boolean equals(Object o) {
            log(id, o instanceof Key ? ((Key) o).id : -1);
            return o instanceof Key && ((Key) o).k == k;
        }
        public int hashCode() { return k; }
        public String toString() { return k + "#" + id; }
    }

    static String ex(Throwable e) {
        return "!" + e.getClass().getSimpleName() + ":" + e.getMessage();
    }

    static int[] ints(int n, int range) {
        int[] a = new int[n];
        for (int i = 0; i < n; i++) {
            int k = r(10);
            a[i] = k == 0 ? Integer.MIN_VALUE : k == 1 ? Integer.MAX_VALUE : r(range) - range / 2;
        }
        return a;
    }

    static int size() {
        int k = r(10);
        return k < 4 ? r(8) : k < 8 ? r(40) : r(200);
    }

    static final float[] FS = {Float.NaN, -0.0f, 0.0f, 1.5f, -1.5f, Float.NEGATIVE_INFINITY, Float.POSITIVE_INFINITY, Float.MIN_VALUE, -3f, 7f};
    static final double[] DS = {Double.NaN, -0.0, 0.0, 2.5, -2.5, Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY, Double.MIN_VALUE, -9.0, 1e300};

    static float[] floats(int n) {
        float[] a = new float[n];
        for (int i = 0; i < n; i++) a[i] = r(3) == 0 ? FS[r(FS.length)] : (r(41) - 20) / 4f;
        return a;
    }

    static double[] doubles(int n) {
        double[] a = new double[n];
        for (int i = 0; i < n; i++) a[i] = r(3) == 0 ? DS[r(DS.length)] : (r(41) - 20) / 8.0;
        return a;
    }

    /** A range [from, to) that is mostly valid. */
    static int[] range(int n) {
        int k = r(12);
        if (k == 0) return new int[]{-1, n};
        if (k == 1) return new int[]{0, n + 1};
        if (k == 2) return new int[]{n, n > 0 ? n - 1 : -1};
        int from = r(n + 1), to = from + r(n - from + 1);
        return new int[]{from, to};
    }

    // ---- sorts of primitive arrays ----

    public static String sortPrim(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 6; round++) {
            int n = size();
            boolean par = r(3) == 0, rng = r(3) == 0, nul = r(15) == 0;
            int[] ft = range(n);
            try {
                switch (r(7)) {
                    case 0: {
                        int[] a = nul ? null : ints(n, r(2) == 0 ? 10 : 1000);
                        if (rng) { if (par) Arrays.parallelSort(a, ft[0], ft[1]); else Arrays.sort(a, ft[0], ft[1]); }
                        else { if (par) Arrays.parallelSort(a); else Arrays.sort(a); }
                        out.append(Arrays.toString(a));
                        break;
                    }
                    case 1: {
                        long[] a = null;
                        if (!nul) { a = new long[n]; for (int i = 0; i < n; i++) a[i] = (long) r(1000) * (r(2) == 0 ? 1 : 1L << 40) - 500; }
                        if (rng) { if (par) Arrays.parallelSort(a, ft[0], ft[1]); else Arrays.sort(a, ft[0], ft[1]); }
                        else { if (par) Arrays.parallelSort(a); else Arrays.sort(a); }
                        out.append(Arrays.toString(a));
                        break;
                    }
                    case 2: {
                        short[] a = null;
                        if (!nul) { a = new short[n]; for (int i = 0; i < n; i++) a[i] = (short) (r(70000) - 35000); }
                        if (rng) { if (par) Arrays.parallelSort(a, ft[0], ft[1]); else Arrays.sort(a, ft[0], ft[1]); }
                        else { if (par) Arrays.parallelSort(a); else Arrays.sort(a); }
                        out.append(Arrays.toString(a));
                        break;
                    }
                    case 3: {
                        char[] a = null;
                        if (!nul) { a = new char[n]; for (int i = 0; i < n; i++) a[i] = (char) (r(2) == 0 ? 'a' + r(26) : r(65536)); }
                        if (rng) { if (par) Arrays.parallelSort(a, ft[0], ft[1]); else Arrays.sort(a, ft[0], ft[1]); }
                        else { if (par) Arrays.parallelSort(a); else Arrays.sort(a); }
                        out.append(Arrays.hashCode(a)).append(a == null ? "" : a.length > 0 ? "" + (int) a[0] + "," + (int) a[a.length - 1] : "");
                        break;
                    }
                    case 4: {
                        byte[] a = null;
                        if (!nul) { a = new byte[n]; for (int i = 0; i < n; i++) a[i] = (byte) r(256); }
                        if (rng) { if (par) Arrays.parallelSort(a, ft[0], ft[1]); else Arrays.sort(a, ft[0], ft[1]); }
                        else { if (par) Arrays.parallelSort(a); else Arrays.sort(a); }
                        out.append(Arrays.toString(a));
                        break;
                    }
                    case 5: {
                        float[] a = nul ? null : floats(n);
                        if (rng) { if (par) Arrays.parallelSort(a, ft[0], ft[1]); else Arrays.sort(a, ft[0], ft[1]); }
                        else { if (par) Arrays.parallelSort(a); else Arrays.sort(a); }
                        out.append(Arrays.toString(a));
                        break;
                    }
                    default: {
                        double[] a = nul ? null : doubles(n);
                        if (rng) { if (par) Arrays.parallelSort(a, ft[0], ft[1]); else Arrays.sort(a, ft[0], ft[1]); }
                        else { if (par) Arrays.parallelSort(a); else Arrays.sort(a); }
                        out.append(Arrays.toString(a));
                        break;
                    }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(';');
        }
        return out.toString();
    }

    // ---- sorts of object arrays (TimSort) ----

    static Key[] keys(int n, int range) {
        Key[] a = new Key[n];
        int mode = r(5);
        for (int i = 0; i < n; i++) {
            int k = mode == 0 ? i : mode == 1 ? n - i : mode == 2 ? (i / 7) * (i % 2 == 0 ? 1 : -1) : r(range);
            a[i] = new Key(k, i);
        }
        if (n > 0 && r(8) == 0) a[r(n)] = null;
        return a;
    }

    static Comparator<Key> comparator() {
        switch (r(7)) {
            case 6: return (x, y) -> { log(x.id, y.id); return (x.k % 7 < y.k % 7) ? -1 : 1; };   // never 0: contract violations
            case 0: return (x, y) -> { log(x.id, y.id); return Integer.compare(x.k, y.k); };
            case 1: return (x, y) -> { log(x.id, y.id); return Integer.compare(y.k, x.k); };
            case 2: return (x, y) -> { log(x.id, y.id); return r(3) - 1; };          // inconsistent
            case 3: return (x, y) -> { log(x.id, y.id); return (x.k % 3) - (y.k % 3); };
            case 4: return Comparator.nullsFirst((x, y) -> { log(x.id, y.id); return x.k - y.k; });
            default: return null;
        }
    }

    public static String sortObj(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 4; round++) {
            reset();
            int n = size();
            Key[] a = keys(n, r(2) == 0 ? 5 : 1000);
            if (r(6) == 0) limit = 1 + r(60);
            int[] ft = range(n);
            boolean rng = r(3) == 0;
            try {
                switch (r(6)) {
                    case 0:
                        if (rng) Arrays.sort(a, ft[0], ft[1]); else Arrays.sort(a);
                        break;
                    case 1: case 2: {
                        Comparator<Key> c = comparator();
                        if (rng) Arrays.sort(a, ft[0], ft[1], c); else Arrays.sort(a, c);
                        break;
                    }
                    case 3: {
                        Comparator<Key> c = comparator();
                        if (rng) Arrays.parallelSort(a, ft[0], ft[1], c); else Arrays.parallelSort(a, c);
                        break;
                    }
                    case 4:
                        if (rng) Arrays.parallelSort(a, ft[0], ft[1]); else Arrays.parallelSort(a);
                        break;
                    default: {
                        List<Key> l = Arrays.asList(a);
                        l.sort(comparator());
                        break;
                    }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(logged()).append(Arrays.toString(a)).append(';');
        }
        // natural ordering of JDK classes: Strings, boxes, mixtures (the bridge's ClassCastException), nulls
        Object[] o = new Object[r(40)];
        int mix = r(4);
        for (int i = 0; i < o.length; i++) {
            int k = r(20);
            o[i] = mix == 0 ? (Object) ("s" + k) : mix == 1 ? (Object) Integer.valueOf(k - 10)
                : mix == 2 ? (r(10) == 0 ? (Object) ("x" + k) : (Object) Integer.valueOf(k)) : (r(12) == 0 ? null : (Object) ("t" + k));
        }
        try {
            if (r(2) == 0) Arrays.sort(o);
            else {
                Comparable[] cs = Arrays.copyOf(o, o.length, Comparable[].class);
                o = cs;
                Arrays.parallelSort(cs);
            }
            out.append(Arrays.toString(o));
        } catch (RuntimeException e) {
            out.append(e instanceof NullPointerException && mix == 3 ? "!NPE" : ex(e));
        }
        try {
            Arrays.sort((Object[]) null);
        } catch (RuntimeException e) {
            out.append(ex(e));
        }
        return out.toString();
    }

    // ---- binarySearch ----

    public static String search(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 6; round++) {
            int n = size();
            boolean sorted = r(4) != 0, rng = r(3) == 0, nul = r(15) == 0;
            int[] ft = range(n);
            try {
                switch (r(8)) {
                    case 0: {
                        int[] a = nul ? null : ints(n, 40);
                        if (sorted && a != null) Arrays.sort(a);
                        int key = r(40) - 20;
                        out.append(rng ? Arrays.binarySearch(a, ft[0], ft[1], key) : Arrays.binarySearch(a, key));
                        break;
                    }
                    case 1: {
                        long[] a = new long[n];
                        for (int i = 0; i < n; i++) a[i] = r(30);
                        if (sorted) Arrays.sort(a);
                        out.append(rng ? Arrays.binarySearch(a, ft[0], ft[1], (long) r(30)) : Arrays.binarySearch(a, (long) r(30)));
                        break;
                    }
                    case 2: {
                        char[] a = new char[n];
                        for (int i = 0; i < n; i++) a[i] = (char) ('a' + r(26));
                        if (sorted) Arrays.sort(a);
                        char key = (char) ('a' + r(26));
                        out.append(rng ? Arrays.binarySearch(a, ft[0], ft[1], key) : Arrays.binarySearch(a, key));
                        short[] b = new short[n];
                        for (int i = 0; i < n; i++) b[i] = (short) (r(30) - 15);
                        if (sorted) Arrays.sort(b);
                        out.append(',').append(Arrays.binarySearch(b, (short) (r(30) - 15)));
                        byte[] c = new byte[n];
                        for (int i = 0; i < n; i++) c[i] = (byte) (r(30) - 15);
                        if (sorted) Arrays.sort(c);
                        out.append(',').append(Arrays.binarySearch(c, (byte) (r(30) - 15)));
                        break;
                    }
                    case 3: {
                        float[] a = floats(n);
                        if (sorted) Arrays.sort(a);
                        float key = r(2) == 0 ? FS[r(FS.length)] : (r(41) - 20) / 4f;
                        out.append(rng ? Arrays.binarySearch(a, ft[0], ft[1], key) : Arrays.binarySearch(a, key));
                        break;
                    }
                    case 4: {
                        double[] a = doubles(n);
                        if (sorted) Arrays.sort(a);
                        double key = r(2) == 0 ? DS[r(DS.length)] : (r(41) - 20) / 8.0;
                        out.append(rng ? Arrays.binarySearch(a, ft[0], ft[1], key) : Arrays.binarySearch(a, key));
                        break;
                    }
                    case 5: {
                        reset();
                        Key[] a = keys(n, 30);
                        if (sorted) Arrays.sort(a, Comparator.nullsLast(Comparator.naturalOrder()));
                        reset();
                        Key key = r(10) == 0 ? null : new Key(r(30), 999);
                        out.append(rng ? Arrays.binarySearch(a, ft[0], ft[1], key) : Arrays.binarySearch(a, key)).append(logged());
                        break;
                    }
                    case 6: {
                        reset();
                        Key[] a = keys(n, 30);
                        Comparator<Key> c = comparator();
                        Key key = new Key(r(30), 999);
                        if (c != null && r(10) == 0) a = null;
                        out.append(rng ? Arrays.binarySearch(a, ft[0], ft[1], key, c) : Arrays.binarySearch(a, key, c)).append(logged());
                        break;
                    }
                    default: {
                        Object[] a = new Object[n];
                        for (int i = 0; i < n; i++) a[i] = r(6) == 0 ? (Object) ("s" + i) : r(12) == 0 ? new Object() : (Object) Integer.valueOf(i);
                        Object key = r(3) == 0 ? (Object) "s3" : Integer.valueOf(r(n + 2));
                        out.append(Arrays.binarySearch(a, key));
                        break;
                    }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(';');
        }
        return out.toString();
    }

    // ---- copyOf / copyOfRange ----

    static final Class<?>[] TYPES = {Object[].class, String[].class, Integer[].class, CharSequence[].class, Comparable[].class,
        int[].class, String.class, null, Number[].class, Object[][].class};

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String copies(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 8; round++) {
            int n = r(8);
            int len = r(12) - 2;
            int from = r(10) - 1, to = from + r(10) - 2;
            boolean nul = r(12) == 0;
            try {
                switch (r(10)) {
                    case 0: {
                        int[] a = nul ? null : ints(n, 100);
                        int[] c = r(2) == 0 ? Arrays.copyOf(a, r(3) == 0 ? n : len) : Arrays.copyOfRange(a, r(3) == 0 ? 0 : from, r(3) == 0 ? n : to);
                        out.append(c == a).append(Arrays.toString(c));
                        break;
                    }
                    case 1: {
                        long[] a = nul ? null : new long[n];
                        if (a != null) for (int i = 0; i < n; i++) a[i] = r(100);
                        long[] c = r(2) == 0 ? Arrays.copyOf(a, len) : Arrays.copyOfRange(a, from, to);
                        out.append(Arrays.toString(c));
                        boolean[] z = new boolean[n];
                        z = r(2) == 0 ? Arrays.copyOf(z, r(2) == 0 ? n : len) : Arrays.copyOfRange(z, r(2) == 0 ? 0 : from, r(2) == 0 ? n : to);
                        out.append(Arrays.toString(z));
                        break;
                    }
                    case 2: {
                        byte[] a = new byte[n];
                        short[] b = new short[n];
                        char[] c = new char[n];
                        for (int i = 0; i < n; i++) { a[i] = (byte) i; b[i] = (short) -i; c[i] = (char) ('a' + i); }
                        if (nul) a = null;
                        byte[] a2 = Arrays.copyOfRange(a, r(2) == 0 ? 0 : from, to);
                        out.append(a2 == a).append(Arrays.toString(a2));
                        out.append(Arrays.toString(Arrays.copyOf(b, len))).append(new String(Arrays.copyOfRange(c, from, to)));
                        break;
                    }
                    case 3: {
                        float[] a = floats(n);
                        double[] d = doubles(n);
                        float[] a2 = Arrays.copyOf(a, r(2) == 0 ? n : len);
                        out.append(a2 == a).append(Arrays.toString(a2));
                        double[] d2 = Arrays.copyOfRange(d, r(2) == 0 ? 0 : from, r(2) == 0 ? n : to);
                        out.append(d2 == d).append(Arrays.toString(d2));
                        break;
                    }
                    case 4: case 5: {
                        String[] a = nul ? null : new String[n];
                        if (a != null) for (int i = 0; i < n; i++) a[i] = "s" + i;
                        Object[] c = r(2) == 0 ? Arrays.copyOf(a, r(3) == 0 ? n : len) : Arrays.copyOfRange(a, r(3) == 0 ? 0 : from, r(3) == 0 ? n : to);
                        out.append(c == a).append(c.getClass().getName()).append(Arrays.toString(c));
                        break;
                    }
                    case 6: case 7: {
                        Object[] a = nul ? null : new Object[n];
                        int kind = r(3);
                        if (a != null) for (int i = 0; i < n; i++) a[i] = kind == 0 ? (Object) ("t" + i) : kind == 1 ? (Object) Integer.valueOf(i) : (i % 2 == 0 ? (Object) "u" : Integer.valueOf(i));
                        Class t = TYPES[r(TYPES.length)];
                        Object[] c = r(2) == 0 ? Arrays.copyOf(a, len, t) : Arrays.copyOfRange(a, from, to, t);
                        out.append(c.getClass().getName()).append(Arrays.toString(c));
                        break;
                    }
                    case 8: {
                        Integer[] a = new Integer[n];
                        for (int i = 0; i < n; i++) a[i] = i * 3;
                        Number[] c = Arrays.copyOf(a, len, Number[].class);
                        out.append(c.getClass().getSimpleName()).append(Arrays.toString(c));
                        Integer[] e = Arrays.copyOfRange(a, from, to);
                        out.append(e.getClass().getSimpleName()).append(Arrays.toString(e));
                        break;
                    }
                    default: {
                        char[] a = nul ? null : "hello".toCharArray();
                        out.append(Arrays.toString(Arrays.copyOfRange(a, from, to)));
                        break;
                    }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(';');
        }
        return out.toString();
    }

    // ---- fill / setAll ----

    public static String fills(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 8; round++) {
            int n = r(9);
            int[] ft = range(n);
            boolean rng = r(2) == 0, nul = r(12) == 0;
            try {
                switch (r(11)) {
                    case 0: { int[] a = nul ? null : new int[n]; if (rng) Arrays.fill(a, ft[0], ft[1], 7); else Arrays.fill(a, -3); out.append(Arrays.toString(a)); break; }
                    case 1: { long[] a = nul ? null : new long[n]; if (rng) Arrays.fill(a, ft[0], ft[1], 7L << 40); else Arrays.fill(a, -3L); out.append(Arrays.toString(a)); break; }
                    case 2: { short[] a = nul ? null : new short[n]; if (rng) Arrays.fill(a, ft[0], ft[1], (short) 9); else Arrays.fill(a, (short) -9); out.append(Arrays.toString(a)); break; }
                    case 3: { char[] a = nul ? null : new char[n]; if (rng) Arrays.fill(a, ft[0], ft[1], 'x'); else Arrays.fill(a, 'y'); out.append(Arrays.toString(a)); break; }
                    case 4: { byte[] a = nul ? null : new byte[n]; if (rng) Arrays.fill(a, ft[0], ft[1], (byte) 5); else Arrays.fill(a, (byte) -5); out.append(Arrays.toString(a)); break; }
                    case 5: { boolean[] a = nul ? null : new boolean[n]; if (rng) Arrays.fill(a, ft[0], ft[1], true); else Arrays.fill(a, true); out.append(Arrays.toString(a)); break; }
                    case 6: { float[] a = nul ? null : new float[n]; double[] d = new double[n];
                        if (rng) { Arrays.fill(a, ft[0], ft[1], -0.0f); Arrays.fill(d, ft[0], ft[1], Double.NaN); } else { Arrays.fill(a, 2.5f); Arrays.fill(d, -0.0); }
                        out.append(Arrays.toString(a)).append(Arrays.toString(d)); break; }
                    case 7: { Object[] a = nul ? null : r(2) == 0 ? new String[n] : new Object[n];
                        Object v = r(3) == 0 ? (Object) Integer.valueOf(4) : r(4) == 0 ? null : "v";
                        if (rng) Arrays.fill(a, ft[0], ft[1], v); else Arrays.fill(a, v);
                        out.append(Arrays.toString(a)); break; }
                    case 8: { reset(); Object[] a = nul ? null : r(2) == 0 ? new String[n] : new Object[n];
                        if (r(8) == 0) limit = 1 + r(4);
                        Arrays.setAll(a, r(10) == 0 ? null : i -> { log(i, 0); return i % 3 == 2 && r(4) == 0 ? (Object) Integer.valueOf(i) : "g" + i; });
                        out.append(Arrays.toString(a)).append(logged()); break; }
                    case 9: { reset(); int[] a = nul ? null : new int[n]; long[] b = new long[n]; double[] c = new double[n];
                        Arrays.setAll(a, i -> { log(i, 1); return i * i; });
                        Arrays.setAll(b, i -> { log(i, 2); return (long) i << 33; });
                        Arrays.setAll(c, i -> { log(i, 3); return i / 2.0; });
                        out.append(Arrays.toString(a)).append(Arrays.toString(b)).append(Arrays.toString(c)).append(logged()); break; }
                    default: { int[] a = new int[n]; Arrays.setAll(a, null); break; }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(';');
        }
        return out.toString();
    }

    // ---- equals / compare / compareUnsigned / mismatch ----

    static String eqcmp(int t, int n1, int n2, boolean rng, int[] f1, int[] f2) {
        // two arrays of type t with a common prefix
        int common = r(Math.min(n1, n2) + 1);
        int[] x = ints(n1, 6), y = ints(n2, 6);
        for (int i = 0; i < common; i++) y[i] = x[i];
        StringBuilder out = new StringBuilder();
        switch (t) {
            case 0: {
                int[] a = x, b = r(10) == 0 ? a : y;
                if (r(12) == 0) a = null;
                if (rng) out.append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1]))
                    .append(Arrays.compareUnsigned(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1]));
                else out.append(Arrays.equals(a, b)).append(Arrays.compare(a, b)).append(Arrays.compareUnsigned(a, b)).append(Arrays.mismatch(a, b));
                break;
            }
            case 1: {
                long[] a = new long[n1], b = new long[n2];
                for (int i = 0; i < n1; i++) a[i] = (long) x[i] << 32 | (x[i] & 7);
                for (int i = 0; i < n2; i++) b[i] = (long) y[i] << 32 | (y[i] & 7);
                if (rng) out.append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1]))
                    .append(Arrays.compareUnsigned(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1]));
                else out.append(Arrays.equals(a, b)).append(Arrays.compare(a, b)).append(Arrays.compareUnsigned(a, b)).append(Arrays.mismatch(a, b));
                break;
            }
            case 2: {
                short[] a = new short[n1], b = new short[n2];
                for (int i = 0; i < n1; i++) a[i] = (short) (x[i] * 9000);
                for (int i = 0; i < n2; i++) b[i] = (short) (y[i] * 9000);
                if (rng) out.append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1]))
                    .append(Arrays.compareUnsigned(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1]));
                else out.append(Arrays.equals(a, b)).append(Arrays.compare(a, b)).append(Arrays.compareUnsigned(a, b)).append(Arrays.mismatch(a, b));
                break;
            }
            case 3: {
                byte[] a = new byte[n1], b = new byte[n2];
                for (int i = 0; i < n1; i++) a[i] = (byte) (x[i] * 50);
                for (int i = 0; i < n2; i++) b[i] = (byte) (y[i] * 50);
                if (r(12) == 0) b = null;
                if (rng) out.append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1]))
                    .append(Arrays.compareUnsigned(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1]));
                else out.append(Arrays.equals(a, b)).append(Arrays.compare(a, b)).append(Arrays.compareUnsigned(a, b)).append(Arrays.mismatch(a, b));
                break;
            }
            case 4: {
                char[] a = new char[n1], b = new char[n2];
                boolean[] p = new boolean[n1], q = new boolean[n2];
                for (int i = 0; i < n1; i++) { a[i] = (char) ('m' + x[i]); p[i] = x[i] > 0; }
                for (int i = 0; i < n2; i++) { b[i] = (char) ('m' + y[i]); q[i] = y[i] > 0; }
                if (rng) out.append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1]))
                    .append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.equals(p, f1[0], f1[1], q, f2[0], f2[1]))
                    .append(Arrays.compare(p, f1[0], f1[1], q, f2[0], f2[1])).append(Arrays.mismatch(p, f1[0], f1[1], q, f2[0], f2[1]));
                else out.append(Arrays.equals(a, b)).append(Arrays.compare(a, b)).append(Arrays.mismatch(a, b))
                    .append(Arrays.equals(p, q)).append(Arrays.compare(p, q)).append(Arrays.mismatch(p, q));
                break;
            }
            case 5: {
                float[] a = new float[n1], b = new float[n2];
                for (int i = 0; i < n1; i++) a[i] = FS[Math.floorMod(x[i], FS.length)];
                for (int i = 0; i < n2; i++) b[i] = FS[Math.floorMod(y[i], FS.length)];
                if (rng) out.append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1]))
                    .append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1]));
                else out.append(Arrays.equals(a, b)).append(Arrays.compare(a, b)).append(Arrays.mismatch(a, b));
                break;
            }
            case 6: {
                double[] a = new double[n1], b = new double[n2];
                for (int i = 0; i < n1; i++) a[i] = DS[Math.floorMod(x[i], DS.length)];
                for (int i = 0; i < n2; i++) b[i] = DS[Math.floorMod(y[i], DS.length)];
                if (rng) out.append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1]))
                    .append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1]));
                else out.append(Arrays.equals(a, b)).append(Arrays.compare(a, b)).append(Arrays.mismatch(a, b));
                break;
            }
            default: {
                reset();
                Key[] a = new Key[n1], b = new Key[n2];
                for (int i = 0; i < n1; i++) a[i] = x[i] == 3 ? null : new Key(x[i], i);
                for (int i = 0; i < n2; i++) b[i] = i < common && r(2) == 0 ? a[i] : y[i] == 3 ? null : new Key(y[i], 100 + i);
                Comparator<Key> c = Comparator.nullsLast((u, v) -> { log(u.id, v.id); return u.k - v.k; });
                if (r(10) == 0) c = null;
                if (rng) out.append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1])).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1]))
                    .append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1])).append(logged())
                    .append(Arrays.equals(a, f1[0], f1[1], b, f2[0], f2[1], c)).append(Arrays.compare(a, f1[0], f1[1], b, f2[0], f2[1], c))
                    .append(Arrays.mismatch(a, f1[0], f1[1], b, f2[0], f2[1], c));
                else out.append(Arrays.equals(a, b)).append(Arrays.compare(a, b)).append(Arrays.mismatch(a, b)).append(logged())
                    .append(Arrays.equals(a, b, c)).append(Arrays.compare(a, b, c)).append(Arrays.mismatch(a, b, c));
                out.append(logged());
                break;
            }
        }
        return out.toString();
    }

    public static String compares(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 8; round++) {
            int n1 = r(10), n2 = r(10);
            boolean rng = r(3) == 0;
            int[] f1 = range(n1), f2 = range(n2);
            try {
                out.append(eqcmp(r(8), n1, n2, rng, f1, f2));
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(';');
        }
        try {
            out.append(Arrays.compare((int[]) null, (int[]) null)).append(Arrays.compare(null, new int[0])).append(Arrays.compare(new long[0], null))
               .append(Arrays.equals((Object[]) null, new Object[0])).append(Arrays.compare((String[]) null, new String[0]))
               .append(Arrays.mismatch(new int[0], (int[]) null));
        } catch (RuntimeException e) {
            out.append(ex(e));
        }
        try {
            out.append(Arrays.compare(new Comparable[]{"a", 1}, new Comparable[]{"a", "b"}));
        } catch (RuntimeException e) {
            out.append(ex(e));
        }
        return out.toString();
    }

    // ---- parallelPrefix / parallelSetAll / parallelSort ----

    public static String parallel(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 6; round++) {
            reset();
            int n = r(60) == 0 ? 17 + r(4) : r(17);
            int[] ft = range(n);
            boolean rng = r(3) == 0, nul = r(15) == 0;
            if (r(8) == 0) limit = 1 + r(5);
            try {
                switch (r(6)) {
                    case 0: {
                        int[] a = nul ? null : ints(n, 20);
                        if (rng) Arrays.parallelPrefix(a, ft[0], ft[1], (x, y) -> { log(x, y); return x + y; });
                        else Arrays.parallelPrefix(a, r(10) == 0 ? null : (x, y) -> { log(x, y); return x * 3 - y; });
                        out.append(Arrays.toString(a));
                        break;
                    }
                    case 1: {
                        long[] a = new long[n];
                        for (int i = 0; i < n; i++) a[i] = r(50);
                        if (rng) Arrays.parallelPrefix(a, ft[0], ft[1], (x, y) -> { log((int) x, (int) y); return Math.max(x, y); });
                        else Arrays.parallelPrefix(a, (x, y) -> { log((int) x, (int) y); return x - y; });
                        out.append(Arrays.toString(a));
                        break;
                    }
                    case 2: {
                        double[] a = doubles(n);
                        if (rng) Arrays.parallelPrefix(a, ft[0], ft[1], (x, y) -> { log((int) x, (int) y); return x + y; });
                        else Arrays.parallelPrefix(a, (x, y) -> { log((int) x, (int) y); return x * y; });
                        out.append(Arrays.toString(a));
                        break;
                    }
                    case 3: {
                        String[] a = nul ? null : new String[n];
                        if (a != null) for (int i = 0; i < n; i++) a[i] = "" + (char) ('a' + r(26));
                        if (rng) Arrays.parallelPrefix(a, ft[0], ft[1], (x, y) -> { log(x.length(), y.length()); return x + y; });
                        else Arrays.parallelPrefix(a, (x, y) -> { log(x.length(), y.length()); return y + x; });
                        out.append(Arrays.toString(a));
                        break;
                    }
                    case 4: {
                        int m = r(30) == 0 ? 2 : r(2);
                        Object[] a = new Object[m];
                        int[] b = new int[m];
                        long[] c = new long[m];
                        double[] d = new double[m];
                        Arrays.parallelSetAll(a, i -> { log(i, 7); return "p" + i; });
                        Arrays.parallelSetAll(b, i -> { log(i, 8); return i - 4; });
                        Arrays.parallelSetAll(c, i -> { log(i, 9); return 5L * i; });
                        Arrays.parallelSetAll(d, i -> { log(i, 10); return i * 0.5; });
                        out.append(Arrays.toString(a)).append(Arrays.toString(b)).append(Arrays.toString(c)).append(Arrays.toString(d));
                        break;
                    }
                    default: {
                        int[] a = null;
                        Arrays.parallelSetAll(a, r(2) == 0 ? null : i -> i);
                        break;
                    }
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(logged()).append(';');
        }
        return out.toString();
    }

    // ---- asList / stream / hashCode / toString ----

    public static String misc(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int n = r(6);
        Integer[] a = new Integer[n];
        for (int i = 0; i < n; i++) a[i] = r(4) == 0 ? null : r(20);
        List<Integer> l = Arrays.asList(a);
        out.append(l).append(l.size()).append(l.hashCode()).append(Arrays.hashCode(a)).append(Arrays.deepHashCode(a)).append(';');
        try {
            out.append(Arrays.stream(a).filter(x -> x != null).map(x -> x * 2).collect(Collectors.toList()));
            out.append(Arrays.stream(new int[]{3, 1, 2}, r(3), 3).sum()).append(Arrays.stream(new long[]{r(9), 4}).max().getAsLong());
            out.append(Arrays.stream(new double[]{1.5, r(3)}).sum());
        } catch (RuntimeException e) {
            out.append(ex(e));
        }
        Object[] nulls = {null};
        try {
            switch (r(4)) {
                case 0: Arrays.stream((Object[]) nulls[0]); break;
                case 1: Arrays.stream((int[]) nulls[0]); break;
                case 2: Arrays.stream((long[]) nulls[0]); break;
                default: Arrays.stream((double[]) nulls[0]); break;
            }
        } catch (RuntimeException e) {
            out.append(ex(e));
        }
        try {
            Arrays.asList((Object[]) nulls[0]);
        } catch (RuntimeException e) {
            out.append(ex(e));
        }
        try {
            Arrays.stream(new int[3], 2, r(5));
        } catch (RuntimeException e) {
            out.append(ex(e));
        }
        Object[] deep = {a, new int[]{n}, new Object[]{null, "x"}, null};
        out.append(Arrays.deepToString(deep)).append(Arrays.deepEquals(deep, deep.clone())).append(Arrays.equals(deep, deep.clone()));
        reset();
        Key[] k1 = {new Key(1, 1), new Key(2, 2)}, k2 = {k1[0], new Key(2, 3)};
        out.append(Arrays.equals(k1, k2)).append(logged()).append(Arrays.mismatch(k1, k2)).append(logged());
        return out.toString();
    }
}

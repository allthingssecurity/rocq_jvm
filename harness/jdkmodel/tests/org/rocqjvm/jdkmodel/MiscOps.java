package org.rocqjvm.jdkmodel;

import java.util.Comparator;
import java.util.Objects;

/** Differential tests of System.arraycopy's checks and messages and of java.util.Objects
 *  (callbacks into equals/hashCode/toString/Supplier, messages of requireNonNull*, checkIndex). */
public final class MiscOps {
    private MiscOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static final class P {
        final int v;
        P(int v) { this.v = v; }
        @Override public boolean equals(Object o) { return o instanceof P && ((P) o).v == v; }
        @Override public int hashCode() { return v * 7 + 1; }
        @Override public String toString() { return "P" + v; }
    }

    static Object arr(int k) {
        switch (k) {
            case 0: return new int[3 + r(3)];
            case 1: return new long[2 + r(3)];
            case 2: return new Object[] {"a", 1, "b", null};
            case 3: return new String[3 + r(2)];
            case 4: return new Integer[] {1, 2, 3};
            case 5: return new char[4];
            case 6: return "notAnArray";
            case 7: return null;
            case 8: return new Number[3];
            default: return new int[][] {{1}, {2}};
        }
    }

    static String show(Object[] a) {
        StringBuilder b = new StringBuilder("[");
        for (Object o : a) b.append(o != null && o.getClass().isArray() ? o.getClass().getName() : String.valueOf(o)).append(',');
        return b.append(']').toString();
    }

    public static String arraycopy(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            Object src = arr(r(10)), dst = arr(r(10));
            int sp = r(6) - 1, dp = r(6) - 1, n = r(6) - 1;
            try {
                System.arraycopy(src, sp, dst, dp, n);
                out.append("ok");
                if (dst instanceof Object[]) out.append(show((Object[]) dst));
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
                if (dst instanceof Object[]) out.append(show((Object[]) dst));
            }
            out.append(';');
        }
        return out.toString();
    }

    static Object obj() {
        switch (r(6)) {
            case 0: return null;
            case 1: return new P(r(3));
            case 2: return "s" + r(3);
            case 3: return r(3);
            case 4: return new P(r(3));
            default: return (long) r(3);
        }
    }

    public static String objects(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        Comparator<Object> cmp = (a, b) -> String.valueOf(a).compareTo(String.valueOf(b));
        for (int k = 0; k < 8; k++) {
            Object a = obj(), b = obj();
            try {
                switch (r(12)) {
                    case 0: out.append(Objects.equals(a, b)); break;
                    case 1: out.append(Objects.hashCode(a)); break;
                    case 2: out.append(Objects.hash(a, b, "x")); break;
                    case 3: out.append(Objects.toString(a)).append(Objects.toString(b, "dflt")); break;
                    case 4: out.append(Objects.requireNonNull(a)); break;
                    case 5: out.append(Objects.requireNonNull(a, "msg" + k)); break;
                    case 6: out.append(Objects.requireNonNull(a, () -> "supplied" + b)); break;
                    case 7: out.append(Objects.requireNonNullElse(a, b)); break;
                    case 8: out.append(Objects.isNull(a)).append(Objects.nonNull(b)); break;
                    case 9: out.append(Objects.compare(a, b, cmp)); break;
                    case 10: out.append(Objects.checkIndex(r(5) - 1, r(4))); break;
                    default: out.append(Objects.equals(a, a)).append(Objects.hash()); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }
}

package org.rocqjvm.jdkmodel;

/** Differential tests of String.format / String.formatted: random format strings (valid and
 *  invalid specifiers) over random arguments; the result, or the exception class and message. */
public final class FmtOps {
    private FmtOps() {
    }

    static final class Obj {
        final int v;
        Obj(int v) { this.v = v; }
        public String toString() { return "Obj" + v; }
        public int hashCode() { return v * 31 + 7; }
    }

    static int s;

    static int r(int n) {
        s = s * 1103515245 + 12345;
        return ((s >>> 8) & 0x7fffff) % n;
    }

    static Object arg() {
        switch (r(11)) {
            case 0: return null;
            case 1: return r(2000) - 1000;
            case 2: return (long) (r(2000000) - 1000000) * 1000003L;
            case 3: return (short) (r(70000) - 35000);
            case 4: return (byte) (r(256) - 128);
            case 5: return (char) ('a' + r(26));
            case 6: return r(2) == 0;
            case 7: return "str" + r(100);
            case 8: return new Obj(r(50));
            case 9: return Integer.MIN_VALUE + r(3);
            default: return r(10);
        }
    }

    static String spec() {
        StringBuilder b = new StringBuilder("%");
        if (r(6) == 0) b.append(1 + r(4)).append('$');
        String fl = "-#+ 0,(<";
        int nf = r(6) == 0 ? 1 + r(2) : 0;
        for (int i = 0; i < nf; i++) b.append(fl.charAt(r(fl.length())));
        if (r(3) == 0) b.append(r(13));
        if (r(12) == 0) b.append('.').append(r(10) == 0 ? "" : String.valueOf(r(6)));
        String conv = r(12) == 0 ? "DOqt%n" : "ssssddddxxXcbBhHSo";
        b.append(conv.charAt(r(conv.length())));
        return b.toString();
    }

    public static String format(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int rounds = 3 + r(6);
        for (int k = 0; k < rounds; k++) {
            StringBuilder f = new StringBuilder();
            int pieces = 1 + r(4);
            for (int i = 0; i < pieces; i++) {
                if (r(3) == 0) f.append("ab".substring(0, r(3)));
                f.append(spec());
            }
            if (r(10) == 0) f.append('%');
            Object[] args = new Object[pieces + r(3) - 1];
            for (int i = 0; i < args.length; i++) args[i] = arg();
            try {
                String res = (r(4) == 0) ? f.toString().formatted(args) : String.format(f.toString(), args);
                out.append('[').append(res).append(']');
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    /** Typical uses: padding, zero padding, grouping, hex dumps, null arguments. */
    public static String common(int n) {
        int a = n % 100000;
        return String.format("%5d|%-5d|%05d|%,d|%x|%08X|%+d|% d|%(d|%s|%10s|%-10s|%.3s|%b|%c|%%|%n",
            a, a, a, n, n, n, a, a, -a, "v" + a, "r", "l", "truncated", n > 0, (char) ('A' + (a & 15)))
            + String.format("%2$s-%1$s-%<s %s", "x", "y")
            + String.format("%s %d", null, null)
            + String.format("%h %H", "hi" + a, a)
            + String.format("%o %#o %#x", (byte) n, n, (long) n);
    }
}

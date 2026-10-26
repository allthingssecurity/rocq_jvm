package org.rocqjvm.jdkmodel;

/** Differential tests of String.format's floating-point conversions (e E f g G): random flags,
 *  widths and precisions over random doubles and floats (incl. NaN, infinities, -0.0, subnormals,
 *  halfway cases), null and wrong argument types, and the specifier errors. */
public final class FmtFloatOps {
    private FmtFloatOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static long rl() { return ((long) r(1 << 22) << 42) ^ ((long) r(1 << 22) << 20) ^ r(1 << 20); }

    static final double[] SPECIAL = {0.0, -0.0, 1.0, -1.0, 0.5, 2.5, 0.125, 2.675, 1.005, 0.045, 9.995, 99.5, 999999.5, 1e7, 1e-5,
        0.0001, 123456789.0, Double.NaN, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY, Double.MIN_VALUE, Double.MAX_VALUE,
        1e-300, 1e300, 3.14159265358979, -2.5e-7, 5e-5, 9.9999995, 0.95, 1234.5678};

    static Object arg() {
        switch (r(10)) {
            case 0: return Double.longBitsToDouble(rl());
            case 1: case 2: return SPECIAL[r(SPECIAL.length)];
            case 3: return (r(200000) - 100000) / 64.0;
            case 4: return (float) ((r(20000) - 10000) / 16.0);
            case 5: return Float.intBitsToFloat(r(1 << 22) << 10 ^ r(1 << 10));
            case 6: return r(10) == 0 ? null : (Object) Integer.valueOf(r(100));
            case 7: return (r(2000000) - 1000000) / 1000.0;
            default: return SPECIAL[r(SPECIAL.length)] * (r(2) == 0 ? 1 : -1);
        }
    }

    static String spec() {
        StringBuilder b = new StringBuilder("%");
        String flags = "-#+ 0,(";
        for (int k = r(3); k > 0; k--) b.append(flags.charAt(r(flags.length())));
        if (r(2) == 0) b.append(1 + r(20));
        if (r(3) != 0) b.append('.').append(r(r(4) == 0 ? 20 : 5));
        b.append("efgEG".charAt(r(5)));
        return b.toString();
    }

    public static String fmt(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            String f = spec();
            Object a = arg();
            out.append(f).append('|');
            try {
                out.append(String.format(f, a));
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String common(int seed) {
        s = seed;
        double d = (r(2000000) - 1000000) / 997.0;
        float f = (float) d;
        return String.format("%.2f %.3f %10.4f %-10.1f| %e %.0e %g %.3g %,.2f %(.2f %+.1f %08.2f %.0f %#.0f %s %s",
            d, d, d, d, d, d, d, d, d * 1000, d, d, d, d, d, d, f)
            + String.format("|%.1f %.2f %.5f %f", 0.05, 0.005, 1e-6, f);
    }

    /** %a / %A and Double/Float.toHexString. */
    public static String hex(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            StringBuilder b = new StringBuilder("%");
            String flags = "-#+ 0,(";
            for (int j = r(3); j > 0; j--) b.append(flags.charAt(r(flags.length())));
            if (r(2) == 0) b.append(1 + r(30));
            if (r(2) != 0) b.append('.').append(r(r(4) == 0 ? 16 : 6));
            b.append(r(3) == 0 ? 'A' : 'a');
            String f = b.toString();
            Object a = arg();
            out.append(f).append('|');
            try {
                out.append(String.format(f, a));
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            if (a instanceof Double) out.append('|').append(Double.toHexString((Double) a));
            if (a instanceof Float) out.append('|').append(Float.toHexString((Float) a));
            out.append(';');
        }
        double sub = Double.longBitsToDouble(r(1 << 30));
        out.append(String.format("%.3a %.1a %a %.12a %.13a", sub, Double.MAX_VALUE, Float.MIN_VALUE, 1.0 / 3, -0.0))
           .append(Float.toHexString(Float.intBitsToFloat(r(1 << 23)))).append(Float.toHexString(-Float.MAX_VALUE));
        return out.toString();
    }

    /** BigInteger (d o x X) and BigDecimal (e f g E G, and the a conversion error) arguments. */
    public static String bigs(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        String flags = "-#+ 0,(";
        for (int k = 0; k < 10; k++) {
            boolean dec = r(2) == 0;
            StringBuilder b = new StringBuilder("%");
            for (int j = r(3); j > 0; j--) b.append(flags.charAt(r(flags.length())));
            if (r(2) == 0) b.append(1 + r(25));
            if (dec && r(3) != 0) b.append('.').append(r(r(4) == 0 ? 25 : 6));
            b.append(dec ? "efgEGa".charAt(r(6)) : "doxXd".charAt(r(5)));
            String f = b.toString();
            Object a;
            if (dec) {
                StringBuilder u = new StringBuilder(r(4) == 0 ? "-" : "");
                for (int j = 1 + r(r(3) == 0 ? 30 : 8); j > 0; j--) u.append((char) ('0' + (j == 1 || r(4) != 0 ? r(10) : 0)));
                java.math.BigDecimal bd = new java.math.BigDecimal(new java.math.BigInteger(u.toString()), r(30) - 12);
                a = r(8) == 0 ? java.math.BigDecimal.ZERO.setScale(r(6) - 2) : bd;
            } else {
                StringBuilder u = new StringBuilder(r(3) == 0 ? "-" : "");
                for (int j = 1 + r(30); j > 0; j--) u.append((char) ('0' + r(10)));
                a = new java.math.BigInteger(u.toString());
            }
            out.append(f).append('|');
            try {
                out.append(String.format(f, a));
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }
}

package org.rocqjvm.jdkmodel;

/** Differential tests of the decimal conversions of double and float (JDK 21): Double/Float.toString
 *  through every route (static, String.valueOf, StringBuilder.append, string concatenation, the
 *  boxes' toString, records), and parseDouble/parseFloat/valueOf with their NumberFormatException
 *  messages, over random bit patterns, short decimals, boundaries and malformed strings. */
public final class FloatStrOps {
    private FloatStrOps() {
    }

    record P(double x, float y) { }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static long rl() { return ((long) r(1 << 22) << 42) ^ ((long) r(1 << 22) << 20) ^ r(1 << 20); }

    static double pow10(int e) { double x = 1; if (e >= 0) { for (int i = 0; i < e; i++) x *= 10; } else { for (int i = 0; i < -e; i++) x /= 10; } return x; }
    static double pow2(int e) { double x = 1; if (e >= 0) { for (int i = 0; i < e; i++) x *= 2; } else { for (int i = 0; i < -e; i++) x /= 2; } return x; }
    static double up(double x) { return Double.longBitsToDouble(Double.doubleToRawLongBits(x) + 1); }

    static double rd() {
        switch (r(8)) {
            case 0: return Double.longBitsToDouble(rl());
            case 1: return (r(2000) - 1000) / 8.0;
            case 2: return r(100000) / pow10(r(12));
            case 3: return pow10(r(40) - 20) * (r(2) == 0 ? 1 : -1);
            case 4: { double[] e = {0.0, -0.0, Double.NaN, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY, Double.MIN_VALUE,
                                     Double.MAX_VALUE, Double.MIN_NORMAL, 1e7, 9999999.999, 0.001, 0.00099999, 1e-3, 1e23, 2e22, 5e-324, 1.0};
                      return e[r(e.length)]; }
            case 5: return Double.longBitsToDouble(rl() & 0x000fffffffffffffL);   // subnormal
            case 6: return (double) r(1 << 22) * pow2(r(200) - 100);
            default: return up(r(1000) / 10.0);
        }
    }

    static float rf() {
        switch (r(6)) {
            case 0: return Float.intBitsToFloat(r(1 << 22) << 10 ^ r(1 << 10));
            case 1: return (r(2000) - 1000) / 16f;
            case 2: return r(100000) / (float) pow10(r(9));
            case 3: { float[] e = {0f, -0f, Float.NaN, Float.POSITIVE_INFINITY, Float.MIN_VALUE, Float.MAX_VALUE, Float.MIN_NORMAL, 1e7f, 1.1f, 0.1f, 100f, 1e-3f};
                      return e[r(e.length)]; }
            case 4: return Float.intBitsToFloat(r(1 << 23));
            default: return (float) rd();
        }
    }

    public static String toStr(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            double d = rd();
            float f = rf();
            out.append(Double.toString(d)).append('|').append(String.valueOf(f)).append('|');
            out.append(d).append('|').append(f).append('|');
            String c = "d=" + d + ",f=" + f + ";";
            out.append(c);
            Double bd = d;
            Float bf = f;
            out.append(bd.toString()).append(bf).append(String.valueOf((Object) bd)).append(new P(d, f)).append('\n');
        }
        return out.toString();
    }

    static final String[] STRS = {"1.0", "0.1", "100", "1e23", "2e-3", "1.0E7", "-0.0", "+5", "NaN", "-NaN", "Infinity", "-Infinity",
        "+Infinity", "infinity", "nan", "", "   ", "1..2", ".", ".5", "5.", "-", "+", "1e", "1e+", "1e-5", "1E5", "1.5f", "1.5D",
        "1.5ff", "0x1p0", "0x1.8p1", "-0x.8p-1", "0x1.p", "0X10P-4", "0x1p2147483648", "0x1p-2147483649", "0x0p99", "0x.p1",
        "0x1.fffffffffffffp1023", "0x1.fffffffffffff8p1023", "0x1p-1075", "0x1.0000000000001p-1075", "0x1p-1074", "1_0",
        "00012.50e002", "0e999999999999", "1e999999999999", "1e-999999999999", "3.4028235e38", "3.4028236e38", "1.4e-45",
        "7.0e-46", "7.1e-46", "0x1.fffffep127", "0x1.ffffffp127", "\t12 ", "1e0001", "4.9e-324", "2.4703282292062328e-324",
        "2.4703282292062327e-324", "1.7976931348623158e308", "1.7976931348623159e308", "12345678901234567890123", "0.30000000000000004",
        " 1e1 ", "1e1x", "0x", "0x1", "1,5", "--1", "1e--1", "9007199254740993", "9007199254740992.5"};

    public static String parse(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 8; k++) {
            String t;
            switch (r(4)) {
                case 0: t = STRS[r(STRS.length)]; break;
                case 1: { StringBuilder b = new StringBuilder(); if (r(3) == 0) b.append(r(2) == 0 ? '-' : '+');
                          for (int i = r(20); i > 0; i--) b.append("0123456789000.eE+-fdx ".charAt(r(22))); t = b.toString(); break; }
                case 2: { StringBuilder b = new StringBuilder(); for (int i = 1 + r(18); i > 0; i--) b.append((char) ('0' + r(10)));
                          if (r(2) == 0) b.insert(r(b.length()), '.'); b.append('e').append(r(700) - 350); t = b.toString(); break; }
                default: t = Double.toString(rd()); break;
            }
            try {
                double d = Double.parseDouble(t);
                out.append(Double.doubleToRawLongBits(d)).append(',').append(Double.valueOf(t));
            } catch (NumberFormatException e) {
                out.append("!NFE:").append(e.getMessage());
            }
            out.append(' ');
            try {
                float f = Float.parseFloat(t);
                out.append(Float.floatToRawIntBits(f)).append(',').append(Float.valueOf(t));
            } catch (NumberFormatException e) {
                out.append("!NFE:").append(e.getMessage());
            }
            out.append(';');
        }
        try {
            Double.parseDouble(null);
        } catch (NullPointerException e) {
            out.append(e.getMessage());
        }
        return out.toString();
    }
}

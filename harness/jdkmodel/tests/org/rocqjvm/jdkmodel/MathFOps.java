package org.rocqjvm.jdkmodel;

/** Differential tests of java.lang.Math / StrictMath on double and float: the methods the
 *  specification fixes exactly, over random bit patterns, small integers, halves, boundaries
 *  and special values (results printed with Double.toString and doubleToLongBits). */
public final class MathFOps {
    private MathFOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static long rl() { return ((long) r(1 << 22) << 42) ^ ((long) r(1 << 22) << 20) ^ r(1 << 20); }

    static final double[] SPECIAL = {0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 1.5, -1.5, 2.5, -2.5, Double.NaN, Double.POSITIVE_INFINITY,
        Double.NEGATIVE_INFINITY, Double.MIN_VALUE, -Double.MIN_VALUE, Double.MAX_VALUE, -Double.MAX_VALUE, Double.MIN_NORMAL,
        0.49999999999999994, 4503599627370496.5, 9007199254740993.0, 1e20, -1e20, 9.223372036854776E18, 2.0, 3.0, 10.0, -2.0, 0.1, 1e-300, 1e300};

    static double rd() {
        switch (r(6)) {
            case 0: return Double.longBitsToDouble(rl());
            case 1: return SPECIAL[r(SPECIAL.length)];
            case 2: return (r(4000) - 2000) / 4.0;
            case 3: return r(64) - 32;
            case 4: return Double.longBitsToDouble(rl() & 0x000fffffffffffffL) * (r(2) == 0 ? 1 : -1);
            default: return (r(2000000) - 1000000) / 1024.0;
        }
    }

    static float rf() {
        switch (r(4)) {
            case 0: return Float.intBitsToFloat(r(1 << 22) << 10 ^ r(1 << 10));
            case 1: return (float) SPECIAL[r(SPECIAL.length)];
            case 2: return (r(4000) - 2000) / 4f;
            default: return r(64) - 32;
        }
    }

    static String d(double x) { return Double.toString(x) + "/" + Long.toHexString(Double.doubleToLongBits(x)); }
    static String f(float x) { return Float.toString(x) + "/" + Integer.toHexString(Float.floatToIntBits(x)); }

    public static String dbl(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            double a = rd(), b = rd(), c = rd();
            out.append(d(a)).append(' ').append(d(b)).append(':');
            out.append(d(Math.abs(a))).append(',').append(d(Math.signum(a))).append(',').append(d(Math.floor(a))).append(',')
               .append(d(Math.ceil(a))).append(',').append(d(Math.rint(a))).append(',').append(Math.round(a)).append(',')
               .append(d(Math.sqrt(a))).append(',').append(d(Math.ulp(a))).append(',').append(d(Math.nextUp(a))).append(',')
               .append(d(Math.nextDown(a))).append(',').append(Math.getExponent(a)).append(',').append(d(Math.toRadians(a))).append(',')
               .append(d(Math.toDegrees(a))).append(',').append(d(Math.max(a, b))).append(',').append(d(Math.min(a, b))).append(',')
               .append(d(Math.copySign(a, b))).append(',').append(d(StrictMath.copySign(a, b))).append(',')
               .append(d(Math.IEEEremainder(a, b))).append(',').append(d(Math.nextAfter(a, b))).append(',')
               .append(d(Math.fma(a, b, c))).append(',').append(d(Math.scalb(a, r(2200) - 1100))).append(',')
               .append(d(StrictMath.floor(a))).append(',').append(d(StrictMath.sqrt(b))).append(',').append(d(StrictMath.max(a, b)));
            out.append(';');
        }
        return out.toString();
    }

    static final double[] PSPECIAL = {0.0, -0.0, 1.0, -1.0, Double.NaN, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY, 2.0, -2.0, 4.0, 3.0};
    static final double[] YSPECIAL = {0.0, -0.0, 1.0, -1.0, Double.NaN, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY, 2.0, -2.0, 3.0, -3.0};

    /** Math.pow where the specification fixes the result: special values and integer powers. */
    public static String pow(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 8; k++) {
            double x, y;
            switch (r(3)) {
                case 0: x = PSPECIAL[r(PSPECIAL.length)]; y = YSPECIAL[r(YSPECIAL.length)]; break;
                case 1: x = PSPECIAL[r(PSPECIAL.length)]; y = r(21) - 10; break;
                default: x = r(41) - 20; y = r(2) == 0 ? r(13) : r(9) - 8; if (x != 0 && x != 1 && x != -1 && x != 2 && x != -2 && x != 4 && x != 8 && x != 16 && y < 0) y = -y; break;
            }
            if (r(10) == 0) { x = -(r(9) + 1) - 0.5; y = 0.5; }   // a negative base and a non-integer power: NaN
            out.append(d(x)).append('^').append(d(y)).append('=').append(d(Math.pow(x, y))).append(';');
        }
        return out.toString();
    }

    public static String flt(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            float a = rf(), b = rf(), c = rf();
            double dd = rd();
            out.append(f(a)).append(' ').append(f(b)).append(':');
            out.append(f(Math.abs(a))).append(',').append(f(Math.signum(a))).append(',').append(Math.round(a)).append(',')
               .append(f(Math.ulp(a))).append(',').append(f(Math.nextUp(a))).append(',').append(f(Math.nextDown(a))).append(',')
               .append(Math.getExponent(a)).append(',').append(f(Math.max(a, b))).append(',').append(f(Math.min(a, b))).append(',')
               .append(f(Math.copySign(a, b))).append(',').append(f(Math.fma(a, b, c))).append(',')
               .append(f(Math.scalb(a, r(400) - 200))).append(',').append(f(Math.nextAfter(a, dd))).append(',')
               .append(f(Math.nextAfter(a, (double) b))).append(';');
        }
        return out.toString();
    }
}

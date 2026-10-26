package org.rocqjvm.jdkmodel;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.MathContext;
import java.math.RoundingMode;

/** Differential tests of java.math.BigDecimal, MathContext and RoundingMode: random values (compact
 *  and inflated unscaled values, small, large and extreme scales), constructors and parsing with
 *  their messages, arithmetic with and without MathContext in every rounding mode, the division
 *  family, scale operations, string forms, conversions, pow and sqrt, object identity of results
 *  (operands returned, cached constants). */
public final class DecOps {
    private DecOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static long rl() { return ((long) r(1 << 22) << 42) ^ ((long) r(1 << 22) << 20) ^ r(1 << 20); }

    static final RoundingMode[] RM = RoundingMode.values();

    static BigInteger unscaled() {
        switch (r(10)) {
            case 0: return BigInteger.valueOf(r(21) - 10);
            case 1: return BigInteger.valueOf(rl() >> r(64));
            case 2: return BigInteger.valueOf(rl());
            case 3: return BigInteger.TEN.pow(r(30)).multiply(BigInteger.valueOf(r(2) == 0 ? 1 : -1)).add(BigInteger.valueOf(r(3) - 1));
            case 4: return BigInteger.valueOf(rl()).multiply(BigInteger.valueOf(rl())).shiftRight(r(60));
            case 5: return BigInteger.valueOf(r(1000) - 500).multiply(BigInteger.TEN.pow(r(8)));
            case 6: { long[] sp = {Long.MIN_VALUE, Long.MAX_VALUE, Long.MIN_VALUE + 1, 999999999999999999L, 1000000000000000000L, -9223372036854775807L / 10};
                return BigInteger.valueOf(sp[r(sp.length)]); }
            case 7: return BigInteger.ZERO;
            default: return BigInteger.valueOf(r(200001) - 100000);
        }
    }

    static int scl() {
        switch (r(12)) {
            case 0: return Integer.MAX_VALUE - r(3);
            case 1: return Integer.MIN_VALUE + r(3);
            case 2: return r(60) - 30;
            default: return r(16) - 5;
        }
    }

    static int mildScl() {
        return r(10) == 0 ? r(60) - 30 : r(16) - 5;
    }

    static BigDecimal dec() {
        switch (r(9)) {
            case 0: return new BigDecimal(unscaled(), mildScl());
            case 1: return BigDecimal.valueOf(rl() >> r(64), mildScl());
            case 2: return BigDecimal.valueOf(r(21) - 10);
            case 3: return new BigDecimal(Double.longBitsToDouble(rl()) > 0 ? (r(2000000) - 1000000) / 64.0 : (r(2000) - 1000) / 7.0);
            case 4: return BigDecimal.valueOf((r(2000000) - 1000000) / 1000.0);
            case 5: { BigDecimal[] c = {BigDecimal.ZERO, BigDecimal.ONE, BigDecimal.valueOf(2), BigDecimal.TEN}; return c[r(4)]; }
            case 6: return new BigDecimal(BigInteger.ZERO, mildScl());
            default: return new BigDecimal(unscaled(), mildScl());
        }
    }

    static MathContext mc() {
        switch (r(10)) {
            case 0: return MathContext.UNLIMITED;
            case 1: return MathContext.DECIMAL32;
            case 2: return MathContext.DECIMAL64;
            case 3: return new MathContext(r(40), RM[r(8)]);
            default: return new MathContext(1 + r(12), RM[r(8)]);
        }
    }

    static String id(BigDecimal res, BigDecimal a, BigDecimal b) {
        if (res == null) return "=null";
        if (res == a) return "=a";
        if (res == b) return "=b";
        if (res == BigDecimal.ZERO) return "=0";
        if (res == BigDecimal.ONE) return "=1";
        if (res == BigDecimal.TEN) return "=10";
        if (res.scale() == 0 && res.signum() > 0 && res.compareTo(BigDecimal.TEN) <= 0 && res == BigDecimal.valueOf(res.intValue())) return "=c";
        if (res.signum() == 0 && res.scale() > 0 && res.scale() < 16 && res == BigDecimal.ZERO.setScale(res.scale())) return "=z";
        return "";
    }

    static void ex(StringBuilder out, RuntimeException e) {
        out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
    }

    static void put(StringBuilder out, BigDecimal res, BigDecimal a, BigDecimal b) {
        out.append(res).append(id(res, a, b));
    }

    static final String CH = "0123456789.eE+-x ٠٣５";

    static String numStr() {
        StringBuilder t = new StringBuilder();
        switch (r(4)) {
            case 0: {
                int n = r(30);
                for (int i = 0; i < n; i++) t.append(CH.charAt(r(4) == 0 ? r(CH.length()) : r(11)));
                return t.toString();
            }
            case 1: return new BigDecimal(unscaled(), mildScl()).toString();
            default: {
                if (r(3) == 0) t.append("+-".charAt(r(2)));
                int n = r(25);
                for (int i = 0; i < n; i++) t.append((char) ('0' + r(10)));
                if (r(2) == 0) {
                    t.append('.');
                    for (int i = r(12); i > 0; i--) t.append((char) ('0' + r(10)));
                }
                if (r(2) == 0) {
                    t.append("eE".charAt(r(2)));
                    if (r(2) == 0) t.append("+-".charAt(r(2)));
                    int k = r(5) == 0 ? r(14) : r(4);
                    for (int i = 0; i < k; i++) t.append((char) ('0' + (r(4) == 0 ? 0 : r(10))));
                }
                return t.toString();
            }
        }
    }

    public static String ctor(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 12; k++) {
            try {
                BigDecimal res;
                switch (r(14)) {
                    case 0: case 1: case 2: { String t = numStr(); out.append(t).append(':'); res = new BigDecimal(t); break; }
                    case 3: { String t = numStr(); out.append(t).append(':'); res = new BigDecimal(t, mc()); break; }
                    case 4: { char[] c = numStr().toCharArray(); int off = r(4) - 1, len = c.length - r(4);
                        res = r(2) == 0 ? new BigDecimal(c, off, len) : new BigDecimal(c, off, len, mc()); break; }
                    case 5: { double d = r(3) == 0 ? Double.longBitsToDouble(rl()) : (r(2000000) - 1000000) / 1024.0;
                        res = r(2) == 0 ? new BigDecimal(d) : new BigDecimal(d, mc()); break; }
                    case 6: { double d = r(3) == 0 ? Double.longBitsToDouble(rl()) : (r(2000000) - 1000000) / 1000.0;
                        res = BigDecimal.valueOf(d); break; }
                    case 7: { int v = r(2) == 0 ? r(2000001) - 1000000 : (int) rl(); res = r(2) == 0 ? new BigDecimal(v) : new BigDecimal(v, mc()); break; }
                    case 8: { long v = r(4) == 0 ? Long.MIN_VALUE : rl(); res = r(2) == 0 ? new BigDecimal(v) : new BigDecimal(v, mc()); break; }
                    case 9: { BigInteger v = unscaled(); int sc = scl(); res = r(2) == 0 ? new BigDecimal(v, sc) : new BigDecimal(v, sc, mc()); break; }
                    case 10: { BigInteger v = unscaled(); res = r(2) == 0 ? new BigDecimal(v) : new BigDecimal(v, mc()); break; }
                    case 11: res = BigDecimal.valueOf(rl() >> r(64), scl()); break;
                    case 12: { long v = r(3) == 0 ? r(12) : rl() >> r(64); res = r(2) == 0 ? BigDecimal.valueOf(v) : BigDecimal.valueOf(v, r(3) == 0 ? 0 : r(20)); break; }
                    default:
                        switch (r(7)) {
                            case 0: res = new BigDecimal((String) null); break;
                            case 1: res = new BigDecimal((char[]) null); break;
                            case 2: res = new BigDecimal("1.5", null); break;
                            case 3: res = new BigDecimal((BigInteger) null, 2); break;
                            case 4: res = new BigDecimal(r(2) == 0 ? 0.0 : 2.5, null); break;
                            case 5: res = new BigDecimal(Double.NaN); break;
                            default: res = new BigDecimal(r(2), null); break;
                        }
                }
                put(out, res, null, null);
                out.append('/').append(res.precision());
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String arith(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 12; k++) {
            BigDecimal a = dec();
            BigDecimal b = r(6) == 0 ? BigDecimal.ZERO : dec();
            if (r(8) == 0) b = new BigDecimal(unscaled(), scl());
            MathContext m = mc();
            try {
                BigDecimal res;
                switch (r(14)) {
                    case 0: res = a.add(b); break;
                    case 1: res = a.add(b, m); break;
                    case 2: res = a.subtract(b); break;
                    case 3: res = a.subtract(b, m); break;
                    case 4: res = a.multiply(b); break;
                    case 5: res = a.multiply(b, m); break;
                    case 6: res = r(2) == 0 ? a.negate() : a.negate(m); break;
                    case 7: res = r(2) == 0 ? a.abs() : a.abs(m); break;
                    case 8: res = r(2) == 0 ? a.plus() : a.plus(m); break;
                    case 9: res = a.round(m); break;
                    case 10: res = r(2) == 0 ? a.min(b) : a.max(b); break;
                    case 11: { BigDecimal c = new BigDecimal(unscaled(), mildScl() + 40); res = a.add(c, m); break; }
                    case 12:
                        switch (r(6)) {
                            case 0: res = a.add(null); break;
                            case 1: res = a.add(null, m); break;
                            case 2: res = a.subtract(null, m); break;
                            case 3: res = a.multiply(b, null); break;
                            case 4: res = a.round(null); break;
                            default: res = a.min(null); break;
                        }
                        break;
                    default: out.append(a.compareTo(b)).append(a.equals(b)).append(a.signum()).append(','); res = a; break;
                }
                put(out, res, a, b);
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String div(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            BigDecimal a = dec();
            BigDecimal b = r(7) == 0 ? (r(2) == 0 ? BigDecimal.ZERO : new BigDecimal(BigInteger.ZERO, r(10) - 3)) : dec();
            if (r(10) == 0) b = new BigDecimal(BigInteger.valueOf(r(2) == 0 ? 3 : 7).pow(r(5)), mildScl());
            MathContext m = mc();
            int sc = r(10) == 0 ? scl() : mildScl();
            try {
                BigDecimal res;
                switch (r(13)) {
                    case 0: res = a.divide(b, sc, RM[r(8)]); break;
                    case 1: res = a.divide(b, sc, r(10) - 1); break;
                    case 2: res = r(2) == 0 ? a.divide(b, RM[r(8)]) : a.divide(b, r(10) - 1); break;
                    case 3: case 4: res = a.divide(b); break;
                    case 5: case 6: res = a.divide(b, m); break;
                    case 7: res = r(2) == 0 ? a.divideToIntegralValue(b) : a.divideToIntegralValue(b, m); break;
                    case 8: res = r(2) == 0 ? a.remainder(b) : a.remainder(b, m); break;
                    case 9: { BigDecimal[] qr = r(2) == 0 ? a.divideAndRemainder(b) : a.divideAndRemainder(b, m);
                        put(out, qr[0], a, b); out.append(','); res = qr[1]; break; }
                    case 10: { BigDecimal c = BigDecimal.valueOf(r(2) == 0 ? 3 : 7, r(5));
                        res = a.divide(c, new MathContext(r(30), RM[r(8)])); break; }
                    case 11: res = a.divide(b, new MathContext(r(4) == 0 ? 0 : 1 + r(5), RM[r(8)])); break;
                    default:
                        switch (r(7)) {
                            case 0: res = a.divide(null); break;
                            case 1: res = a.divide(null, m); break;
                            case 2: res = a.divide(b, (RoundingMode) null); break;
                            case 3: res = a.divide(null, 2, RoundingMode.UP); break;
                            case 4: res = a.divideToIntegralValue(null, m); break;
                            case 5: res = a.remainder(null); break;
                            default: res = a.divide(b, (MathContext) null); break;
                        }
                }
                put(out, res, a, b);
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String scale(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 12; k++) {
            BigDecimal a = dec();
            int n = r(8) == 0 ? scl() : mildScl();
            try {
                Object res;
                switch (r(12)) {
                    case 0: case 1: res = a.setScale(n, RM[r(8)]); break;
                    case 2: res = r(2) == 0 ? a.setScale(n) : a.setScale(n, r(10) - 1); break;
                    case 3: res = a.movePointLeft(r(5) == 0 ? 0 : n); break;
                    case 4: res = a.movePointRight(r(5) == 0 ? 0 : n); break;
                    case 5: res = a.scaleByPowerOfTen(n); break;
                    case 6: res = a.stripTrailingZeros(); break;
                    case 7: res = a.precision() + "/" + a.scale() + "/" + a.signum() + "/" + a.unscaledValue(); break;
                    case 8: res = a.ulp(); break;
                    case 9: { BigInteger u = a.unscaledValue(); res = (u == BigInteger.ZERO) + "," + (u == BigInteger.ONE) + "," + (u == BigInteger.TEN) + "," + u; break; }
                    case 10: res = a.setScale(a.scale() + r(5) - 2, RoundingMode.UNNECESSARY); break;
                    default: res = a.setScale(2, (RoundingMode) null); break;
                }
                out.append(res);
                if (res instanceof BigDecimal) out.append(id((BigDecimal) res, a, null));
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String conv(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 12; k++) {
            BigDecimal a = r(5) == 0 ? new BigDecimal(unscaled(), r(700) - 350) : dec();
            try {
                switch (r(15)) {
                    case 0: out.append(a.toString()).append(',').append(a.toEngineeringString()); break;
                    case 1: out.append(a.toPlainString()); break;
                    case 2: out.append(a.intValue()).append(',').append(a.longValue()); break;
                    case 3: out.append(a.intValueExact()); break;
                    case 4: out.append(a.longValueExact()); break;
                    case 5: out.append(r(2) == 0 ? a.shortValueExact() : a.byteValueExact()); break;
                    case 6: out.append(Double.doubleToRawLongBits(a.doubleValue())); break;
                    case 7: out.append(Float.floatToRawIntBits(a.floatValue())); break;
                    case 8: out.append(a.toBigInteger()); break;
                    case 9: out.append(a.toBigIntegerExact()); break;
                    case 10: out.append(a.hashCode()); break;
                    case 11: { BigDecimal b = a.setScale(a.scale() + r(3)); out.append(a.equals(b)).append(a.compareTo(b)).append(b.hashCode()); break; }
                    case 12: out.append(a.shortValue()).append(',').append(a.byteValue()); break;
                    case 13: { BigDecimal b = new BigDecimal(BigInteger.valueOf(rl()).multiply(BigInteger.valueOf(rl())), r(800) - 400);
                        out.append(Double.doubleToRawLongBits(b.doubleValue())).append(',').append(Float.floatToRawIntBits(b.floatValue())); break; }
                    default: out.append(new BigDecimal(unscaled(), scl()).toString()); break;
                }
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String powsqrt(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            BigDecimal a = r(3) == 0 ? new BigDecimal(BigInteger.valueOf(r(1000)), r(8) - 2) : dec();
            MathContext m = r(3) == 0 ? new MathContext(r(25), RM[r(8)]) : mc();
            try {
                BigDecimal res;
                switch (r(6)) {
                    case 0: res = a.pow(r(10) == 0 ? r(5) - 2 : r(12)); break;
                    case 1: res = a.pow(r(30) - 10, m); break;
                    case 2: case 3: res = a.abs().sqrt(m); break;
                    case 4: { BigDecimal sq = a.multiply(a); res = sq.sqrt(r(2) == 0 ? MathContext.UNLIMITED : m); break; }
                    default: res = r(2) == 0 ? a.sqrt(null) : a.pow(2, null); break;
                }
                put(out, res, a, null);
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String mctx(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            try {
                switch (r(8)) {
                    case 0: { MathContext m = new MathContext(r(20) - 3, r(6) == 0 ? null : RM[r(8)]); out.append(m).append(m.getPrecision()).append(m.getRoundingMode()); break; }
                    case 1: { MathContext m = new MathContext(r(20) - 3); out.append(m); break; }
                    case 2: {
                        String[] t = {"precision=7 roundingMode=HALF_EVEN", "precision=0 roundingMode=UP", "precision=-1 roundingMode=UP",
                            "precision=x roundingMode=UP", "precision=5 roundingMode=up", "precision=5  roundingMode=UP", "precision=",
                            "precision=12 roundingMode=", "precision=+3 roundingMode=FLOOR", "Precision=1 roundingMode=UP",
                            "precision=99999999999 roundingMode=UP", "precision=3 roundingMode=UNNECESSARY", "", null};
                        String v = t[r(t.length)];
                        out.append(new MathContext(v)); break;
                    }
                    case 3: { MathContext a = mc(); MathContext b = mc(); out.append(a.equals(b)).append(a.equals(new MathContext(a.toString()))).append(a.equals("x")); break; }
                    case 4: { int v = r(12) - 2; out.append(RoundingMode.valueOf(v)); break; }
                    case 5: { RoundingMode m = RM[r(8)]; out.append(m.name()).append(m.ordinal()).append(m.compareTo(RM[r(8)])).append(m == RoundingMode.valueOf(m.ordinal())); break; }
                    case 6: out.append(RoundingMode.values().length).append(RoundingMode.HALF_EVEN.toString()).append(RoundingMode.values()[r(8)]); break;
                    default: out.append(MathContext.DECIMAL128).append(MathContext.UNLIMITED).append(MathContext.DECIMAL32.getPrecision()); break;
                }
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String[] EDGE = {"0", "-0", "0.000", "0E+5", "0E-20", "1", "-1", "1.0", "10", "100E-2", "9.99", "0.0001", "123456789012345678",
        "1234567890123456789", "9223372036854775807", "-9223372036854775808", "9223372036854775808", "0.00000001234", "1E+2147483647",
        "1E-2147483647", "-5E-2147483647", "12345678901234567890123456789012345678901234567890", "0.5", "-0.5", "2.5", "-2.5", "1.05", "99999",
        "4.000000000000000000000000001", "1e+0", "1.e1", ".5", "+.5e-3", "5.", "3.141592653589793238462643383279502884197"};

    static BigDecimal edge() {
        return new BigDecimal(EDGE[r(EDGE.length)]);
    }

    public static String edge(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            BigDecimal a = r(4) == 0 ? dec() : edge();
            BigDecimal b = r(4) == 0 ? dec() : edge();
            MathContext m = new MathContext(r(4) == 0 ? r(40) : 1 + r(6), RM[r(8)]);
            try {
                Object res;
                switch (r(20)) {
                    case 0: res = a.add(b, m); break;
                    case 1: res = a.subtract(b, m); break;
                    case 2: res = a.multiply(b, m); break;
                    case 3: res = a.divide(b, m); break;
                    case 4: res = a.divide(b); break;
                    case 5: res = a.divideToIntegralValue(b, m); break;
                    case 6: res = a.remainder(b, m); break;
                    case 7: res = a.setScale(r(3) == 0 ? -600000 + r(3) : r(20) - 10, RM[r(8)]); break;
                    case 8: res = a.round(m); break;
                    case 9: res = a.abs().sqrt(m); break;
                    case 10: res = a.pow(r(7), m); break;
                    case 11: res = a.stripTrailingZeros(); break;
                    case 12: res = a.toEngineeringString() + "," + (Math.abs(a.scale()) < 1000 ? a.toPlainString() : "") + "," + a.precision(); break;
                    case 13: res = Double.doubleToRawLongBits(a.doubleValue()) + "," + Float.floatToRawIntBits(a.floatValue()); break;
                    case 14: res = new BigDecimal(EDGE[r(EDGE.length)].toCharArray(), m); break;
                    case 15: res = new BigDecimal(EDGE[r(EDGE.length)].toCharArray()); break;
                    case 16: res = a.compareTo(b) + "," + a.equals(b) + "," + a.hashCode() + "," + a.max(b) + id(a.min(b), a, b); break;
                    case 17: res = a.divide(b, r(30) - 10, RM[r(8)]); break;
                    case 18: res = a.longValue() + "," + a.intValue() + "," + a.toBigInteger(); break;
                    default: res = a.movePointLeft(r(30) - 15) + "," + a.movePointRight(r(30) - 15) + "," + a.scaleByPowerOfTen(r(30) - 15); break;
                }
                out.append(res);
                if (res instanceof BigDecimal) out.append(id((BigDecimal) res, a, b));
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }
}

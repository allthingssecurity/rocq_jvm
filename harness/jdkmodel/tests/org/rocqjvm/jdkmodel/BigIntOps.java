package org.rocqjvm.jdkmodel;

import java.math.BigInteger;

/** Differential tests of java.math.BigInteger: random values of all sizes (boundary values, powers
 *  of two and their neighbours, multi-word numbers of both signs), arithmetic with exceptions,
 *  bit operations, conversions, parsing with its messages, modular arithmetic, object identity of
 *  results (cached constants, operands returned). */
public final class BigIntOps {
    private BigIntOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static long rl() { return ((long) r(1 << 22) << 42) ^ ((long) r(1 << 22) << 20) ^ r(1 << 20); }

    static BigInteger big() {
        switch (r(12)) {
            case 0: return BigInteger.valueOf(r(41) - 20);
            case 1: return BigInteger.valueOf(rl());
            case 2: return BigInteger.valueOf(rl() >> r(64));
            case 3: { BigInteger b = BigInteger.ONE.shiftLeft(r(130)); int d = r(3) - 1; b = b.add(BigInteger.valueOf(d)); return r(2) == 0 ? b : b.negate(); }
            case 4: return new BigInteger(r(2) == 0 ? 1 : -1, bytes(1 + r(30)));
            case 5: return new BigInteger(bytes(1 + r(20)));
            case 6: { long[] sp = {Long.MIN_VALUE, Long.MAX_VALUE, Integer.MIN_VALUE, Integer.MAX_VALUE, 0xffffffffL, 1L << 32, -(1L << 32), 1L << 31, -(1L << 31), 1L << 63 - 1};
                return BigInteger.valueOf(sp[r(sp.length)]); }
            case 7: return BigInteger.valueOf(rl()).multiply(BigInteger.valueOf(rl())).multiply(BigInteger.valueOf(r(1000) - 500));
            case 8: return BigInteger.TEN.pow(r(40)).subtract(BigInteger.valueOf(r(3)));
            case 9: return r(2) == 0 ? BigInteger.ZERO : BigInteger.ONE;
            default: return BigInteger.valueOf(r(2000001) - 1000000);
        }
    }

    static byte[] bytes(int n) {
        byte[] b = new byte[n];
        for (int i = 0; i < n; i++) b[i] = (byte) (r(5) == 0 ? (r(2) == 0 ? 0 : -1) : r(256));
        return b;
    }

    static String str(byte[] b) {
        StringBuilder t = new StringBuilder("[");
        for (int i = 0; i < b.length; i++) t.append(i == 0 ? "" : ",").append(b[i]);
        return t.append(']').toString();
    }

    static String id(BigInteger res, BigInteger a, BigInteger b) {
        if (res == a) return "=a";
        if (res == b) return "=b";
        if (res == BigInteger.ZERO) return "=0";
        if (res == BigInteger.ONE) return "=1";
        if (res == BigInteger.TWO) return "=2";
        if (res == BigInteger.TEN) return "=10";
        if (res == BigInteger.valueOf(-1)) return "=-1";
        if (res == BigInteger.valueOf(res.longValue())) return "=c";
        return "";
    }

    static void ex(StringBuilder out, RuntimeException e) {
        out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
    }

    public static String arith(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 12; k++) {
            BigInteger a = big();
            BigInteger b = r(6) == 0 ? BigInteger.ZERO : big();
            try {
                BigInteger res;
                switch (r(16)) {
                    case 0: res = a.add(b); break;
                    case 1: res = a.subtract(b); break;
                    case 2: res = a.multiply(b); break;
                    case 3: res = a.divide(b); break;
                    case 4: res = a.remainder(b); break;
                    case 5: { BigInteger[] qr = a.divideAndRemainder(b); out.append(qr[0]).append(id(qr[0], a, b)).append(',');
                        res = qr[1]; break; }
                    case 6: res = a.mod(b); break;
                    case 7: res = a.pow(r(8) == 0 ? r(5) - 2 : r(40)); break;
                    case 8: res = a.gcd(b); break;
                    case 9: res = a.abs(); break;
                    case 10: res = a.negate(); break;
                    case 11: res = r(2) == 0 ? a.min(b) : a.max(b); break;
                    case 12: res = a.sqrt(); break;
                    case 13: { BigInteger[] sr = a.sqrtAndRemainder(); out.append(sr[0]).append(id(sr[0], a, b)).append(',');
                        res = sr[1]; break; }
                    case 14: res = r(2) == 0 ? a.add(null) : a.divide(null); break;
                    default: res = BigInteger.valueOf(a.signum() * 100 + a.compareTo(b) * 10 + (a.equals(b) ? 1 : 0)); break;
                }
                out.append(res).append(id(res, a, b));
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String bits(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 12; k++) {
            BigInteger a = big();
            BigInteger b = big();
            int n = r(10) == 0 ? -r(5) : r(140);
            try {
                Object res;
                switch (r(17)) {
                    case 0: res = a.and(b); break;
                    case 1: res = a.or(b); break;
                    case 2: res = a.xor(b); break;
                    case 3: res = a.andNot(b); break;
                    case 4: res = a.not(); break;
                    case 5: res = a.shiftLeft(r(3) == 0 ? -n : n); break;
                    case 6: res = a.shiftRight(r(3) == 0 ? -n : n); break;
                    case 7: res = a.testBit(n); break;
                    case 8: res = a.setBit(n); break;
                    case 9: res = a.clearBit(n); break;
                    case 10: res = a.flipBit(n); break;
                    case 11: res = a.getLowestSetBit() + "/" + a.bitLength() + "/" + a.bitCount(); break;
                    case 12: res = str(a.toByteArray()); break;
                    case 13: res = a.shiftLeft(r(2) == 0 ? Integer.MIN_VALUE : -Integer.MAX_VALUE); break;
                    case 14: res = a.shiftRight(r(2) == 0 ? Integer.MAX_VALUE : 1 << 20); break;
                    case 15: res = a.hashCode(); break;
                    default: res = a.and(null); break;
                }
                out.append(res);
                if (res instanceof BigInteger) out.append(id((BigInteger) res, a, b));
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
            BigInteger a = big();
            try {
                switch (r(14)) {
                    case 0: out.append(a.intValue()).append(',').append(a.longValue()); break;
                    case 1: out.append(a.shortValue()).append(',').append(a.byteValue()); break;
                    case 2: out.append(Double.doubleToRawLongBits(a.doubleValue())); break;
                    case 3: out.append(Float.floatToRawIntBits(a.floatValue())); break;
                    case 4: out.append(a.intValueExact()); break;
                    case 5: out.append(a.longValueExact()); break;
                    case 6: out.append(a.shortValueExact()); break;
                    case 7: out.append(a.byteValueExact()); break;
                    case 8: out.append(a.toString(r(40))); break;
                    case 9: out.append(a.toString(16)).append(',').append(a.toString(2)).append(',').append(a.toString(36)); break;
                    case 10: { BigInteger c = BigInteger.ONE.shiftLeft(r(1100)).multiply(a.add(BigInteger.valueOf(r(7))));
                        out.append(c.doubleValue()).append(',').append(c.negate().floatValue()); break; }
                    case 11: out.append(new BigInteger(a.toByteArray()).equals(a)); break;
                    case 12: out.append(a.hashCode()).append(',').append(a.equals(a.toString())); break;
                    default: out.append(a); break;
                }
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String DIG = "0123456789abcdefzZ0+- x٠١１";

    public static String parse(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 12; k++) {
            try {
                BigInteger res;
                switch (r(9)) {
                    case 0: case 1: case 2: {
                        StringBuilder t = new StringBuilder();
                        if (r(3) == 0) t.append("+-".charAt(r(2)));
                        int n = r(30);
                        for (int i = 0; i < n; i++) t.append(r(12) == 0 ? DIG.charAt(r(DIG.length())) : (char) ('0' + r(10)));
                        int radix = r(8) == 0 ? r(40) : (r(2) == 0 ? 10 : 2 + r(35));
                        out.append(t.toString()).append('/').append(radix).append(':');
                        res = new BigInteger(t.toString(), radix);
                        break;
                    }
                    case 3: { BigInteger a = big(); int radix = 2 + r(35); res = new BigInteger(a.toString(radix), radix); out.append(res.equals(a)); break; }
                    case 4: { byte[] b = bytes(r(12)); int off = r(5) - 1; int len = r(8) - 1; res = new BigInteger(b, off, len); break; }
                    case 5: { byte[] b = bytes(r(12)); int sg = r(5) - 2; res = r(2) == 0 ? new BigInteger(sg, b) : new BigInteger(sg, b, r(4) - 1, r(6) - 1); break; }
                    case 6: res = r(2) == 0 ? new BigInteger((String) null) : new BigInteger((byte[]) null); break;
                    case 7:
                        switch (r(6)) {
                            case 0: res = new BigInteger(r(3) - 1, r(2) == 0 ? null : new byte[] {0, 0}); break;
                            case 1: res = new BigInteger(r(3) - 1, (java.util.Random) null); break;
                            case 2: res = new BigInteger(r(4) * 40, r(3), (java.util.Random) null); break;
                            case 3: res = BigInteger.probablePrime(r(4) * 40, null); break;
                            case 4: { BigInteger a = big(); out.append(a.bitLength() <= 81 ? a.isProbablePrime(99 + r(30)) : false).append(','); res = a; break; }
                            default: { BigInteger a = big().abs(); res = a.bitLength() <= 70 ? a.nextProbablePrime() : a; break; }
                        }
                        break;
                    default: res = new BigInteger(bytes(r(3))); break;
                }
                out.append(res).append(id(res, null, null));
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String modular(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            BigInteger a = big();
            BigInteger e = r(4) == 0 ? BigInteger.valueOf(r(7) - 3) : big();
            BigInteger m = r(5) == 0 ? BigInteger.valueOf(r(5) - 1) : big().abs();
            try {
                BigInteger res;
                switch (r(7)) {
                    case 0: case 1: case 2: res = a.modPow(e, m); break;
                    case 3: res = a.modInverse(m); break;
                    case 4: res = a.mod(m); break;
                    case 5: {
                        BigInteger p = BigInteger.valueOf(r(1000000)).multiply(BigInteger.valueOf(r(1000000) + 1));
                        out.append(p.isProbablePrime(100)).append(p.add(BigInteger.ONE).isProbablePrime(r(2) == 0 ? 0 : 120)).append(',');
                        res = BigInteger.valueOf(r(100000) - 100).nextProbablePrime();
                        break;
                    }
                    default: res = r(2) == 0 ? a.modPow(e, null) : a.modPow(null, m); break;
                }
                out.append(res).append(id(res, a, m));
            } catch (RuntimeException ex) {
                ex(out, ex);
            }
            out.append(';');
        }
        return out.toString();
    }
}

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.SplittableRandom;

/**
 * JVM side of the float/double differential test.
 *
 *   java FloatHarness gen  DIR N SEED   writes DIR/OP.in (N lines per op)
 *   java FloatHarness eval DIR [OP...]  reads DIR/OP.in, writes DIR/OP.java
 *
 * Input format: float bits as 8-digit hex, double bits as 16-digit hex
 * (unsigned), int/long as signed decimal; one or two operands per line.
 * Output: float/double results as Integer/Long.toHexString of
 * Float.floatToIntBits / Double.doubleToLongBits (NaNs canonicalised to
 * 0x7fc00000 / 0x7ff8000000000000), int/long results as signed decimal.
 * The fneg_raw/dneg_raw ops use floatToRawIntBits/doubleToRawLongBits
 * (no canonicalisation) to observe the sign of a negated NaN.
 */
public class FloatHarness {

  static final String[] OPS = {
    "fadd", "fsub", "fmul", "fdiv", "frem", "fneg", "fneg_raw",
    "dadd", "dsub", "dmul", "ddiv", "drem", "dneg", "dneg_raw",
    "i2f", "i2d", "l2f", "l2d", "f2d", "d2f", "f2i", "f2l", "d2i", "d2l",
    "fcmpl", "fcmpg", "dcmpl", "dcmpg"
  };

  // ------------------------------------------------------------ generators

  static final int[] FSPEC = {
    0, 0x80000000, 0x7f800000, 0xff800000,                 // zeros, infinities
    0x7fc00000, 0xffc00000, 0x7f800001, 0xff800001,        // NaNs (quiet, signalling)
    0x7fbfffff, 0x7fffffff, 0xffffffff, 0x7fc00001,
    1, 0x80000001, 2, 3, 0x7f7fffff, 0xff7fffff,           // MIN_VALUE, MAX_VALUE
    0x00800000, 0x80800000, 0x007fffff, 0x807fffff,        // MIN_NORMAL, max subnormal
    0x00400000, 0x00800001, 0x3f800000, 0xbf800000, 0x40000000, 0x3f000000,
    0x4f000000, 0xcf000000, 0x4effffff, 0xceffffff, 0x4f000001, 0xcf000001, // 2^31
    0x5f000000, 0xdf000000, 0x5effffff, 0xdeffffff, 0x5f000001, 0xdf000001, // 2^63
    0x4b800000, 0x4b7fffff, 0x4b800001, 0x4b000000,        // 2^24, 2^23
    0x3dcccccd, 0x3e4ccccd, 0x40400000, 0x41200000, 0x3eaaaaab, 0x34000000,
  };

  static final long[] DSPEC = {
    0L, 0x8000000000000000L, 0x7ff0000000000000L, 0xfff0000000000000L,
    0x7ff8000000000000L, 0xfff8000000000000L, 0x7ff0000000000001L, 0xfff0000000000001L,
    0x7ff7ffffffffffffL, 0x7fffffffffffffffL, 0xffffffffffffffffL, 0x7ff8000000000001L,
    1L, 0x8000000000000001L, 2L, 3L, 0x7fefffffffffffffL, 0xffefffffffffffffL,
    0x0010000000000000L, 0x8010000000000000L, 0x000fffffffffffffL, 0x800fffffffffffffL,
    0x0008000000000000L, 0x0010000000000001L,
    0x3ff0000000000000L, 0xbff0000000000000L, 0x4000000000000000L, 0x3fe0000000000000L,
    0x41e0000000000000L, 0xc1e0000000000000L, 0x41dfffffffffffffL, 0xc1dfffffffffffffL, // 2^31
    0x41dfffffffc00000L, 0xc1e0000000200000L, 0x41dfffffffe00000L, // 2^31-1, -2^31-1, 2^31-0.5
    0x43e0000000000000L, 0xc3e0000000000000L, 0x43dfffffffffffffL, 0xc3dfffffffffffffL, // 2^63
    0x4340000000000000L, 0x433fffffffffffffL, 0x4340000000000001L, // 2^53
    0x47efffffe0000000L, 0x47effffff0000000L, 0x47effffff0000001L, 0x47efffffefffffffL, // float max
    0x47f0000000000000L, 0x36a0000000000000L, 0x3690000000000000L, 0x3698000000000000L, // 2^128, 2^-149, 2^-150
    0x3810000000000000L, 0x380fffffffffffffL, 0x3fb999999999999aL, 0x3fc999999999999aL,
  };

  static int pickF(SplittableRandom r) { return FSPEC[r.nextInt(FSPEC.length)]; }
  static long pickD(SplittableRandom r) { return DSPEC[r.nextInt(DSPEC.length)]; }

  /** significand of width w with a "rounding-tie" shape: random high part, bit t set,
   *  zeros below (possibly +-1), so that it is a tie for some rounding position. */
  static long tieFrac(SplittableRandom r, int w) {
    int t = r.nextInt(w);
    long hi = r.nextLong() & ~((1L << (t + 1)) - 1);
    long v = hi | (1L << t);
    int k = r.nextInt(4);
    if (k == 1) v += 1; else if (k == 2) v -= 1;
    return v & ((1L << w) - 1);
  }

  static long edgeFrac(SplittableRandom r, int w) {
    long max = (1L << w) - 1;
    long[] c = {0, 1, 2, 3, max, max - 1, max - 2, 1L << (w - 1), (1L << (w - 1)) + 1, (1L << (w - 1)) - 1};
    return c[r.nextInt(c.length)];
  }

  static int mkF(boolean s, int e, long frac) {
    return (s ? 0x80000000 : 0) | ((e & 0xff) << 23) | (int) (frac & 0x7fffff);
  }
  static long mkD(boolean s, long e, long frac) {
    return (s ? 0x8000000000000000L : 0L) | ((e & 0x7ff) << 52) | (frac & 0xfffffffffffffL);
  }
  static int clampE(int e, int max) { return Math.max(0, Math.min(max, e)); }

  static long anyFrac(SplittableRandom r, int w) {
    switch (r.nextInt(3)) {
      case 0: return edgeFrac(r, w);
      case 1: return tieFrac(r, w);
      default: return r.nextLong() & ((1L << w) - 1);
    }
  }

  static int genF(SplittableRandom r) {
    boolean s = r.nextBoolean();
    switch (r.nextInt(16)) {
      case 0: case 1: case 2: return pickF(r);
      case 3: return mkF(s, r.nextInt(255), edgeFrac(r, 23));                 // near powers of two
      case 4: return mkF(s, r.nextInt(3), r.nextBoolean() ? r.nextInt(16) : r.nextInt()); // subnormal
      case 5: { int[] k = {0, 1, 22, 23, 24, 25, 30, 31, 32, 52, 53, 62, 63, 64};
                return mkF(s, 127 + k[r.nextInt(k.length)], anyFrac(r, 23)); } // near int/long limits
      case 6: return mkF(s, r.nextInt(255), tieFrac(r, 23));
      case 7: return mkF(s, 255, 1 + r.nextInt(0x7fffff));                   // NaN payloads
      case 8: case 9: return mkF(s, 100 + r.nextInt(55), r.nextInt());       // ordinary magnitudes
      default: return r.nextInt();
    }
  }

  static int genF2(SplittableRandom r, int a) {
    boolean s = r.nextBoolean();
    int ea = (a >>> 23) & 0xff;
    switch (r.nextInt(10)) {
      case 0: case 1: case 2: case 3: return genF(r);
      case 4: return r.nextBoolean() ? a ^ 0x80000000 : a;
      case 5: return (a + r.nextInt(9) - 4) ^ (r.nextBoolean() ? 0x80000000 : 0);
      case 6: case 7: { int d = r.nextBoolean() ? r.nextInt(61) - 30 : (r.nextBoolean() ? 1 : -1) * (22 + r.nextInt(5));
                        return mkF(s, clampE(ea + d, 254), anyFrac(r, 23)); }
      case 8: return mkF(s, ea, r.nextInt());
      default: { float[] c = {1f, 2f, 3f, 0.5f, 10f, 0.1f, 7f, 1.5f, 0.75f, 1e-3f, 1e10f};
                 float v = c[r.nextInt(c.length)]; return Float.floatToRawIntBits(s ? -v : v); }
    }
  }

  static long genD(SplittableRandom r) {
    boolean s = r.nextBoolean();
    switch (r.nextInt(18)) {
      case 0: case 1: case 2: return pickD(r);
      case 3: return mkD(s, r.nextInt(2047), edgeFrac(r, 52));
      case 4: return mkD(s, r.nextInt(3), r.nextBoolean() ? r.nextInt(16) : r.nextLong());
      case 5: { int[] k = {0, 1, 23, 24, 25, 30, 31, 32, 52, 53, 54, 62, 63, 64};
                return mkD(s, 1023 + k[r.nextInt(k.length)], anyFrac(r, 52)); }
      case 6: return mkD(s, r.nextInt(2047), tieFrac(r, 52));
      case 7: return mkD(s, 2047, 1 + (r.nextLong() & 0xfffffffffffffL - 1));
      case 8: case 9: return mkD(s, 900 + r.nextInt(250), r.nextLong());
      case 10: case 11: return floatish(r);
      default: return r.nextLong();
    }
  }

  /** doubles that exercise d2f: around float values, ties at float precision,
   *  the float subnormal range and the float overflow threshold. */
  static long floatish(SplittableRandom r) {
    boolean s = r.nextBoolean();
    switch (r.nextInt(4)) {
      case 0: {
        long d = Double.doubleToRawLongBits((double) Float.intBitsToFloat(genF(r)));
        long[] p = {0x10000000L, 0x10000001L, 0x0fffffffL, 0, 1, r.nextLong() & 0x1fffffffL};
        return d ^ (p[r.nextInt(p.length)] & 0x1fffffffL);
      }
      case 1: return mkD(s, 1023 - 155 + r.nextInt(35), anyFrac(r, 52));   // float subnormals
      case 2: return mkD(s, 1023 + 125 + r.nextInt(5), anyFrac(r, 52));    // float overflow
      default: return mkD(s, 1023 - 140 + r.nextInt(280), tieFrac(r, 52));
    }
  }

  static long genD2(SplittableRandom r, long a) {
    boolean s = r.nextBoolean();
    int ea = (int) ((a >>> 52) & 0x7ff);
    switch (r.nextInt(10)) {
      case 0: case 1: case 2: case 3: return genD(r);
      case 4: return r.nextBoolean() ? a ^ 0x8000000000000000L : a;
      case 5: return (a + r.nextInt(9) - 4) ^ (r.nextBoolean() ? 0x8000000000000000L : 0L);
      case 6: case 7: { int d = r.nextBoolean() ? r.nextInt(121) - 60 : (r.nextBoolean() ? 1 : -1) * (51 + r.nextInt(5));
                        return mkD(s, clampE(ea + d, 2046), anyFrac(r, 52)); }
      case 8: return mkD(s, ea, r.nextLong());
      default: { double[] c = {1, 2, 3, 0.5, 10, 0.1, 7, 1.5, 0.75, 1e-3, 1e10};
                 double v = c[r.nextInt(c.length)]; return Double.doubleToRawLongBits(s ? -v : v); }
    }
  }

  /** operands for f2i/f2l: half near the int/long range limits */
  static int genFconv(SplittableRandom r) {
    if (r.nextBoolean()) return genF(r);
    return mkF(r.nextBoolean(), 127 - 2 + r.nextInt(69), anyFrac(r, 23));
  }
  static long genDconv(SplittableRandom r) {
    if (r.nextBoolean()) return genD(r);
    return mkD(r.nextBoolean(), 1023 - 2 + r.nextInt(69), anyFrac(r, 52));
  }

  static int genI(SplittableRandom r) {
    switch (r.nextInt(10)) {
      case 0: case 1: { int[] c = {0, 1, -1, Integer.MIN_VALUE, Integer.MAX_VALUE, Integer.MIN_VALUE + 1,
                                   Integer.MAX_VALUE - 1, 1 << 24, (1 << 24) + 1, (1 << 24) - 1, 1 << 30,
                                   -(1 << 24) - 1, (1 << 25) + 3, 0x7fffffc0, 0x7fffff80, 0x7fffffbf};
                        return c[r.nextInt(c.length)]; }
      case 2: case 3: case 4: return r.nextInt() >> r.nextInt(32);
      case 5: case 6: { int v = (r.nextInt(1 << 24) << 1 | 1 | 1 << 24) << r.nextInt(7);  // odd 25-bit: tie
                        v += r.nextInt(3) - 1; return r.nextBoolean() ? v : -v; }
      default: return r.nextInt();
    }
  }

  static long genL(SplittableRandom r) {
    switch (r.nextInt(10)) {
      case 0: case 1: { long[] c = {0, 1, -1, Long.MIN_VALUE, Long.MAX_VALUE, Long.MIN_VALUE + 1, Long.MAX_VALUE - 1,
                                    1L << 53, (1L << 53) + 1, (1L << 53) - 1, 1L << 24, (1L << 24) + 1,
                                    Long.MAX_VALUE - 1023, Long.MAX_VALUE - 1024, Long.MAX_VALUE - 512,
                                    Integer.MIN_VALUE, Integer.MAX_VALUE};
                        return c[r.nextInt(c.length)]; }
      case 2: case 3: return r.nextLong() >> r.nextInt(64);
      case 4: case 5: { long v = ((r.nextLong() & ((1L << 24) - 1)) << 1 | 1 | 1L << 24) << r.nextInt(39);
                        v += r.nextInt(3) - 1; return r.nextBoolean() ? v : -v; }
      case 6: case 7: { long v = ((r.nextLong() & ((1L << 53) - 1)) << 1 | 1 | 1L << 53) << r.nextInt(10);
                        v += r.nextInt(3) - 1; return r.nextBoolean() ? v : -v; }
      default: return r.nextLong();
    }
  }

  static String fh(int x) { return String.format("%08x", x); }
  static String dh(long x) { return String.format("%016x", x); }

  static String genLine(String op, SplittableRandom r) {
    switch (op) {
      case "fadd": case "fsub": case "fmul": case "fdiv": case "frem": case "fcmpl": case "fcmpg": {
        int a = genF(r); int b = genF2(r, a);
        if (r.nextBoolean()) { int t = a; a = b; b = t; }
        return fh(a) + " " + fh(b);
      }
      case "dadd": case "dsub": case "dmul": case "ddiv": case "drem": case "dcmpl": case "dcmpg": {
        long a = genD(r); long b = genD2(r, a);
        if (r.nextBoolean()) { long t = a; a = b; b = t; }
        return dh(a) + " " + dh(b);
      }
      case "fneg": case "fneg_raw": case "f2d": return fh(genF(r));
      case "dneg": case "dneg_raw": return dh(genD(r));
      case "d2f": return dh(r.nextBoolean() ? floatish(r) : genD(r));
      case "f2i": case "f2l": return fh(genFconv(r));
      case "d2i": case "d2l": return dh(genDconv(r));
      case "i2f": case "i2d": return Integer.toString(genI(r));
      case "l2f": case "l2d": return Long.toString(genL(r));
      default: throw new IllegalArgumentException(op);
    }
  }

  // ------------------------------------------------------------ evaluation

  static String F(float x) { return Integer.toHexString(Float.floatToIntBits(x)); }
  static String D(double x) { return Long.toHexString(Double.doubleToLongBits(x)); }
  static float pf(String s) { return Float.intBitsToFloat(Integer.parseUnsignedInt(s, 16)); }
  static double pd(String s) { return Double.longBitsToDouble(Long.parseUnsignedLong(s, 16)); }

  static int fcmpl(float a, float b) { return a > b ? 1 : a == b ? 0 : -1; }
  static int fcmpg(float a, float b) { return a < b ? -1 : a == b ? 0 : 1; }
  static int dcmpl(double a, double b) { return a > b ? 1 : a == b ? 0 : -1; }
  static int dcmpg(double a, double b) { return a < b ? -1 : a == b ? 0 : 1; }

  static String eval(String op, String[] t) {
    switch (op) {
      case "fadd": return F(pf(t[0]) + pf(t[1]));
      case "fsub": return F(pf(t[0]) - pf(t[1]));
      case "fmul": return F(pf(t[0]) * pf(t[1]));
      case "fdiv": return F(pf(t[0]) / pf(t[1]));
      case "frem": return F(pf(t[0]) % pf(t[1]));
      case "fneg": return F(-pf(t[0]));
      case "fneg_raw": return Integer.toHexString(Float.floatToRawIntBits(-pf(t[0])));
      case "dadd": return D(pd(t[0]) + pd(t[1]));
      case "dsub": return D(pd(t[0]) - pd(t[1]));
      case "dmul": return D(pd(t[0]) * pd(t[1]));
      case "ddiv": return D(pd(t[0]) / pd(t[1]));
      case "drem": return D(pd(t[0]) % pd(t[1]));
      case "dneg": return D(-pd(t[0]));
      case "dneg_raw": return Long.toHexString(Double.doubleToRawLongBits(-pd(t[0])));
      case "i2f": return F((float) Integer.parseInt(t[0]));
      case "i2d": return D((double) Integer.parseInt(t[0]));
      case "l2f": return F((float) Long.parseLong(t[0]));
      case "l2d": return D((double) Long.parseLong(t[0]));
      case "f2d": return D((double) pf(t[0]));
      case "d2f": return F((float) pd(t[0]));
      case "f2i": return Integer.toString((int) pf(t[0]));
      case "f2l": return Long.toString((long) pf(t[0]));
      case "d2i": return Integer.toString((int) pd(t[0]));
      case "d2l": return Long.toString((long) pd(t[0]));
      case "fcmpl": return Integer.toString(fcmpl(pf(t[0]), pf(t[1])));
      case "fcmpg": return Integer.toString(fcmpg(pf(t[0]), pf(t[1])));
      case "dcmpl": return Integer.toString(dcmpl(pd(t[0]), pd(t[1])));
      case "dcmpg": return Integer.toString(dcmpg(pd(t[0]), pd(t[1])));
      default: throw new IllegalArgumentException(op);
    }
  }

  public static void main(String[] args) throws IOException {
    if (args[0].equals("gen")) {
      File dir = new File(args[1]); dir.mkdirs();
      int n = Integer.parseInt(args[2]); long seed = Long.parseLong(args[3]);
      for (String op : OPS) {
        SplittableRandom r = new SplittableRandom(seed ^ (op.hashCode() * 0x9E3779B97F4A7C15L));
        try (Writer w = new BufferedWriter(new OutputStreamWriter(
                 new FileOutputStream(new File(dir, op + ".in")), StandardCharsets.US_ASCII), 1 << 16)) {
          for (int i = 0; i < n; i++) { w.write(genLine(op, r)); w.write('\n'); }
        }
      }
    } else if (args[0].equals("eval")) {
      File dir = new File(args[1]);
      String[] ops = args.length > 2 ? java.util.Arrays.copyOfRange(args, 2, args.length) : OPS;
      for (String op : ops) {
        try (BufferedReader in = new BufferedReader(new InputStreamReader(
                 new FileInputStream(new File(dir, op + ".in")), StandardCharsets.US_ASCII), 1 << 16);
             Writer w = new BufferedWriter(new OutputStreamWriter(
                 new FileOutputStream(new File(dir, op + ".java")), StandardCharsets.US_ASCII), 1 << 16)) {
          String line;
          while ((line = in.readLine()) != null) { w.write(eval(op, line.split(" "))); w.write('\n'); }
        }
      }
    } else throw new IllegalArgumentException(args[0]);
  }
}

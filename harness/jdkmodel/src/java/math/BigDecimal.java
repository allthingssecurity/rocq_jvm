/*
 * rocq-jvm model of java.math.BigDecimal (clean-room, Apache-2.0).
 * Representation as in JDK 21: the unscaled value (a long "compact" value, Long.MIN_VALUE meaning
 * "does not fit", and/or a BigInteger) and the scale; precision is a cache. The arithmetic is exact
 * integer arithmetic on the unscaled values (java.math.BigInteger, i.e. the ModelBig natives),
 * followed by JDK 21's rounding (all RoundingModes, MathContext precision) and its choice of the
 * result's scale (preferred scales, trailing-zero stripping, the X3.274 pow algorithm, the
 * Newton iteration of sqrt from Math.sqrt's first guess). Results follow JDK 21's object identity
 * where the JDK returns an operand or a cached constant (valueOf caches 0..10 at scale 0 and zero
 * at scales 0..15). Exceptions and messages are JDK 21's, including those whose text depends on
 * the JDK's internal path (division by a zero divisor with an explicit scale: "/ by zero" or
 * "BigInteger divide by zero"; checkScale's "Overflow"/"Underflow"; powers of ten above
 * 10^536870919: "BigInteger would overflow supported range") and HotSpot's helpful
 * NullPointerException messages of the JDK's implicit null checks (thrown explicitly here).
 * STUCK (no claim): powers of ten above 10^100000 that a result needs, strings longer than 10^6
 * characters.
 * Not followed: the identity of the BigInteger returned by unscaledValue()/toBigInteger() for
 * values the JDK keeps inflated although they fit in a long (a fresh BigInteger here).
 */
package java.math;

public class BigDecimal extends Number implements Comparable<BigDecimal> {
    private static final long serialVersionUID = 6108874887143696463L;

    static final long INFLATED = Long.MIN_VALUE;
    private static final BigInteger INFLATED_BIGINT = BigInteger.valueOf(INFLATED);
    static final int POW_BOUND = 100000;
    static final int TEN_POW_OVERFLOW = 536870920;

    private BigInteger intVal;
    private int scale;
    private transient int precision;
    private transient String stringCache;
    private final transient long intCompact;

    BigDecimal(BigInteger intVal, long val, int scale, int prec) {
        this.scale = scale;
        this.precision = prec;
        this.intCompact = val;
        this.intVal = intVal;
    }

    private static final BigDecimal[] ZERO_THROUGH_TEN = new BigDecimal[11];
    private static final BigDecimal[] ZERO_SCALED_BY = new BigDecimal[16];

    static {
        for (int i = 0; i <= 10; i++) ZERO_THROUGH_TEN[i] = new BigDecimal(BigInteger.valueOf(i), i, 0, i == 10 ? 2 : 1);
        ZERO_SCALED_BY[0] = ZERO_THROUGH_TEN[0];
        for (int i = 1; i < 16; i++) ZERO_SCALED_BY[i] = new BigDecimal(BigInteger.ZERO, 0, i, 1);
    }

    public static final BigDecimal ZERO = ZERO_THROUGH_TEN[0];
    public static final BigDecimal ONE = ZERO_THROUGH_TEN[1];
    public static final BigDecimal TWO = ZERO_THROUGH_TEN[2];
    public static final BigDecimal TEN = ZERO_THROUGH_TEN[10];
    private static final BigDecimal ONE_TENTH = valueOf(1L, 1);
    private static final BigDecimal ONE_HALF = valueOf(5L, 1);

    @Deprecated(since = "9") public static final int ROUND_UP = 0;
    @Deprecated(since = "9") public static final int ROUND_DOWN = 1;
    @Deprecated(since = "9") public static final int ROUND_CEILING = 2;
    @Deprecated(since = "9") public static final int ROUND_FLOOR = 3;
    @Deprecated(since = "9") public static final int ROUND_HALF_UP = 4;
    @Deprecated(since = "9") public static final int ROUND_HALF_DOWN = 5;
    @Deprecated(since = "9") public static final int ROUND_HALF_EVEN = 6;
    @Deprecated(since = "9") public static final int ROUND_UNNECESSARY = 7;

    // ================================================================ helpers

    private static NullPointerException npeField(String field, String var) {
        return BigInteger.npeField(field, var);
    }

    private static NullPointerException npeInvoke(String method, String var) {
        return BigInteger.npeInvoke(method, var);
    }

    private static int mcPrecision(MathContext mc) {
        if (mc == null) throw npeField("precision", "mc");
        return mc.precision;
    }

    private static int oldMode(RoundingMode roundingMode) {
        if (roundingMode == null) throw npeField("oldMode", "roundingMode");
        return roundingMode.oldMode;
    }

    static long compactValFor(BigInteger b) {
        int[] m = b.mag;
        if (m.length == 0) return 0;
        if (m.length > 2 || (m.length == 2 && m[0] < 0)) return INFLATED;
        long u = m.length == 2 ? ((m[1] & 0xffffffffL) + ((long) m[0] << 32)) : (m[0] & 0xffffffffL);
        return b.signum < 0 ? -u : u;
    }

    private BigInteger inflated() {
        if (intVal == null) return BigInteger.valueOf(intCompact);
        return intVal;
    }

    /** the unscaled value for arithmetic */
    private BigInteger u() {
        return intVal != null ? intVal : BigInteger.valueOf(intCompact);
    }

    static BigDecimal zeroValueOf(int scale) {
        if (scale >= 0 && scale < ZERO_SCALED_BY.length) return ZERO_SCALED_BY[scale];
        return new BigDecimal(BigInteger.ZERO, 0, scale, 1);
    }

    /** the JDK's valueOf for a result held as a BigInteger (zero and small integers cached) */
    static BigDecimal vof(BigInteger v, int scale) {
        long c = compactValFor(v);
        if (c == 0) return zeroValueOf(scale);
        if (c != INFLATED) {
            if (scale == 0 && c > 0 && c <= 10) return ZERO_THROUGH_TEN[(int) c];
            return new BigDecimal(null, c, scale, 0);
        }
        return new BigDecimal(v, INFLATED, scale, 0);
    }

    /** a new object for a result (the JDK's new BigDecimal(intVal, compact, scale, prec)) */
    private static BigDecimal fresh(BigInteger v, int scale, int prec) {
        long c = compactValFor(v);
        return new BigDecimal(c == INFLATED ? v : null, c, scale, prec);
    }

    /** decimal digits of |v| (1 for 0) */
    static int digits(BigInteger v) {
        if (v.signum == 0) return 1;
        String t = ModelBig.toStr(v.mag.length == 0 ? new int[] {0} : magEnc(v), 10);
        return t.length();
    }

    private static int[] magEnc(BigInteger v) {
        int[] e = v.enc();
        e[0] = 1;
        return e;
    }

    /** 10^n for 0 <= n where the JDK reaches bigTenToThe(n) */
    static BigInteger tenPow(int n) {
        if (n <= 0) return n == 0 ? BigInteger.ONE : BigInteger.ZERO;
        if (n >= TEN_POW_OVERFLOW) throw new ArithmeticException("BigInteger would overflow supported range");
        if (n > POW_BOUND) throw ModelStuck.unsupported("BigDecimal: power of ten beyond the model bound");
        return BigInteger.make(ModelBig.op2(11, new int[] {1, 10}, BigInteger.encLong(n)));
    }

    /** the overflow of bigTenToThe(n) (n >= 19), without computing the power */
    private static void checkTenPow(int n) {
        if (n >= TEN_POW_OVERFLOW) throw new ArithmeticException("BigInteger would overflow supported range");
    }

    /** v * 10^n (n <= 0: v) */
    private static BigInteger mulTen(BigInteger v, int n) {
        if (n <= 0 || v.signum == 0) return v;
        return v.multiply(tenPow(n));
    }

    private static int checkScaleNonZero(long val) {
        int asInt = (int) val;
        if (asInt != val) throw new ArithmeticException(asInt > 0 ? "Underflow" : "Overflow");
        return asInt;
    }

    /** the JDK's static checkScale(value, val): saturates for a zero value */
    private static int checkScale(boolean nonZero, long val) {
        int asInt = (int) val;
        if (asInt != val) {
            asInt = val > Integer.MAX_VALUE ? Integer.MAX_VALUE : Integer.MIN_VALUE;
            if (nonZero) throw new ArithmeticException(asInt > 0 ? "Underflow" : "Overflow");
        }
        return asInt;
    }

    /** the JDK's instance checkScale */
    private int checkScale(long val) {
        return checkScale(signum() != 0, val);
    }

    private static int saturateLong(long s) {
        int i = (int) s;
        return (s == i) ? i : (s < 0 ? Integer.MIN_VALUE : Integer.MAX_VALUE);
    }

    private static boolean needIncrement(int mode, int qsign, int cmpFracHalf, boolean oddQuot) {
        switch (mode) {
            case ROUND_UNNECESSARY: throw new ArithmeticException("Rounding necessary");
            case ROUND_UP: return true;
            case ROUND_DOWN: return false;
            case ROUND_CEILING: return qsign > 0;
            case ROUND_FLOOR: return qsign < 0;
            default:
                if (cmpFracHalf < 0) return false;
                if (cmpFracHalf > 0) return true;
                if (mode == ROUND_HALF_DOWN) return false;
                if (mode == ROUND_HALF_UP) return true;
                return oddQuot;
        }
    }

    /** n / d rounded (d != 0); exact[0] tells whether the division was exact */
    private static BigInteger divRound(BigInteger n, BigInteger d, int mode, boolean[] exact) {
        BigInteger[] qr = n.divideAndRemainder(d);
        if (qr[1].signum == 0) {
            if (exact != null) exact[0] = true;
            return qr[0];
        }
        if (exact != null) exact[0] = false;
        int qsign = n.signum == d.signum ? 1 : -1;
        int cmpHalf = qr[1].abs().shiftLeft(1).compareMagnitude(d);
        boolean odd = qr[0].testBit(0);
        return needIncrement(mode, qsign, cmpHalf, odd) ? qr[0].add(BigInteger.valueOf(qsign)) : qr[0];
    }

    /** n / (d * 10^k) rounded, k >= 0, without computing 10^k when the quotient is below 1/2 */
    private static BigInteger divRoundTen(BigInteger n, BigInteger d, int k, int mode, boolean[] exact) {
        if (k > 0 && n.signum != 0 && (long) digits(n) + 2 <= (long) digits(d) + k) {
            checkTenPow(k);
            if (exact != null) exact[0] = false;
            int qsign = n.signum == d.signum ? 1 : -1;
            return needIncrement(mode, qsign, -1, false) ? BigInteger.valueOf(qsign) : BigInteger.ZERO;
        }
        return divRound(n, mulTen(d, k), mode, exact);
    }

    /** the JDK's doRound(BigInteger intVal, int scale, MathContext mc): valueOf semantics */
    private static BigDecimal roundVal(BigInteger v, int scale, MathContext mc) {
        int mcp = mc.precision;
        if (mcp > 0) {
            int prec = digits(v);
            int drop = prec - mcp;
            while (drop > 0) {
                scale = checkScaleNonZero((long) scale - drop);
                v = divRoundTen(v, BigInteger.ONE, drop, mc.roundingMode.oldMode, null);
                prec = digits(v);
                drop = prec - mcp;
            }
        }
        return vof(v, scale);
    }

    /** the JDK's doRound(BigDecimal val, MathContext mc): val itself when no digit is dropped */
    private static BigDecimal roundBD(BigDecimal val, MathContext mc) {
        int mcp = mc.precision;
        if (mcp > 0) {
            int prec = val.precision();
            int drop = prec - mcp;
            if (drop <= 0) return val;
            BigInteger v = val.u();
            int scale = val.scale;
            while (drop > 0) {
                scale = checkScaleNonZero((long) scale - drop);
                v = divRoundTen(v, BigInteger.ONE, drop, mc.roundingMode.oldMode, null);
                prec = digits(v);
                drop = prec - mcp;
            }
            return fresh(v, scale, prec);
        }
        return val;
    }

    /** the JDK's createAndStripZerosToMatchScale (valueOf semantics) */
    private static BigDecimal stripZeros(BigInteger v, int scale, long preferredScale) {
        while (v.compareMagnitude(BigInteger.TEN) >= 0 && scale > preferredScale) {
            if (v.testBit(0)) break;
            BigInteger[] qr = v.divideAndRemainder(BigInteger.TEN);
            if (qr[1].signum != 0) break;
            v = qr[0];
            scale = checkScale(v.signum != 0, (long) scale - 1);
        }
        return vof(v, scale);
    }

    /** the JDK's divideAndRound(dividend, divisor, scale, mode, preferredScale) */
    private static BigDecimal divideAndRound(BigInteger n, BigInteger d, int k, int scale, int mode, int preferredScale) {
        boolean[] exact = new boolean[1];
        BigInteger q = divRoundTen(n, d, k, mode, exact);
        if (exact[0] && preferredScale != scale) return stripZeros(q, scale, preferredScale);
        return vof(q, scale);
    }

    private static void checkFromIndexSizeNfe(int from, int size, int length) {
        if ((length | from | size) < 0 || size > length - from)
            throw new NumberFormatException("Bad offset or len arguments for char[] input.");
    }

    // ================================================================ constructors

    private BigDecimal(BigDecimal src, boolean copy) {
        this.intVal = src.intVal;
        this.intCompact = src.intCompact;
        this.scale = src.scale;
        this.precision = src.precision;
    }

    public BigDecimal(char[] in, int offset, int len) {
        this(in, offset, len, MathContext.UNLIMITED);
    }

    public BigDecimal(char[] in, int offset, int len, MathContext mc) {
        this(parse(in, offset, len, mc), true);
    }

    private static char at(char[] in, int i) {
        if (i < 0 || i >= in.length) {
            NumberFormatException e = new NumberFormatException();
            e.initCause(new ArrayIndexOutOfBoundsException("Index " + i + " out of bounds for length " + in.length));
            throw e;
        }
        return in[i];
    }

    private static int dec(char c) {
        return Character.digit(c, 10);
    }

    private static BigDecimal parse(char[] in, int offset, int len, MathContext mc) {
        if (in == null) throw BigInteger.npeArray("in");
        checkFromIndexSizeNfe(offset, len, in.length);
        int prec = 0;
        long scl = 0;
        boolean isneg = false;
        char c0 = at(in, offset);
        if (c0 == '-') {
            isneg = true;
            offset++;
            len--;
        } else if (c0 == '+') {
            offset++;
            len--;
        }
        boolean dot = false;
        boolean compact = len <= 18;
        int[] ds = new int[len > 0 ? len : 0];
        int nd = 0; // digits collected (leading zeros dropped)
        for (; len > 0; offset++, len--) {
            char c = in[offset];
            int d = -1;
            if (c >= '0' && c <= '9') d = c - '0';
            else if (c != '.' && Character.isDigit(c)) d = dec(c);
            if (d >= 0) {
                if (d == 0) {
                    if (prec == 0) prec = 1;
                    else if (nd != 0) {
                        ds[nd++] = 0;
                        ++prec;
                    }
                } else {
                    if (prec != 1 || nd != 0) ++prec;
                    ds[nd++] = d;
                }
                if (dot) ++scl;
            } else if (c == '.') {
                if (dot) throw new NumberFormatException("Character array contains more than one decimal point.");
                dot = true;
            } else if (c == 'e' || c == 'E') {
                scl -= parseExp(in, offset, len);
                break;
            } else if (compact) {
                throw new NumberFormatException("Character " + c
                    + " is neither a decimal digit number, decimal point, nor \"e\" notation exponential mark.");
            } else {
                throw new NumberFormatException("Character array is missing \"e\" notation exponential mark.");
            }
        }
        if (prec == 0) throw new NumberFormatException("No digits found.");
        int[] digs = new int[nd];
        System.arraycopy(ds, 0, digs, 0, nd);
        int[] e = nd == 0 ? new int[] {0} : ModelBig.fromDigits(digs, 10);
        if (isneg && e[0] != 0) e[0] = -1;
        BigInteger v = BigInteger.make(e);
        int mcp = mcPrecision(mc);
        boolean rounded = false;
        if (mcp > 0 && prec > mcp) {
            int drop = prec - mcp;
            while (drop > 0) {
                scl -= drop;
                v = divRoundTen(v, BigInteger.ONE, drop, mc.roundingMode.oldMode, null);
                prec = digits(v);
                drop = prec - mcp;
            }
            rounded = true;
        }
        if ((int) scl != scl) throw new NumberFormatException("Exponent overflow.");
        long cv = compactValFor(v);
        // the JDK keeps the BigInteger for long input (more than 18 characters) unless rounded to a long
        BigInteger keep = cv == INFLATED || (!compact && !rounded) ? v : null;
        return new BigDecimal(keep, cv, (int) scl, prec);
    }

    private static long parseExp(char[] in, int offset, int len) {
        long exp = 0;
        offset++;
        char c = at(in, offset);
        len--;
        boolean negexp = c == '-';
        if (negexp || c == '+') {
            offset++;
            c = at(in, offset);
            len--;
        }
        if (len <= 0) throw new NumberFormatException("No exponent digits.");
        while (len > 10 && (c == '0' || dec(c) == 0)) {
            offset++;
            c = at(in, offset);
            len--;
        }
        if (len > 10) throw new NumberFormatException("Too many nonzero exponent digits.");
        for (;; len--) {
            int v;
            if (c >= '0' && c <= '9') {
                v = c - '0';
            } else {
                v = dec(c);
                if (v < 0) throw new NumberFormatException("Not a digit.");
            }
            exp = exp * 10 + v;
            if (len == 1) break;
            offset++;
            c = at(in, offset);
        }
        return negexp ? -exp : exp;
    }

    private static int lenOf(char[] in) {
        if (in == null) throw BigInteger.npeArray("in");
        return in.length;
    }

    public BigDecimal(char[] in) {
        this(in, 0, lenOf(in));
    }

    public BigDecimal(char[] in, MathContext mc) {
        this(in, 0, lenOf(in), mc);
    }

    private static char[] chars(String val) {
        if (val == null) throw npeInvoke("String.toCharArray()", "val");
        return val.toCharArray();
    }

    public BigDecimal(String val) {
        this(chars(val), 0, val.length());
    }

    public BigDecimal(String val, MathContext mc) {
        this(chars(val), 0, val.length(), mc);
    }

    public BigDecimal(double val) {
        this(val, MathContext.UNLIMITED);
    }

    public BigDecimal(double val, MathContext mc) {
        this(fromDouble(val, mc), true);
    }

    private static BigDecimal fromDouble(double val, MathContext mc) {
        if (Double.isInfinite(val) || Double.isNaN(val)) throw new NumberFormatException("Infinite or NaN");
        long bits = Double.doubleToLongBits(val);
        int sign = (bits >> 63) == 0 ? 1 : -1;
        int exponent = (int) ((bits >> 52) & 0x7ffL);
        long significand = exponent == 0 ? (bits & ((1L << 52) - 1)) << 1 : (bits & ((1L << 52) - 1)) | (1L << 52);
        exponent -= 1075;
        if (significand == 0) return new BigDecimal(BigInteger.ZERO, 0, 0, 1);
        while ((significand & 1) == 0) {
            significand >>= 1;
            exponent++;
        }
        int scl = 0;
        BigInteger rb = null;
        BigInteger v = BigInteger.valueOf(sign * significand);
        if (exponent < 0) {
            rb = BigInteger.valueOf(5).pow(-exponent).multiply(v);
            scl = -exponent;
            v = rb;
        } else if (exponent > 0) {
            rb = BigInteger.TWO.pow(exponent).multiply(v);
            v = rb;
        }
        long compactVal = compactValFor(v);
        int prec = 0;
        int mcp = mcPrecision(mc);
        if (mcp > 0) {
            prec = digits(v);
            int drop = prec - mcp;
            while (drop > 0) {
                scl = checkScaleNonZero((long) scl - drop);
                v = divRoundTen(v, BigInteger.ONE, drop, mc.roundingMode.oldMode, null);
                prec = digits(v);
                drop = prec - mcp;
            }
            compactVal = compactValFor(v);
            rb = compactVal == INFLATED ? v : null;
        }
        return new BigDecimal(rb, compactVal, scl, prec);
    }

    private static BigInteger toStrictBigInteger(BigInteger val) {
        if (val == null) throw npeInvoke("Object.getClass()", "val");
        return val.getClass() == BigInteger.class ? val : new BigInteger(val.toByteArray().clone());
    }

    public BigDecimal(BigInteger val) {
        this.scale = 0;
        this.intVal = toStrictBigInteger(val);
        this.intCompact = compactValFor(intVal);
    }

    public BigDecimal(BigInteger val, MathContext mc) {
        this(toStrictBigInteger(val), 0, mc);
    }

    public BigDecimal(BigInteger unscaledVal, int scale) {
        this.intVal = toStrictBigInteger(unscaledVal);
        this.intCompact = compactValFor(this.intVal);
        this.scale = scale;
    }

    public BigDecimal(BigInteger unscaledVal, int scale, MathContext mc) {
        this(fromBig(toStrictBigInteger(unscaledVal), scale, mc), true);
    }

    /** the constructors' rounding loop (checkScaleNonZero on each drop) */
    private static BigDecimal fromBig(BigInteger v, int scale, MathContext mc) {
        int mcp = mcPrecision(mc);
        int prec = 0;
        BigInteger keep = v;
        if (mcp > 0) {
            prec = digits(v);
            int drop = prec - mcp;
            while (drop > 0) {
                scale = checkScaleNonZero((long) scale - drop);
                v = divRoundTen(v, BigInteger.ONE, drop, mc.roundingMode.oldMode, null);
                prec = digits(v);
                drop = prec - mcp;
            }
            keep = compactValFor(v) == INFLATED ? v : null;
        }
        return new BigDecimal(keep, compactValFor(v), scale, prec);
    }

    public BigDecimal(int val) {
        this.intCompact = val;
        this.scale = 0;
        this.intVal = null;
    }

    public BigDecimal(int val, MathContext mc) {
        this(fromBig(BigInteger.valueOf(val), 0, mc).compactCopy(), true);
    }

    public BigDecimal(long val) {
        this.intCompact = val;
        this.intVal = (val == INFLATED) ? INFLATED_BIGINT : null;
        this.scale = 0;
    }

    public BigDecimal(long val, MathContext mc) {
        this(fromLong(val, mc), true);
    }

    private static BigDecimal fromLong(long val, MathContext mc) {
        BigDecimal r = fromBig(BigInteger.valueOf(val), 0, mc);
        if (val == INFLATED && mc.precision == 0) return new BigDecimal(INFLATED_BIGINT, INFLATED, 0, 0);
        return r.compactCopy();
    }

    /** the same value with the BigInteger dropped when it fits in a long */
    private BigDecimal compactCopy() {
        if (intCompact != INFLATED) intVal = null;
        return this;
    }

    // ================================================================ static factories

    public static BigDecimal valueOf(long unscaledVal, int scale) {
        if (scale == 0) return valueOf(unscaledVal);
        if (unscaledVal == 0) return zeroValueOf(scale);
        return new BigDecimal(unscaledVal == INFLATED ? INFLATED_BIGINT : null, unscaledVal, scale, 0);
    }

    public static BigDecimal valueOf(long val) {
        if (val >= 0 && val < ZERO_THROUGH_TEN.length) return ZERO_THROUGH_TEN[(int) val];
        if (val != INFLATED) return new BigDecimal(null, val, 0, 0);
        return new BigDecimal(INFLATED_BIGINT, val, 0, 0);
    }

    /** the JDK's package-private valueOf(long, int, int) */
    private static BigDecimal valueOf(long unscaledVal, int scale, int prec) {
        if (scale == 0 && unscaledVal >= 0 && unscaledVal < ZERO_THROUGH_TEN.length) return ZERO_THROUGH_TEN[(int) unscaledVal];
        if (unscaledVal == 0) return zeroValueOf(scale);
        return new BigDecimal(unscaledVal == INFLATED ? INFLATED_BIGINT : null, unscaledVal, scale, prec);
    }

    public static BigDecimal valueOf(double val) {
        return new BigDecimal(Double.toString(val));
    }

    // ================================================================ add, subtract, multiply

    /** the exact sum at the larger scale (the JDK's add(xs, scale1, ys, scale2) variants) */
    private static BigDecimal addExact(BigInteger x, int s1, BigInteger y, int s2) {
        long sdiff = (long) s1 - s2;
        if (sdiff == 0) return vof(x.add(y), s1);
        if (sdiff < 0) {
            int raise = checkScale(x.signum != 0, -sdiff);
            return vof(mulTen(x, raise).add(y), s2);
        }
        int raise = checkScale(y.signum != 0, sdiff);
        return vof(x.add(mulTen(y, raise)), s1);
    }

    public BigDecimal add(BigDecimal augend) {
        if (augend == null) throw npeField("intCompact", "augend");
        return addExact(u(), scale, augend.u(), augend.scale);
    }

    public BigDecimal add(BigDecimal augend, MathContext mc) {
        int mcp = mcPrecision(mc);
        if (mcp == 0) return add(augend);
        if (augend == null) throw npeInvoke("java.math.BigDecimal.signum()", "augend");
        BigDecimal lhs = this;
        boolean lhsIsZero = lhs.signum() == 0;
        boolean augendIsZero = augend.signum() == 0;
        if (lhsIsZero || augendIsZero) {
            int preferredScale = Math.max(lhs.scale, augend.scale);
            if (lhsIsZero && augendIsZero) return zeroValueOf(preferredScale);
            BigDecimal result = lhsIsZero ? roundBD(augend, mc) : roundBD(lhs, mc);
            if (result.scale == preferredScale) return result;
            if (result.scale > preferredScale) return stripZeros(result.u(), result.scale, preferredScale);
            int precisionDiff = mcp - result.precision();
            int scaleDiff = preferredScale - result.scale;
            if (precisionDiff >= scaleDiff) return result.setScale(preferredScale);
            return result.setScale(result.scale + precisionDiff);
        }
        long padding = (long) lhs.scale - augend.scale;
        if (padding != 0) {
            // the JDK's preAlign: a small operand below the result's precision is replaced by one
            // unit of its sign three digits beyond it (the rounding is the same)
            BigDecimal big;
            BigDecimal small;
            if (padding < 0) {
                big = lhs;
                small = augend;
            } else {
                big = augend;
                small = lhs;
            }
            long estResultUlpScale = (long) big.scale - big.precision() + mcp;
            long smallHighDigitPos = (long) small.scale - small.precision() + 1;
            if (smallHighDigitPos > big.scale + 2 && smallHighDigitPos > estResultUlpScale + 2) {
                small = valueOf(small.signum(), this.checkScale(Math.max(big.scale, estResultUlpScale) + 3));
            }
            lhs = big;
            augend = small;
            if (lhs.scale < augend.scale) lhs = lhs.setScale(augend.scale, ROUND_UNNECESSARY);
            else if (augend.scale < lhs.scale) augend = augend.setScale(lhs.scale, ROUND_UNNECESSARY);
        }
        return roundVal(lhs.u().add(augend.u()), lhs.scale, mc);
    }

    public BigDecimal subtract(BigDecimal subtrahend) {
        if (subtrahend == null) throw npeField("intCompact", "subtrahend");
        return addExact(u(), scale, subtrahend.u().negate(), subtrahend.scale);
    }

    public BigDecimal subtract(BigDecimal subtrahend, MathContext mc) {
        if (mcPrecision(mc) == 0) return subtract(subtrahend);
        if (subtrahend == null) throw npeInvoke("java.math.BigDecimal.negate()", "subtrahend");
        return add(subtrahend.negate(), mc);
    }

    public BigDecimal multiply(BigDecimal multiplicand) {
        if (multiplicand == null) throw npeField("scale", "multiplicand");
        int productScale = checkScale((long) scale + multiplicand.scale);
        return vof(u().multiply(multiplicand.u()), productScale);
    }

    public BigDecimal multiply(BigDecimal multiplicand, MathContext mc) {
        if (mcPrecision(mc) == 0) return multiply(multiplicand);
        if (multiplicand == null) throw npeField("scale", "multiplicand");
        int productScale = checkScale((long) scale + multiplicand.scale);
        return roundVal(u().multiply(multiplicand.u()), productScale, mc);
    }

    // ================================================================ division

    private static void checkMode(int roundingMode) {
        if (roundingMode < ROUND_UP || roundingMode > ROUND_UNNECESSARY)
            throw new IllegalArgumentException("Invalid rounding mode");
    }

    @Deprecated(since = "9")
    public BigDecimal divide(BigDecimal divisor, int scale, int roundingMode) {
        checkMode(roundingMode);
        if (divisor == null) throw npeField("intCompact", "divisor");
        return divideScaled(this, divisor, scale, roundingMode);
    }

    private static boolean fitsTimesTen(long val, int n) {
        // the JDK's longMultiplyPowerTen(val, n) != INFLATED
        if (val == 0 || n <= 0) return true;
        if (n >= 19) return false;
        long bound = Long.MAX_VALUE;
        for (int i = 0; i < n; i++) bound /= 10;
        return val == 1 || Math.abs(val) <= bound;
    }

    /** the JDK's divide(dividend, dividendScale, divisor, divisorScale, scale, roundingMode) */
    private static BigDecimal divideScaled(BigDecimal x, BigDecimal y, int scale, int mode) {
        BigInteger xs = x.u();
        BigInteger ys = y.u();
        int ds = x.scale;
        int dvs = y.scale;
        boolean xCompact = x.intCompact != INFLATED;
        if (checkScale(xs.signum != 0, (long) scale + dvs) > ds) {
            int newScale = scale + dvs;
            int raise = newScale - ds;
            if (ys.signum == 0) {
                // a long division ("/ by zero") when the scaled dividend fits in a long, else
                // MutableBigInteger's (after computing 10^raise)
                if (xCompact && raise < 19 && fitsTimesTen(x.intCompact, raise)) throw new ArithmeticException("/ by zero");
                checkTenPow(raise);
                throw new ArithmeticException("BigInteger divide by zero");
            }
            // a zero dividend: the JDK still multiplies it by bigTenToThe(raise) unless raise < 19
            if (xs.signum == 0 && raise >= 19) checkTenPow(raise);
            return divideAndRound(mulTen(xs, raise), ys, 0, scale, mode, scale);
        } else {
            int newScale = checkScale(ys.signum != 0, (long) ds - scale);
            int raise = newScale - dvs;
            if (ys.signum == 0) {
                if (xCompact && raise < 19) throw new ArithmeticException("/ by zero");
                checkTenPow(raise);
                throw new ArithmeticException("BigInteger divide by zero");
            }
            return divideAndRound(xs, ys, raise > 0 ? raise : 0, scale, mode, scale);
        }
    }

    public BigDecimal divide(BigDecimal divisor, int scale, RoundingMode roundingMode) {
        return divide(divisor, scale, oldMode(roundingMode));
    }

    @Deprecated(since = "9")
    public BigDecimal divide(BigDecimal divisor, int roundingMode) {
        return this.divide(divisor, scale, roundingMode);
    }

    public BigDecimal divide(BigDecimal divisor, RoundingMode roundingMode) {
        return this.divide(divisor, scale, oldMode(roundingMode));
    }

    public BigDecimal divide(BigDecimal divisor) {
        if (divisor == null) throw npeInvoke("java.math.BigDecimal.signum()", "divisor");
        if (divisor.signum() == 0) {
            if (this.signum() == 0) throw new ArithmeticException("Division undefined");
            throw new ArithmeticException("Division by zero");
        }
        int preferredScale = saturateLong((long) this.scale - divisor.scale);
        if (this.signum() == 0) return zeroValueOf(preferredScale);
        long yp = divisor.precision();
        MathContext mc = new MathContext((int) Math.min(this.precision() + (10 * yp + 2) / 3, Integer.MAX_VALUE),
            RoundingMode.UNNECESSARY);
        BigDecimal quotient;
        try {
            quotient = this.divide(divisor, mc);
        } catch (ArithmeticException e) {
            throw new ArithmeticException("Non-terminating decimal expansion; no exact representable decimal result.");
        }
        int quotientScale = quotient.scale;
        if (preferredScale > quotientScale) return quotient.setScale(preferredScale, ROUND_UNNECESSARY);
        return quotient;
    }

    public BigDecimal divide(BigDecimal divisor, MathContext mc) {
        int mcp = mcPrecision(mc);
        if (mcp == 0) return divide(divisor);
        if (divisor == null) throw npeField("scale", "divisor");
        BigDecimal dividend = this;
        long preferredScale = (long) dividend.scale - divisor.scale;
        if (divisor.signum() == 0) {
            if (dividend.signum() == 0) throw new ArithmeticException("Division undefined");
            throw new ArithmeticException("Division by zero");
        }
        if (dividend.signum() == 0) return zeroValueOf(saturateLong(preferredScale));
        int xprec = dividend.precision();
        int yprec = divisor.precision();
        BigInteger xs = dividend.u();
        BigInteger ys = divisor.u();
        // normalize to 0.1 <= x' < 1 and x' <= y' < 10 x' (compare x * 10^yprec with y * 10^xprec)
        int c;
        if (xprec <= yprec) c = mulTen(xs, yprec - xprec).compareMagnitude(ys);
        else c = xs.compareMagnitude(mulTen(ys, xprec - yprec));
        if (c > 0) yprec -= 1;
        int scl = checkScaleNonZero(preferredScale + yprec - xprec + mcp);
        long e = (long) mcp + yprec - xprec;
        checkScaleNonZero(e);
        BigInteger n;
        BigInteger d;
        int k = 0;
        if (e > 0) {
            n = mulTen(xs, (int) e);
            d = ys;
        } else {
            int newScale = checkScaleNonZero((long) xprec - mcp);
            int raise = newScale == yprec ? 0 : checkScaleNonZero((long) newScale - yprec);
            n = xs;
            d = ys;
            k = raise;
        }
        int pref = checkScaleNonZero(preferredScale);
        BigDecimal quotient = divideAndRound(n, d, k, scl, mc.roundingMode.oldMode, pref);
        return roundBD(quotient, mc);
    }

    public BigDecimal divideToIntegralValue(BigDecimal divisor) {
        if (divisor == null) throw npeField("scale", "divisor");
        int preferredScale = saturateLong((long) this.scale - divisor.scale);
        if (this.compareMagnitude(divisor) < 0) return zeroValueOf(preferredScale);
        if (this.signum() == 0 && divisor.signum() != 0) return this.setScale(preferredScale, ROUND_UNNECESSARY);
        long yp = divisor.precision();
        int maxDigits = (int) Math.min(this.precision() + (10 * yp + 2) / 3
            + Math.abs((long) this.scale - divisor.scale) + 2, Integer.MAX_VALUE);
        BigDecimal quotient = this.divide(divisor, new MathContext(maxDigits, RoundingMode.DOWN));
        if (quotient.scale > 0) {
            quotient = quotient.setScale(0, RoundingMode.DOWN);
            quotient = stripZeros(quotient.u(), quotient.scale, preferredScale);
        }
        if (quotient.scale < preferredScale) quotient = quotient.setScale(preferredScale, ROUND_UNNECESSARY);
        return quotient;
    }

    public BigDecimal divideToIntegralValue(BigDecimal divisor, MathContext mc) {
        int mcp = mcPrecision(mc);
        if (mcp == 0) return divideToIntegralValue(divisor);
        if (divisor == null) throw npeField("intCompact", "val");
        if (this.compareMagnitude(divisor) < 0) return divideToIntegralValue(divisor);
        int preferredScale = saturateLong((long) this.scale - divisor.scale);
        BigDecimal result = this.divide(divisor, new MathContext(mcp, RoundingMode.DOWN));
        if (result.scale < 0) {
            BigDecimal product = result.multiply(divisor);
            if (this.subtract(product).compareMagnitude(divisor) >= 0)
                throw new ArithmeticException("Division impossible");
        } else if (result.scale > 0) {
            result = result.setScale(0, RoundingMode.DOWN);
        }
        int precisionDiff;
        if ((preferredScale > result.scale) && (precisionDiff = mcp - result.precision()) > 0) {
            return result.setScale(result.scale + Math.min(precisionDiff, preferredScale - result.scale));
        }
        return stripZeros(result.u(), result.scale, preferredScale);
    }

    public BigDecimal remainder(BigDecimal divisor) {
        return this.divideAndRemainder(divisor)[1];
    }

    public BigDecimal remainder(BigDecimal divisor, MathContext mc) {
        return this.divideAndRemainder(divisor, mc)[1];
    }

    public BigDecimal[] divideAndRemainder(BigDecimal divisor) {
        BigDecimal[] result = new BigDecimal[2];
        result[0] = this.divideToIntegralValue(divisor);
        result[1] = this.subtract(result[0].multiply(divisor));
        return result;
    }

    public BigDecimal[] divideAndRemainder(BigDecimal divisor, MathContext mc) {
        if (mcPrecision(mc) == 0) return divideAndRemainder(divisor);
        BigDecimal[] result = new BigDecimal[2];
        result[0] = this.divideToIntegralValue(divisor, mc);
        result[1] = this.subtract(result[0].multiply(divisor));
        return result;
    }

    // ================================================================ sqrt, pow

    public BigDecimal sqrt(MathContext mc) {
        int signum = signum();
        if (signum == 1) {
            int preferredScale = this.scale / 2;
            BigDecimal zeroWithFinalPreferredScale = valueOf(0L, preferredScale);
            BigDecimal stripped = this.stripTrailingZeros();
            int strippedScale = stripped.scale;
            if (stripped.isPowerOfTen() && strippedScale % 2 == 0) {
                BigDecimal result = valueOf(1L, strippedScale / 2);
                if (result.scale != preferredScale) result = result.add(zeroWithFinalPreferredScale, mc);
                return result;
            }
            int scaleAdjust;
            int sc = stripped.scale - stripped.precision() + 1;
            if (sc % 2 == 0) scaleAdjust = sc;
            else scaleAdjust = sc - 1;
            BigDecimal working = stripped.scaleByPowerOfTen(scaleAdjust);
            BigDecimal guess = new BigDecimal(Math.sqrt(working.doubleValue()));
            int guessPrecision = 15;
            if (mc == null) throw npeInvoke("java.math.MathContext.getPrecision()", "mc");
            int originalPrecision = mc.getPrecision();
            int targetPrecision;
            if (originalPrecision == 0) {
                targetPrecision = stripped.precision() / 2 + 1;
            } else {
                RoundingMode rm = mc.getRoundingMode();
                if (rm == RoundingMode.HALF_UP || rm == RoundingMode.HALF_DOWN || rm == RoundingMode.HALF_EVEN) {
                    targetPrecision = 2 * originalPrecision;
                    if (targetPrecision < 0) targetPrecision = Integer.MAX_VALUE - 2;
                } else {
                    targetPrecision = originalPrecision;
                }
            }
            BigDecimal approx = guess;
            int workingPrecision = working.precision();
            do {
                int tmpPrecision = Math.max(Math.max(guessPrecision, targetPrecision + 2), workingPrecision);
                MathContext mcTmp = new MathContext(tmpPrecision, RoundingMode.HALF_EVEN);
                approx = ONE_HALF.multiply(approx.add(working.divide(approx, mcTmp), mcTmp));
                guessPrecision *= 2;
            } while (guessPrecision < targetPrecision + 2);
            BigDecimal result;
            RoundingMode targetRm = mc.getRoundingMode();
            if (targetRm == RoundingMode.UNNECESSARY || originalPrecision == 0) {
                RoundingMode tmpRm = (targetRm == RoundingMode.UNNECESSARY) ? RoundingMode.DOWN : targetRm;
                MathContext mcTmp = new MathContext(targetPrecision, tmpRm);
                result = approx.scaleByPowerOfTen(-scaleAdjust / 2).round(mcTmp);
                if (this.subtract(result.multiply(result)).compareTo(ZERO) != 0)
                    throw new ArithmeticException("Computed square root not exact.");
            } else {
                result = approx.scaleByPowerOfTen(-scaleAdjust / 2).round(mc);
                if (targetRm == RoundingMode.DOWN || targetRm == RoundingMode.FLOOR) {
                    if (result.multiply(result).compareTo(this) > 0) {
                        BigDecimal ulp = result.ulp();
                        if (approx.compareTo(ONE) == 0) ulp = ulp.multiply(ONE_TENTH);
                        result = result.subtract(ulp);
                    }
                } else if (targetRm == RoundingMode.UP || targetRm == RoundingMode.CEILING) {
                    if (result.multiply(result).compareTo(this) < 0) result = result.add(result.ulp());
                }
            }
            if (result.scale != preferredScale) {
                result = result.stripTrailingZeros().add(zeroWithFinalPreferredScale,
                    new MathContext(originalPrecision, RoundingMode.UNNECESSARY));
            }
            return result;
        } else {
            if (signum == -1) throw new ArithmeticException("Attempted square root of negative BigDecimal");
            return valueOf(0L, scale / 2);
        }
    }

    private boolean isPowerOfTen() {
        BigInteger v = u();
        return v.signum == 1 && v.mag.length == 1 && v.mag[0] == 1;
    }

    public BigDecimal pow(int n) {
        if (n < 0 || n > 999999999) throw new ArithmeticException("Invalid operation");
        int newScale = checkScale((long) scale * n);
        return new BigDecimal(this.inflated().pow(n), newScale);
    }

    public BigDecimal pow(int n, MathContext mc) {
        int mcp = mcPrecision(mc);
        if (mcp == 0) return pow(n);
        if (n < -999999999 || n > 999999999) throw new ArithmeticException("Invalid operation");
        if (n == 0) return ONE;
        BigDecimal lhs = this;
        MathContext workmc = mc;
        int mag = Math.abs(n);
        if (mcp > 0) {
            int elength = digits(BigInteger.valueOf(mag));
            if (elength > mcp) throw new ArithmeticException("Invalid operation");
            workmc = new MathContext(mcp + elength + 1, mc.roundingMode);
        }
        BigDecimal acc = ONE;
        boolean seenbit = false;
        for (int i = 1;; i++) {
            mag += mag;
            if (mag < 0) {
                seenbit = true;
                acc = acc.multiply(lhs, workmc);
            }
            if (i == 31) break;
            if (seenbit) acc = acc.multiply(acc, workmc);
        }
        if (n < 0) acc = ONE.divide(acc, workmc);
        return roundBD(acc, mc);
    }

    // ================================================================ sign, scale, rounding

    public BigDecimal abs() {
        return signum() < 0 ? negate() : this;
    }

    public BigDecimal abs(MathContext mc) {
        return signum() < 0 ? negate(mc) : plus(mc);
    }

    public BigDecimal negate() {
        if (intCompact == INFLATED) return new BigDecimal(intVal.negate(), INFLATED, scale, precision);
        return valueOf(-intCompact, scale, precision);
    }

    public BigDecimal negate(MathContext mc) {
        mcPrecision(mc);
        return negate().plus(mc);
    }

    public BigDecimal plus() {
        return this;
    }

    public BigDecimal plus(MathContext mc) {
        if (mcPrecision(mc) == 0) return this;
        return roundBD(this, mc);
    }

    public int signum() {
        return intCompact != INFLATED ? Long.signum(intCompact) : intVal.signum();
    }

    public int scale() {
        return scale;
    }

    public int precision() {
        int result = precision;
        if (result == 0) {
            result = digits(u());
            precision = result;
        }
        return result;
    }

    public BigInteger unscaledValue() {
        return this.inflated();
    }

    public BigDecimal round(MathContext mc) {
        return plus(mc);
    }

    public BigDecimal setScale(int newScale, RoundingMode roundingMode) {
        return setScale(newScale, oldMode(roundingMode));
    }

    @Deprecated(since = "9")
    public BigDecimal setScale(int newScale, int roundingMode) {
        checkMode(roundingMode);
        int oldScale = this.scale;
        if (newScale == oldScale) return this;
        if (this.signum() == 0) return zeroValueOf(newScale);
        if (newScale > oldScale) {
            int raise = checkScale((long) newScale - oldScale);
            if (intCompact != INFLATED && fitsTimesTen(intCompact, raise)) return valueOf(intCompact * longTen(raise), newScale);
            BigInteger rb = mulTen(u(), raise);
            return new BigDecimal(rb, INFLATED, newScale, (precision > 0) ? precision + raise : 0);
        }
        int drop = checkScale((long) oldScale - newScale);
        return divideAndRound(u(), BigInteger.ONE, drop, newScale, roundingMode, newScale);
    }

    private static long longTen(int n) {
        long t = 1;
        for (int i = 0; i < n; i++) t *= 10;
        return t;
    }

    public BigDecimal setScale(int newScale) {
        return setScale(newScale, ROUND_UNNECESSARY);
    }

    public BigDecimal movePointLeft(int n) {
        if (n == 0 && scale >= 0) return this;
        int newScale = checkScale((long) scale + n);
        BigDecimal num = new BigDecimal(intVal, intCompact, newScale, 0);
        return num.scale < 0 ? num.setScale(0, ROUND_UNNECESSARY) : num;
    }

    public BigDecimal movePointRight(int n) {
        if (n == 0 && scale >= 0) return this;
        int newScale = checkScale((long) scale - n);
        BigDecimal num = new BigDecimal(intVal, intCompact, newScale, 0);
        return num.scale < 0 ? num.setScale(0, ROUND_UNNECESSARY) : num;
    }

    public BigDecimal scaleByPowerOfTen(int n) {
        return new BigDecimal(intVal, intCompact, checkScale((long) scale - n), precision);
    }

    public BigDecimal stripTrailingZeros() {
        if (signum() == 0) return BigDecimal.ZERO;
        return stripZeros(u(), scale, Long.MIN_VALUE);
    }

    // ================================================================ comparison, hashing

    public int compareTo(BigDecimal val) {
        if (val == null) throw npeField("scale", "val");
        int xsign = this.signum();
        int ysign = val.signum();
        if (xsign != ysign) return (xsign > ysign) ? 1 : -1;
        if (xsign == 0) return 0;
        int cmp = compareMagnitude(val);
        return (xsign > 0) ? cmp : -cmp;
    }

    private int compareMagnitude(BigDecimal val) {
        if (val == null) throw npeField("intCompact", "val");
        if (signum() == 0) return val.signum() == 0 ? 0 : -1;
        if (val.signum() == 0) return 1;
        long xae = (long) this.precision() - this.scale;
        long yae = (long) val.precision() - val.scale;
        if (xae < yae) return -1;
        if (xae > yae) return 1;
        long sdiff = (long) this.scale - val.scale;
        BigInteger x = u().abs();
        BigInteger y = val.u().abs();
        // equal adjusted exponents: |sdiff| = |precision difference| is small
        if (sdiff < 0) return mulTen(x, (int) -sdiff).compareMagnitude(y);
        return x.compareMagnitude(mulTen(y, (int) sdiff));
    }

    public boolean equals(Object x) {
        if (!(x instanceof BigDecimal)) return false;
        BigDecimal xDec = (BigDecimal) x;
        if (x == this) return true;
        if (scale != xDec.scale) return false;
        return u().equals(xDec.u());
    }

    public BigDecimal min(BigDecimal val) {
        return compareTo(val) <= 0 ? this : val;
    }

    public BigDecimal max(BigDecimal val) {
        return compareTo(val) >= 0 ? this : val;
    }

    public int hashCode() {
        return 31 * u().hashCode() + scale;
    }

    // ================================================================ strings

    public String toString() {
        String sc = stringCache;
        if (sc == null) stringCache = sc = layoutChars(true);
        return sc;
    }

    public String toEngineeringString() {
        return layoutChars(false);
    }

    private static final int STRING_BOUND = 1000000;

    private static void zeros(StringBuilder b, long n) {
        if (n > STRING_BOUND) throw ModelStuck.unsupported("BigDecimal: string beyond the model bound");
        for (long i = 0; i < n; i++) b.append('0');
    }

    private String layoutChars(boolean sci) {
        BigInteger v = u();
        if (scale == 0) return v.toString();
        String coeff = v.abs().toString();
        int coeffLen = coeff.length();
        StringBuilder buf = new StringBuilder();
        if (signum() < 0) buf.append('-');
        long adjusted = -(long) scale + (coeffLen - 1);
        if ((scale >= 0) && (adjusted >= -6)) {
            int pad = scale - coeffLen;
            if (pad >= 0) {
                buf.append('0');
                buf.append('.');
                zeros(buf, pad);
                buf.append(coeff);
            } else {
                buf.append(coeff.substring(0, -pad));
                buf.append('.');
                buf.append(coeff.substring(-pad, coeffLen));
            }
        } else {
            if (sci) {
                buf.append(coeff.charAt(0));
                if (coeffLen > 1) {
                    buf.append('.');
                    buf.append(coeff.substring(1, coeffLen));
                }
            } else {
                int sig = (int) (adjusted % 3);
                if (sig < 0) sig += 3;
                adjusted -= sig;
                sig++;
                if (signum() == 0) {
                    switch (sig) {
                        case 1: buf.append('0'); break;
                        case 2: buf.append("0.00"); adjusted += 3; break;
                        default: buf.append("0.0"); adjusted += 3; break;
                    }
                } else if (sig >= coeffLen) {
                    buf.append(coeff);
                    zeros(buf, sig - coeffLen);
                } else {
                    buf.append(coeff.substring(0, sig));
                    buf.append('.');
                    buf.append(coeff.substring(sig, coeffLen));
                }
            }
            if (adjusted != 0) {
                buf.append('E');
                if (adjusted > 0) buf.append('+');
                buf.append(adjusted);
            }
        }
        return buf.toString();
    }

    public String toPlainString() {
        BigInteger v = u();
        if (scale == 0) return v.toString();
        if (this.scale < 0) {
            if (signum() == 0) return "0";
            int trailingZeros = checkScaleNonZero(-(long) scale);
            String str = v.toString();
            if (str.length() + trailingZeros < 0) throw new OutOfMemoryError("too large to fit in a String");
            StringBuilder buf = new StringBuilder();
            buf.append(str);
            zeros(buf, trailingZeros);
            return buf.toString();
        }
        String str = v.abs().toString();
        int insertionPoint = str.length() - scale;
        if (insertionPoint == 0) return (signum() < 0 ? "-0." : "0.") + str;
        StringBuilder buf = new StringBuilder();
        if (insertionPoint > 0) {
            if (signum() < 0) buf.append('-');
            buf.append(str.substring(0, insertionPoint)).append('.').append(str.substring(insertionPoint));
        } else {
            if ((signum() < 0 ? 3 : 2) + scale < 0) throw new OutOfMemoryError("too large to fit in a String");
            buf.append(signum() < 0 ? "-0." : "0.");
            zeros(buf, -(long) insertionPoint);
            buf.append(str);
        }
        return buf.toString();
    }

    // ================================================================ conversions

    public BigInteger toBigInteger() {
        return this.setScale(0, ROUND_DOWN).inflated();
    }

    public BigInteger toBigIntegerExact() {
        return this.setScale(0, ROUND_UNNECESSARY).inflated();
    }

    public long longValue() {
        if (intCompact != INFLATED && scale == 0) return intCompact;
        if (this.signum() == 0 || fractionOnly() || scale <= -64) return 0;
        return toBigInteger().longValue();
    }

    private boolean fractionOnly() {
        return this.precision() <= this.scale;
    }

    public long longValueExact() {
        if (intCompact != INFLATED && scale == 0) return intCompact;
        if (this.signum() == 0) return 0;
        if (fractionOnly()) throw new ArithmeticException("Rounding necessary");
        if (precision() - 19 > scale) throw new ArithmeticException("Overflow");
        BigDecimal num = this.setScale(0, ROUND_UNNECESSARY);
        if (num.precision() >= 19) {
            BigInteger iv = num.u();
            if (iv.compareTo(BigInteger.valueOf(Long.MIN_VALUE)) < 0 || iv.compareTo(BigInteger.valueOf(Long.MAX_VALUE)) > 0)
                throw new ArithmeticException("Overflow");
        }
        return num.u().longValue();
    }

    public int intValue() {
        return (intCompact != INFLATED && scale == 0) ? (int) intCompact : (int) longValue();
    }

    public short shortValue() {
        return (short) intValue();
    }

    public byte byteValue() {
        return (byte) intValue();
    }

    public int intValueExact() {
        long num = this.longValueExact();
        if ((int) num != num) throw new ArithmeticException("Overflow");
        return (int) num;
    }

    public short shortValueExact() {
        long num = this.longValueExact();
        if ((short) num != num) throw new ArithmeticException("Overflow");
        return (short) num;
    }

    public byte byteValueExact() {
        long num = this.longValueExact();
        if ((byte) num != num) throw new ArithmeticException("Overflow");
        return (byte) num;
    }

    /**
     * The binary floating-point value nearest to this value (ties to even), with p significand
     * bits, minimum normal exponent emin and maximum exponent emax: JDK 21's doubleValue and
     * floatValue are correctly rounded. Returns the IEEE bits of the magnitude.
     */
    private long nearestBits(int p, int emin, int emax) {
        BigInteger w = u().abs();
        // decimal magnitude bounds: 10^(prec-1-scale) <= |v| < 10^(prec-scale)
        long e10 = (long) precision() - scale;
        long infinity = (long) (2 * emax + 1) << (p - 1);
        if (e10 - 1 > 310) return infinity;
        if (e10 < -330) return 0;
        BigInteger num;
        BigInteger den;
        if (scale <= 0) {
            num = mulTen(w, -scale);
            den = BigInteger.ONE;
        } else {
            num = w;
            den = tenPow(scale);
        }
        // binary exponent: 2^e <= num/den < 2^(e+1)
        int e = num.bitLength() - den.bitLength();
        if (e >= 0 ? num.compareTo(den.shiftLeft(e)) < 0 : num.shiftLeft(-e).compareTo(den) < 0) e--;
        if (e > emax) return infinity;
        int shift = e >= emin ? (p - 1) - e : (p - 1) - emin;
        BigInteger n2 = shift >= 0 ? num.shiftLeft(shift) : num;
        BigInteger d2 = shift >= 0 ? den : den.shiftLeft(-shift);
        BigInteger m = divRound(n2, d2, ROUND_HALF_EVEN, null);
        long mant = m.longValue();
        int bias = -emin + 1;
        if (e < emin) return mant; // subnormal (2^(p-1) here is the smallest normal)
        if (mant == (1L << p)) {
            mant >>= 1;
            e++;
            if (e > emax) return infinity;
        }
        return ((long) (e + bias) << (p - 1)) | (mant - (1L << (p - 1)));
    }

    public double doubleValue() {
        if (signum() == 0) return 0.0;
        double v = Double.longBitsToDouble(nearestBits(53, -1022, 1023));
        return signum() < 0 ? -v : v;
    }

    public float floatValue() {
        if (signum() == 0) return 0.0f;
        float v = Float.intBitsToFloat((int) nearestBits(24, -126, 127));
        return signum() < 0 ? -v : v;
    }

    public BigDecimal ulp() {
        return valueOf(1, this.scale(), 1);
    }
}

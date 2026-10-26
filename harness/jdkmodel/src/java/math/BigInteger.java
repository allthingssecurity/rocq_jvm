/*
 * rocq-jvm model of java.math.BigInteger (clean-room, Apache-2.0).
 * Representation as in JDK 21: signum and a big-endian magnitude without leading zero words, so
 * hashCode, toByteArray, intValue/longValue and the bit operations see the same words. The
 * arithmetic is done by the natives of java.math.ModelBig (exact integer arithmetic in Rocq).
 * Object identity follows JDK 21 where the JDK returns an operand or a cached constant
 * (valueOf caches -16..16; ZERO for zero results of add/subtract/multiply/divide/remainder/mod;
 * this for x+0, x-0, x<<0, ...); every other result is a new object.
 * Exceptions and messages are JDK 21's, including HotSpot's helpful NullPointerException messages
 * of the JDK's own implicit null checks (thrown explicitly here).
 * STUCK (no claim): random construction (new BigInteger(numBits, rnd), probablePrime); results
 * beyond the model bound (shifts/pow/bit operations reaching more than 10^7 bits);
 * isProbablePrime of a composite with certainty below 99 (HotSpot's answer is random) and
 * primality questions above 81 bits.
 * Note: isProbablePrime(c >= 99) of a composite is claimed false; HotSpot answers true with
 * probability at most 2^-100 (50 Miller-Rabin rounds with random bases).
 */
package java.math;

import java.util.Random;

public class BigInteger extends Number implements Comparable<BigInteger> {
    private static final long serialVersionUID = -8287574255936472291L;

    final int signum;
    final int[] mag;

    static final int MAX_BITS = 10000000;

    private static final BigInteger[] POS = new BigInteger[17];
    private static final BigInteger[] NEG = new BigInteger[17];

    static {
        for (int i = 1; i <= 16; i++) {
            POS[i] = new BigInteger(new int[] {i}, 1);
            NEG[i] = new BigInteger(new int[] {i}, -1);
        }
    }

    public static final BigInteger ZERO = new BigInteger(new int[0], 0);
    public static final BigInteger ONE = valueOf(1);
    public static final BigInteger TWO = valueOf(2);
    static final BigInteger NEGATIVE_ONE = valueOf(-1);
    public static final BigInteger TEN = valueOf(10);

    // ---------------------------------------------------------------- representation helpers

    /** trusted: magnitude normalized (no leading zero word), signum 0 iff the magnitude is empty */
    BigInteger(int[] magnitude, int signum) {
        this.mag = magnitude;
        this.signum = magnitude.length == 0 ? 0 : signum;
    }

    /** the ModelBig encoding */
    int[] enc() {
        int[] e = new int[mag.length + 1];
        e[0] = signum;
        System.arraycopy(mag, 0, e, 1, mag.length);
        return e;
    }

    private static int[] tail(int[] e) {
        int[] m = new int[e.length - 1];
        System.arraycopy(e, 1, m, 0, m.length);
        return m;
    }

    /** a new object for an encoded result */
    static BigInteger make(int[] e) {
        return new BigInteger(tail(e), e[0]);
    }

    /** ZERO for a zero result, else a new object */
    static BigInteger makeZ(int[] e) {
        return e[0] == 0 ? ZERO : make(e);
    }

    /** valueOf semantics: the cached constants for -16..16 */
    static BigInteger makeV(int[] e) {
        if (e.length == 1) return ZERO;
        if (e.length == 2 && e[1] > 0 && e[1] <= 16) return e[0] > 0 ? POS[e[1]] : NEG[e[1]];
        return make(e);
    }

    static int[] encLong(long v) {
        if (v == 0) return new int[] {0};
        int s = v < 0 ? -1 : 1;
        long u = v < 0 ? -v : v; // Long.MIN_VALUE stays 2^63 read unsigned
        int hi = (int) (u >>> 32);
        int lo = (int) u;
        if (hi == 0) return new int[] {s, lo};
        return new int[] {s, hi, lo};
    }

    static int[] op(int op, BigInteger a, BigInteger b) {
        return ModelBig.op2(op, a.enc(), b.enc());
    }

    static NullPointerException npeField(String field, String var) {
        return new NullPointerException("Cannot read field \"" + field + "\" because \"" + var + "\" is null");
    }

    static NullPointerException npeInvoke(String method, String var) {
        return new NullPointerException("Cannot invoke \"" + method + "\" because \"" + var + "\" is null");
    }

    static NullPointerException npeArray(String var) {
        return new NullPointerException("Cannot read the array length because \"" + var + "\" is null");
    }

    private static void checkFromIndexSize(int from, int size, int length) {
        if ((length | from | size) < 0 || size > length - from)
            throw new IndexOutOfBoundsException("Range [" + from + ", " + from + " + " + size
                + ") out of bounds for length " + length);
    }

    // ---------------------------------------------------------------- constructors

    public BigInteger(byte[] val, int off, int len) {
        int[] e = fromBytes(val, off, len);
        this.signum = e[0];
        this.mag = tail(e);
    }

    private static int[] fromBytes(byte[] val, int off, int len) {
        if (val == null) throw npeArray("val");
        if (val.length == 0) throw new NumberFormatException("Zero length BigInteger");
        checkFromIndexSize(off, len, val.length);
        if (len == 0) return new int[] {0};
        int[] e = ModelBig.fromDigits(unsignedBytes(val, off, len), 256);
        if (val[off] < 0) {
            // two's complement: value - 2^(8 len)
            int[] p = ModelBig.op2(12, new int[] {1, 1}, encLong(8L * len));
            e = ModelBig.op2(1, e, p);
        }
        return e;
    }

    private static int[] unsignedBytes(byte[] val, int off, int len) {
        int[] ds = new int[len];
        for (int i = 0; i < len; i++) ds[i] = val[off + i] & 0xff;
        return ds;
    }

    private static int lenOf(byte[] a, String var) {
        if (a == null) throw npeArray(var);
        return a.length;
    }

    public BigInteger(byte[] val) {
        this(val, 0, lenOf(val, "val"));
    }

    public BigInteger(int signum, byte[] magnitude, int off, int len) {
        int[] e = fromSignMag(signum, magnitude, off, len);
        this.signum = e[0];
        this.mag = tail(e);
    }

    private static int[] fromSignMag(int signum, byte[] magnitude, int off, int len) {
        if (signum < -1 || signum > 1) throw new NumberFormatException("Invalid signum value");
        if (magnitude == null) throw npeArray("magnitude");
        checkFromIndexSize(off, len, magnitude.length);
        int[] e = ModelBig.fromDigits(unsignedBytes(magnitude, off, len), 256);
        if (e[0] != 0) {
            if (signum == 0) throw new NumberFormatException("signum-magnitude mismatch");
            e[0] = signum;
        }
        return e;
    }

    public BigInteger(int signum, byte[] magnitude) {
        this(signum, magnitude, 0, lenOf(magnitude, "magnitude"));
    }

    private static final int[] DIGITS_PER_INT = {0, 0, 30, 19, 15, 13, 11, 11, 10, 9, 9, 8, 8, 8, 8, 7, 7, 7, 7,
        7, 7, 7, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 5};

    public BigInteger(String val, int radix) {
        int[] e = parse(val, radix);
        this.signum = e[0];
        this.mag = tail(e);
    }

    private static int[] parse(String val, int radix) {
        if (val == null) throw npeInvoke("String.length()", "val");
        int len = val.length();
        if (radix < Character.MIN_RADIX || radix > Character.MAX_RADIX)
            throw new NumberFormatException("Radix out of range");
        if (len == 0) throw new NumberFormatException("Zero length BigInteger");
        int sign = 1;
        int cursor = 0;
        int minus = val.lastIndexOf('-');
        int plus = val.lastIndexOf('+');
        if (minus >= 0) {
            if (minus != 0 || plus >= 0) throw new NumberFormatException("Illegal embedded sign character");
            sign = -1;
            cursor = 1;
        } else if (plus >= 0) {
            if (plus != 0) throw new NumberFormatException("Illegal embedded sign character");
            cursor = 1;
        }
        if (cursor == len) throw new NumberFormatException("Zero length BigInteger");
        while (cursor < len && digit(val.charAt(cursor), radix) == 0) cursor++;
        if (cursor == len) return new int[] {0};
        int n = len - cursor;
        int[] ds = new int[n];
        for (int i = 0; i < n; i++) {
            int d = digit(val.charAt(cursor + i), radix);
            if (d < 0) {
                // the JDK parses groups of DIGITS_PER_INT[radix] digits with Integer.parseInt (the
                // first group shorter) and reports the group holding the first bad character
                int per = DIGITS_PER_INT[radix];
                int first = n % per;
                if (first == 0) first = per;
                int start;
                int end;
                if (i < first) {
                    start = cursor;
                    end = cursor + first;
                } else {
                    start = cursor + first + ((i - first) / per) * per;
                    end = start + per;
                }
                throw new NumberFormatException("For input string: \"" + val.substring(start, end) + "\""
                    + (radix == 10 ? "" : " under radix " + radix));
            }
            ds[i] = d;
        }
        int[] e = ModelBig.fromDigits(ds, radix);
        e[0] = sign;
        return e;
    }

    /** Character.digit(c, radix), from the decimal digit values of Character.digit(c, 10) and the
     *  ASCII and fullwidth Latin letters (the Javadoc's definition) */
    static int digit(char c, int radix) {
        int v = Character.digit(c, 10);
        if (radix == 10 || v >= 0) return v < radix ? v : -1;
        if (c >= 'a' && c <= 'z') v = c - 'a' + 10;
        else if (c >= 'A' && c <= 'Z') v = c - 'A' + 10;
        else if (c >= '\uff41' && c <= '\uff5a') v = c - '\uff41' + 10;
        else if (c >= '\uff21' && c <= '\uff3a') v = c - '\uff21' + 10;
        else return -1;
        return v < radix ? v : -1;
    }

    public BigInteger(String val) {
        this(val, 10);
    }

    public BigInteger(int numBits, Random rnd) {
        if (numBits < 0) throw new IllegalArgumentException("numBits must be non-negative");
        if (numBits > 0) {
            if (rnd == null) throw npeInvoke("java.util.Random.nextBytes(byte[])", "rnd");
            throw ModelStuck.unsupported("BigInteger(int, Random): random bits");
        }
        this.signum = 0;
        this.mag = new int[0];
    }

    public BigInteger(int bitLength, int certainty, Random rnd) {
        if (bitLength < 2) throw new ArithmeticException("bitLength < 2");
        if (rnd == null) {
            if (bitLength < 95) throw npeInvoke("java.util.Random.nextInt()", "rnd");
            throw npeInvoke("java.util.Random.nextBytes(byte[])", "rnd");
        }
        throw ModelStuck.unsupported("BigInteger(int, int, Random): random prime");
    }

    public static BigInteger probablePrime(int bitLength, Random rnd) {
        if (bitLength < 2) throw new ArithmeticException("bitLength < 2");
        if (rnd == null) {
            if (bitLength < 95) throw npeInvoke("java.util.Random.nextInt()", "rnd");
            throw npeInvoke("java.util.Random.nextBytes(byte[])", "rnd");
        }
        throw ModelStuck.unsupported("BigInteger.probablePrime: random prime");
    }

    public static BigInteger valueOf(long val) {
        if (val == 0) return ZERO;
        if (val > 0 && val <= 16) return POS[(int) val];
        if (val < 0 && val >= -16) return NEG[(int) -val];
        return make(encLong(val));
    }

    // ---------------------------------------------------------------- arithmetic

    public BigInteger add(BigInteger val) {
        if (val == null) throw npeField("signum", "val");
        if (val.signum == 0) return this;
        if (signum == 0) return val;
        return makeZ(op(0, this, val));
    }

    public BigInteger subtract(BigInteger val) {
        if (val == null) throw npeField("signum", "val");
        if (val.signum == 0) return this;
        if (signum == 0) return val.negate();
        return makeZ(op(1, this, val));
    }

    public BigInteger multiply(BigInteger val) {
        if (val == null) throw npeField("signum", "val");
        if (val.signum == 0 || signum == 0) return ZERO;
        return make(op(2, this, val));
    }

    public BigInteger parallelMultiply(BigInteger val) {
        return multiply(val);
    }

    private void checkDivisor(BigInteger val) {
        if (val == null) throw npeField("mag", "val");
        if (val.signum == 0) throw new ArithmeticException("BigInteger divide by zero");
    }

    public BigInteger divide(BigInteger val) {
        checkDivisor(val);
        return makeZ(op(3, this, val));
    }

    public BigInteger[] divideAndRemainder(BigInteger val) {
        checkDivisor(val);
        BigInteger[] r = new BigInteger[2];
        r[0] = makeZ(op(3, this, val));
        r[1] = makeZ(op(4, this, val));
        return r;
    }

    public BigInteger remainder(BigInteger val) {
        checkDivisor(val);
        return makeZ(op(4, this, val));
    }

    public BigInteger pow(int exponent) {
        if (exponent < 0) throw new ArithmeticException("Negative exponent");
        if (signum == 0) return exponent == 0 ? ONE : this;
        int tz = getLowestSetBit();
        long shiftBits = (long) tz * exponent;
        if (shiftBits > Integer.MAX_VALUE) throw new ArithmeticException("BigInteger would overflow supported range");
        boolean neg = signum < 0 && (exponent & 1) == 1;
        int[] odd = ModelBig.op2(13, abs().enc(), encLong(tz));
        int oddBits = bitLengthOfMag(tail(odd));
        if (oddBits == 1) {
            if (tz == 0) return neg ? NEGATIVE_ONE : ONE;
            return (neg ? NEGATIVE_ONE : ONE).shiftLeft((int) shiftBits);
        }
        long scaleFactor = (long) oddBits * exponent;
        if (oddBits <= 32 && scaleFactor <= 62) {
            int[] p = powEnc(odd, exponent);
            if (neg) p = ModelBig.op1(0, p);
            if (tz > 0) {
                if (shiftBits + scaleFactor <= 62) return makeV(ModelBig.op2(12, p, encLong(shiftBits)));
                return makeV(p).shiftLeft((int) shiftBits);
            }
            return makeV(p);
        }
        if ((long) bitLength() * exponent / 32 > (1 << 26))
            throw new ArithmeticException("BigInteger would overflow supported range");
        if (exponent == 0) return ONE;
        if ((long) bitLength() * exponent > MAX_BITS) throw ModelStuck.unsupported("BigInteger.pow: beyond the model bound");
        return make(powEnc(enc(), exponent));
    }

    /** a^n for an encoded a (n >= 0) */
    private static int[] powEnc(int[] a, int n) {
        if (n <= 100000) return ModelBig.op2(11, a, encLong(n));
        int[] r = {1, 1};
        int[] b = a;
        while (n != 0) {
            if ((n & 1) != 0) r = ModelBig.op2(2, r, b);
            n >>>= 1;
            if (n != 0) b = ModelBig.op2(2, b, b);
        }
        return r;
    }

    public BigInteger sqrt() {
        if (signum < 0) throw new ArithmeticException("Negative BigInteger");
        return makeZ(ModelBig.op1(2, enc()));
    }

    public BigInteger[] sqrtAndRemainder() {
        BigInteger s = sqrt();
        BigInteger r;
        if (s.signum == 0) {
            r = this;
        } else {
            r = makeZ(ModelBig.op2(1, enc(), ModelBig.op2(2, s.enc(), s.enc())));
        }
        return new BigInteger[] {s, r};
    }

    public BigInteger gcd(BigInteger val) {
        if (val == null) throw npeField("signum", "val");
        if (val.signum == 0) return this.abs();
        if (signum == 0) return val.abs();
        return make(op(6, this, val));
    }

    public BigInteger abs() {
        return signum >= 0 ? this : negate();
    }

    public BigInteger negate() {
        return new BigInteger(mag, -signum);
    }

    public int signum() {
        return signum;
    }

    public BigInteger mod(BigInteger m) {
        if (m == null) throw npeField("signum", "m");
        if (m.signum <= 0) throw new ArithmeticException("BigInteger: modulus not positive");
        return makeZ(op(5, this, m));
    }

    private static boolean isOne(BigInteger x) {
        return x.signum == 1 && x.mag.length == 1 && x.mag[0] == 1;
    }

    public BigInteger modPow(BigInteger exponent, BigInteger m) {
        if (m == null) throw npeField("signum", "m");
        if (m.signum <= 0) throw new ArithmeticException("BigInteger: modulus not positive");
        if (exponent == null) throw npeField("signum", "exponent");
        if (exponent.signum == 0) return isOne(m) ? ZERO : ONE;
        if (isOne(this)) return isOne(m) ? ZERO : ONE;
        if (signum == 0 && exponent.signum >= 0) return ZERO;
        if (signum < 0 && mag.length == 1 && mag[0] == 1 && (exponent.mag[exponent.mag.length - 1] & 1) == 0)
            return isOne(m) ? ZERO : ONE;
        boolean invert = exponent.signum < 0;
        BigInteger e = invert ? exponent.negate() : exponent;
        BigInteger base = (signum < 0 || compareTo(m) >= 0) ? mod(m) : this;
        BigInteger result;
        if ((m.mag[m.mag.length - 1] & 1) != 0) {
            // odd modulus (JDK: Montgomery; exponent one returns the base, zero base ZERO, else new)
            if (isOne(e)) result = base;
            else if (base.signum == 0) result = ZERO;
            else result = make(ModelBig.modPow(base.enc(), e.enc(), m.enc()));
        } else {
            // even modulus (JDK: Chinese remaindering, finally reduced by mod)
            result = makeZ(ModelBig.modPow(base.enc(), e.enc(), m.enc()));
        }
        return invert ? result.modInverse(m) : result;
    }

    public BigInteger modInverse(BigInteger m) {
        if (m == null) throw npeField("signum", "m");
        if (m.signum != 1) throw new ArithmeticException("BigInteger: modulus not positive");
        if (isOne(m)) return ZERO;
        BigInteger modVal = this;
        if (signum < 0 || compareMagnitude(m) >= 0) modVal = mod(m);
        if (isOne(modVal)) return ONE;
        int[] r = ModelBig.op2(15, modVal.enc(), m.enc());
        if (r.length == 0) throw new ArithmeticException("BigInteger not invertible.");
        return make(r);
    }

    // ---------------------------------------------------------------- shifts

    public BigInteger shiftLeft(int n) {
        if (signum == 0) return ZERO;
        if (n > 0) return shiftLeftNew(n);
        if (n == 0) return this;
        return shiftRightImpl(-n);
    }

    /** n read as unsigned */
    private BigInteger shiftLeftNew(int n) {
        long bits = n & 0xffffffffL;
        if (bits > MAX_BITS) throw ModelStuck.unsupported("BigInteger shift beyond the model bound");
        return make(ModelBig.op2(12, enc(), encLong(bits)));
    }

    /** n read as unsigned */
    private BigInteger shiftRightImpl(int n) {
        if ((n >>> 5) >= mag.length) return signum >= 0 ? ZERO : NEGATIVE_ONE;
        return make(ModelBig.op2(13, enc(), encLong(n)));
    }

    public BigInteger shiftRight(int n) {
        if (signum == 0) return ZERO;
        if (n > 0) return shiftRightImpl(n);
        if (n == 0) return this;
        return shiftLeftNew(-n);
    }

    // ---------------------------------------------------------------- bitwise

    public BigInteger and(BigInteger val) {
        if (val == null) throw npeInvoke("java.math.BigInteger.intLength()", "val");
        return make(op(7, this, val));
    }

    public BigInteger or(BigInteger val) {
        if (val == null) throw npeInvoke("java.math.BigInteger.intLength()", "val");
        return make(op(8, this, val));
    }

    public BigInteger xor(BigInteger val) {
        if (val == null) throw npeInvoke("java.math.BigInteger.intLength()", "val");
        return make(op(9, this, val));
    }

    public BigInteger not() {
        return make(ModelBig.op1(1, enc()));
    }

    public BigInteger andNot(BigInteger val) {
        if (val == null) throw npeInvoke("java.math.BigInteger.intLength()", "val");
        return make(op(10, this, val));
    }

    /** word n (from the least significant) of the two's complement representation */
    int getInt(int n) {
        if (n < 0) return 0;
        if (n >= mag.length) return signum < 0 ? -1 : 0;
        int w = mag[mag.length - n - 1];
        if (signum >= 0) return w;
        return n <= firstNonzeroInt() ? -w : ~w;
    }

    private int firstNonzeroInt() {
        int i = mag.length - 1;
        while (i >= 0 && mag[i] == 0) i--;
        return mag.length - i - 1;
    }

    public boolean testBit(int n) {
        if (n < 0) throw new ArithmeticException("Negative bit address");
        return (getInt(n >>> 5) & (1 << (n & 31))) != 0;
    }

    private int[] bitEnc(int n) {
        if (n < 0) throw new ArithmeticException("Negative bit address");
        if (n > MAX_BITS) throw ModelStuck.unsupported("BigInteger bit operation beyond the model bound");
        return ModelBig.op2(12, new int[] {1, 1}, encLong(n));
    }

    public BigInteger setBit(int n) {
        return make(ModelBig.op2(8, enc(), bitEnc(n)));
    }

    public BigInteger clearBit(int n) {
        return make(ModelBig.op2(10, enc(), bitEnc(n)));
    }

    public BigInteger flipBit(int n) {
        return make(ModelBig.op2(9, enc(), bitEnc(n)));
    }

    public int getLowestSetBit() {
        if (signum == 0) return -1;
        int i = mag.length - 1;
        while (mag[i] == 0) i--;
        return ((mag.length - 1 - i) << 5) + Integer.numberOfTrailingZeros(mag[i]);
    }

    static int bitLengthOfMag(int[] m) {
        if (m.length == 0) return 0;
        return ((m.length - 1) << 5) + 32 - Integer.numberOfLeadingZeros(m[0]);
    }

    public int bitLength() {
        int n = bitLengthOfMag(mag);
        if (signum < 0) {
            boolean pow2 = Integer.bitCount(mag[0]) == 1;
            for (int i = 1; i < mag.length && pow2; i++) pow2 = mag[i] == 0;
            if (pow2) n--;
        }
        return n;
    }

    public int bitCount() {
        int bc = 0;
        for (int i = 0; i < mag.length; i++) bc += Integer.bitCount(mag[i]);
        if (signum < 0) bc += getLowestSetBit() - 1;
        return bc;
    }

    // ---------------------------------------------------------------- primality

    private static final int[] MR_BASES = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41};

    /** w odd, w > 2, bitLength <= 81: deterministic Miller-Rabin (bases 2..41) */
    private static boolean isPrimeOdd(BigInteger w) {
        if (w.mag.length == 1 && w.mag[0] > 0 && w.mag[0] <= 41) {
            for (int i = 0; i < MR_BASES.length; i++) if (MR_BASES[i] == w.mag[0]) return true;
            return false;
        }
        int[] we = w.enc();
        int[] wm1 = ModelBig.op2(1, we, new int[] {1, 1});
        BigInteger d = make(wm1);
        int s = d.getLowestSetBit();
        int[] de = ModelBig.op2(13, wm1, encLong(s));
        for (int i = 0; i < MR_BASES.length; i++) {
            int[] x = ModelBig.modPow(new int[] {1, MR_BASES[i]}, de, we);
            if (isOneEnc(x) || ModelBig.op2(14, x, wm1)[0] == 0) continue;
            boolean found = false;
            for (int r = 1; r < s && !found; r++) {
                x = ModelBig.modPow(x, new int[] {1, 2}, we);
                if (ModelBig.op2(14, x, wm1)[0] == 0) found = true;
            }
            if (!found) return false;
        }
        return true;
    }

    private static boolean isOneEnc(int[] x) {
        return x.length == 2 && x[0] == 1 && x[1] == 1;
    }

    public boolean isProbablePrime(int certainty) {
        if (certainty <= 0) return true;
        BigInteger w = abs();
        if (w.signum == 1 && w.mag.length == 1 && w.mag[0] == 2) return true;
        if (!w.testBit(0) || isOne(w)) return false;
        if (w.bitLength() > 81) throw ModelStuck.unsupported("BigInteger.isProbablePrime above 81 bits");
        if (isPrimeOdd(w)) return true;
        if (certainty < 99) throw ModelStuck.unsupported("BigInteger.isProbablePrime: composite, random answer");
        return false;
    }

    public BigInteger nextProbablePrime() {
        if (signum < 0) throw new ArithmeticException("start < 0: " + this);
        if (signum == 0 || isOne(this)) return TWO;
        BigInteger r = add(ONE);
        if (!r.testBit(0)) r = r.add(ONE);
        while (true) {
            if (r.bitLength() > 81) throw ModelStuck.unsupported("BigInteger.nextProbablePrime above 81 bits");
            if (isPrimeOdd(r)) return r;
            r = r.add(TWO);
        }
    }

    // ---------------------------------------------------------------- comparison, hashing

    int compareMagnitude(BigInteger val) {
        int[] a = mag;
        int[] b = val.mag;
        if (a.length != b.length) return a.length < b.length ? -1 : 1;
        for (int i = 0; i < a.length; i++) {
            if (a[i] != b[i]) return (a[i] ^ Integer.MIN_VALUE) < (b[i] ^ Integer.MIN_VALUE) ? -1 : 1;
        }
        return 0;
    }

    public int compareTo(BigInteger val) {
        if (val == null) throw npeField("signum", "val");
        if (signum != val.signum) return signum > val.signum ? 1 : -1;
        if (signum == 0) return 0;
        int c = compareMagnitude(val);
        return signum > 0 ? c : -c;
    }

    public boolean equals(Object x) {
        if (x == this) return true;
        if (!(x instanceof BigInteger)) return false;
        BigInteger b = (BigInteger) x;
        if (b.signum != signum) return false;
        if (b.mag.length != mag.length) return false;
        for (int i = 0; i < mag.length; i++) if (b.mag[i] != mag[i]) return false;
        return true;
    }

    public BigInteger min(BigInteger val) {
        return compareTo(val) < 0 ? this : val;
    }

    public BigInteger max(BigInteger val) {
        return compareTo(val) > 0 ? this : val;
    }

    public int hashCode() {
        int h = 0;
        for (int i = 0; i < mag.length; i++) h = (int) (31 * h + (mag[i] & 0xffffffffL));
        return h * signum;
    }

    // ---------------------------------------------------------------- conversions

    public String toString(int radix) {
        if (signum == 0) return "0";
        if (radix < Character.MIN_RADIX || radix > Character.MAX_RADIX) radix = 10;
        return ModelBig.toStr(enc(), radix);
    }

    public String toString() {
        return toString(10);
    }

    public byte[] toByteArray() {
        int len = bitLength() / 8 + 1;
        byte[] b = new byte[len];
        int word = 0;
        int k = 0;
        for (int i = len - 1, j = 0; i >= 0; i--, j++) {
            if ((j & 3) == 0) word = getInt(k++);
            else word >>>= 8;
            b[i] = (byte) word;
        }
        return b;
    }

    public int intValue() {
        return getInt(0);
    }

    public long longValue() {
        return ((long) getInt(1) << 32) | (getInt(0) & 0xffffffffL);
    }

    public short shortValue() {
        return (short) intValue();
    }

    public byte byteValue() {
        return (byte) intValue();
    }

    public float floatValue() {
        return ModelBig.toFloat(enc());
    }

    public double doubleValue() {
        return ModelBig.toDouble(enc());
    }

    public long longValueExact() {
        if (mag.length <= 2 && bitLength() <= 63) return longValue();
        throw new ArithmeticException("BigInteger out of long range");
    }

    public int intValueExact() {
        if (mag.length <= 1 && bitLength() <= 31) return intValue();
        throw new ArithmeticException("BigInteger out of int range");
    }

    public short shortValueExact() {
        if (mag.length <= 1 && bitLength() <= 31) {
            int v = intValue();
            if (v >= Short.MIN_VALUE && v <= Short.MAX_VALUE) return (short) v;
        }
        throw new ArithmeticException("BigInteger out of short range");
    }

    public byte byteValueExact() {
        if (mag.length <= 1 && bitLength() <= 31) {
            int v = intValue();
            if (v >= Byte.MIN_VALUE && v <= Byte.MAX_VALUE) return (byte) v;
        }
        throw new ArithmeticException("BigInteger out of byte range");
    }
}

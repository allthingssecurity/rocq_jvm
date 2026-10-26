/*
 * rocq-jvm helper (not a JDK class): the integer arithmetic of the java.math model classes,
 * implemented by the Rocq machine (theories/Jdk/Jdk.v, Definition modelbig) on integers encoded
 * as int[] { signum (-1, 0, 1), magnitude words big-endian (unsigned), no leading zero words }.
 * Preconditions that the natives do not cover (division by zero, negative moduli, ...) make the
 * machine STUCK, so the model classes check them first and throw the JDK's exceptions.
 *   op2: 0 add, 1 subtract, 2 multiply, 3 truncated quotient, 4 truncated remainder, 5 floor mod
 *        (b > 0), 6 gcd, 7 and, 8 or, 9 xor, 10 andNot (two's complement), 11 a^b (0 <= b <= 100000),
 *        12 a << b, 13 a >> b (floor; |b| <= 10^7), 14 compare (-1/0/1), 15 a^-1 mod b (b > 0;
 *        an empty array when a is not invertible)
 *   op1: 0 negate, 1 not, 2 floor sqrt (a >= 0)
 * HotSpot never loads this class.
 */
package java.math;

final class ModelBig {
    private ModelBig() {
    }

    static native int[] op2(int op, int[] a, int[] b);

    static native int[] op1(int op, int[] a);

    static native int[] modPow(int[] a, int[] e, int[] m);

    static native String toStr(int[] a, int radix);

    static native int[] fromDigits(int[] digits, int radix);

    static native double toDouble(int[] a);

    static native float toFloat(int[] a);
}

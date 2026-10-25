// corpus11: Math exact/floor operations and Integer/Long bit operations, against HotSpot.
public class MathOps {
    public static int floorModI(int a, int b) { return Math.floorMod(a, b); }
    public static int floorDivI(int a, int b) { return Math.floorDiv(a, b); }
    public static long floorModJ(long a, long b) { return Math.floorMod(a, b); }
    public static long floorDivJ(long a, long b) { return Math.floorDiv(a, b); }
    public static int floorModJI(long a, int b) { return Math.floorMod(a, b); }
    public static int addExactI(int a, int b) { return Math.addExact(a, b); }
    public static int subExactI(int a, int b) { return Math.subtractExact(a, b); }
    public static int mulExactI(int a, int b) { return Math.multiplyExact(a, b); }
    public static long addExactJ(long a, long b) { return Math.addExact(a, b); }
    public static long mulExactJ(long a, long b) { return Math.multiplyExact(a, b); }
    public static long mulExactJI(long a, int b) { return Math.multiplyExact(a, b); }
    public static int toIntExact(long a) { return Math.toIntExact(a); }
    public static int negIncDecI(int a) {
        int r = 0;
        try { r += Math.negateExact(a); } catch (ArithmeticException e) { r += 1; }
        try { r ^= Math.incrementExact(a); } catch (ArithmeticException e) { r ^= 2; }
        try { r += Math.decrementExact(a); } catch (ArithmeticException e) { r += 3; }
        try { r ^= Math.absExact(a); } catch (ArithmeticException e) { r ^= 4; }
        return r;
    }
    public static long negIncDecJ(long a) {
        long r = 0;
        try { r += Math.negateExact(a); } catch (ArithmeticException e) { r += 1; }
        try { r ^= Math.incrementExact(a); } catch (ArithmeticException e) { r ^= 2; }
        try { r += Math.decrementExact(a); } catch (ArithmeticException e) { r += 3; }
        try { r ^= Math.absExact(a); } catch (ArithmeticException e) { r ^= 4; }
        return r;
    }
    public static int bitsI(int a) {
        return Integer.bitCount(a) * 31 + Integer.numberOfLeadingZeros(a) * 17 + Integer.numberOfTrailingZeros(a) * 13
             + Integer.highestOneBit(a) + 7 * Integer.lowestOneBit(a) + Integer.hashCode(a);
    }
    public static long bitsJ(long a) {
        return Long.bitCount(a) * 31L + Long.numberOfLeadingZeros(a) * 17 + Long.numberOfTrailingZeros(a) * 13
             + Long.highestOneBit(a) + 7 * Long.lowestOneBit(a) + Long.hashCode(a) + Long.signum(a);
    }
    public static int rotate(int a, int b) { return Integer.rotateLeft(a, b) ^ (Integer.rotateRight(a, b) * 3) + Integer.sum(a, b); }
}

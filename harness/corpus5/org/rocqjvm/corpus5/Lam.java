package org.rocqjvm.corpus5;

import java.util.function.*;

/** Phase 9 corpus: lambdas and method references (LambdaMetafactory), boxing and its caches,
 *  multianewarray, failing static initialisers (ExceptionInInitializerError, NoClassDefFoundError),
 *  interface static/default/private methods, enum switch, nested classes. */
public class Lam {
    interface Op { int apply(int a, int b); default int twice(int a, int b) { return 2 * apply(a, b); } static Op plus() { return (a, b) -> a + b; } }
    interface Pred { boolean test(int x); }
    enum Mode { ADD, SUB, MUL }
    static class Bad { static int v = 10 / Lam.zero(); static int get() { return v; } }
    static class Bad2 { static final int[] A = new int[-1]; static int get() { return A.length; } }
    static int zeroField;
    static int zero() { return zeroField; }

    static int nonCapturing(int a, int b) { Op op = (x, y) -> x * y + 1; return op.apply(a, b) + op.twice(b, a); }
    static int capturing(int a, int b) { int k = a ^ 5; Op op = (x, y) -> x - y + k; Pred p = x -> x > k; return op.apply(b, a) + (p.test(b) ? 1 : 0); }
    static boolean sameLambda(int a) { Op[] ops = new Op[2]; for (int i = 0; i < 2; i++) ops[i] = (x, y) -> x; return ops[0] == ops[1]; }
    static int staticIface(int a, int b) { return Op.plus().apply(a, b); }
    static int methodRefs(int a) { IntUnaryOperator f = Lam::sq; IntBinaryOperator g = Math::max; return f.applyAsInt(a & 0xffff) + g.applyAsInt(a, -a); }
    static int sq(int x) { return x * x; }
    static int boxedLambda(int a) { Function<Integer, Integer> f = x -> x + 1; Supplier<Integer> s = () -> a; return f.apply(s.get()); }
    static int boxing(int a, long l) {
        Integer x = a, y = a; Long p = l, q = l; Boolean b = a > 0; Character c = (char) (a & 0xff);
        return (x == y ? 1 : 0) + (x.equals(y) ? 2 : 0) + (p == q ? 4 : 0) + (p.equals(q) ? 8 : 0) + (b == Boolean.TRUE ? 16 : 0)
             + (c == (Character) (char) (a & 0xff) ? 32 : 0) + x.hashCode() + p.hashCode() + b.hashCode() + c.compareTo('a');
    }
    static int unbox(int a) { Integer x = a; int y = x + 1; Long z = (long) y; return (int) (z * 2) + x.compareTo(y); }
    static int multi(int a, int b) { int[][][] m = new int[a & 3][b & 3][2]; int s = 0; for (int[][] r : m) for (int[] c : r) s += c.length + c[1]; return s + m.length; }
    static int multiNeg(int a) { long[][] m = new long[2][a]; return m[1].length; }
    static int badInit(int a) { if (a > 0) return Bad.get(); return -1; }
    static int badTwice(int a) { int r = 0; try { r += Bad.get(); } catch (ExceptionInInitializerError e) { r += 100; } try { r += Bad.get(); } catch (NoClassDefFoundError e) { r += 1000; } return r + a; }
    static int badArray(int a) { try { return Bad2.get(); } catch (Throwable t) { return a; } }
    static int enumSwitch(int i) { Mode m = Mode.values()[(i & 0x7fffffff) % 3]; switch (m) { case ADD: return i + 1; case SUB: return i - 1; default: return i * 2; } }
    static int predicates(int a) { IntPredicate even = x -> (x & 1) == 0; IntPredicate pos = x -> x > 0; return (even.test(a) ? 1 : 0) + (pos.test(a) ? 2 : 0); }
}

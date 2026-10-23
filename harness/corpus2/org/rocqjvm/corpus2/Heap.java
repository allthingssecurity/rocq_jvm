package org.rocqjvm.corpus2;

/** Phase 2/3 differential corpus: objects, fields, arrays of every primitive kind and of
 *  references, exceptions (VM-thrown and athrow, handlers, finally, nested), static and
 *  instance calls, virtual and interface dispatch, constructors, static initialisers,
 *  checkcast/instanceof, synchronized blocks. Only int/long parameters and results.
 *  No String, no JDK calls except no-argument exception constructors and Object.<init>. */
public class Heap {
    static int counter;
    static final int[] TABLE;
    static long seed = 0x5DEECE66DL;
    static { int[] t = new int[16]; for (int i = 0; i < t.length; i++) t[i] = i * i - 7; TABLE = t; counter = 3; }

    interface Shape { int area(); default int twice() { return 2 * area(); } }
    static abstract class Base implements Shape {
        int w, h;
        Base(int w, int h) { this.w = w; this.h = h; }
        abstract int kind();
        int perimeter() { return 2 * (w + h); }
    }
    static class Rect extends Base {
        Rect(int w, int h) { super(w, h); }
        public int area() { return w * h; }
        int kind() { return 1; }
    }
    static class Square extends Rect {
        Square(int s) { super(s, s); }
        int kind() { return 2; }
        int perimeter() { return 4 * w; }
    }
    static class Tri extends Base {
        Tri(int b, int h) { super(b, h); }
        public int area() { return (w * h) / 2; }
        int kind() { return 3; }
    }
    static class MyEx extends RuntimeException { int code; MyEx(int c) { super(); code = c; } }
    static class Node { int val; Node next; Node(int v, Node n) { val = v; next = n; } }
    static class Cell { boolean b; byte by; char ch; short sh; long lg; Object ref; }

    // ---- arrays ----
    static int arrSum(int n) {
        int[] a = new int[n & 63];
        for (int i = 0; i < a.length; i++) a[i] = i * n;
        int s = 0; for (int x : a) s += x; return s;
    }
    static int arrIndex(int n, int i) { int[] a = new int[n & 15]; a[i & 31 % 20] = 5; return a[i % 17]; }
    static int arrNeg(int n) { long[] a = new long[n]; return a.length; }
    static int bytes(int a, int b) {
        byte[] x = new byte[4]; x[0] = (byte) a; x[1] = (byte) (a >> 8); x[2] = (byte) b; x[3] = (byte) (b >>> 24);
        return x[0] + x[1] * 3 + x[2] * 7 + x[3] * 11;
    }
    static int chars(int a) { char[] c = new char[3]; c[0] = (char) a; c[1] = (char) (a >> 16); c[2] = (char) -a; return c[0] + c[1] + c[2]; }
    static int shorts(int a) { short[] s = new short[2]; s[0] = (short) a; s[1] = (short) (a * 3); return s[0] - s[1]; }
    static int bools(int a) { boolean[] z = new boolean[3]; z[0] = a > 0; z[1] = (a & 1) == 0; z[2] = !z[0]; return (z[0] ? 1 : 0) + (z[1] ? 2 : 0) + (z[2] ? 4 : 0); }
    static long longs(long a, int n) { long[] l = new long[(n & 7) + 1]; for (int i = 0; i < l.length; i++) l[i] = a * i - (a >>> i); long s = 0; for (long v : l) s ^= v; return s; }
    static int matrix(int n) {
        int[][] m = new int[3][]; for (int i = 0; i < 3; i++) { m[i] = new int[i + 1]; for (int j = 0; j <= i; j++) m[i][j] = n + i * j; }
        return m[2][2] + m[1][0] + m[0].length;
    }
    static int nullArray(int a) { int[] x = (a > 0) ? new int[1] : null; return x[0]; }
    static int nullLength(int a) { long[] x = (a > 10) ? new long[a & 7] : null; return x.length; }
    static int storeCheck(int a) { Object[] o = (a > 0) ? new Rect[2] : new Object[2]; o[0] = new Tri(1, 2); return o.length; }
    static int refArray(int a, int b) {
        Shape[] s = { new Rect(a & 255, b & 255), new Square(a & 31), new Tri(b & 127, 3) };
        int t = 0; for (Shape x : s) t += x.area() + x.twice(); return t;
    }
    static int tableLookup(int i) { return TABLE[i & 15] + counter; }
    // ---- objects, dispatch ----
    static int dispatch(int a, int b) {
        Base x = (a % 3 == 0) ? new Rect(a & 1023, b & 1023) : (a % 3 == 1) ? new Square(b & 4095) : new Tri(a & 4095, b & 4095);
        return x.area() * 7 + x.kind() * 1000 + x.perimeter() + x.twice();
    }
    static int list(int n) {
        Node h = null; for (int i = 0; i < (n & 31); i++) h = new Node(i * n, h);
        int s = 0; while (h != null) { s += h.val; h = h.next; } return s;
    }
    static long cell(int a, long l) {
        Cell c = new Cell(); c.b = a > 3; c.by = (byte) a; c.ch = (char) a; c.sh = (short) a; c.lg = l; c.ref = c;
        return (c.b ? 1 : 0) + c.by + c.ch + c.sh + c.lg + (c.ref == c ? 100 : 0);
    }
    static int casts(int a) {
        Object o = (a & 1) == 0 ? new Rect(1, 2) : (a & 2) == 0 ? new Square(3) : new Node(a, null);
        int r = 0;
        if (o instanceof Shape) r += 1; if (o instanceof Rect) r += 2; if (o instanceof Square) r += 4; if (o instanceof Node) r += 8;
        Rect q = (Rect) o; return r + q.area();
    }
    static int arrCasts(int a) {
        Object o = (a & 1) == 0 ? new int[3] : (Object) new Rect[2];
        int r = 0; if (o instanceof int[]) r += 1; if (o instanceof Object[]) r += 2; if (o instanceof Shape[]) r += 4; if (o instanceof Cloneable) r += 8;
        return r + ((Object[]) o).length;
    }
    // ---- exceptions ----
    static int catchDiv(int a, int b) { try { return a / b; } catch (ArithmeticException e) { return -1; } }
    static int finallyFlow(int a) {
        int r = 0;
        try { if (a < 0) throw new IllegalStateException(); r = 10 / (a & 3); }
        catch (IllegalStateException e) { r = -5; }
        finally { r += 100; }
        return r;
    }
    static int myEx(int a) {
        try { thrower(a); return 0; } catch (MyEx e) { return e.code; }
    }
    static void thrower(int a) { if (a % 5 == 0) throw new MyEx(a / 5); if (a % 7 == 0) throw new UnsupportedOperationException(); }
    static int nested(int a, int b) {
        int r = 1;
        try { try { r = a / b; } finally { r *= 3; } } catch (RuntimeException e) { r = -r; }
        return r;
    }
    static int npe(int a) { Node n = (a > 0) ? new Node(a, null) : null; return n.val; }
    static int uncaught(int a) { if (a > 1000) throw new IllegalArgumentException(); return a; }
    static int rethrow(int a) { try { return 100 / a; } catch (ArithmeticException e) { throw new IllegalStateException(); } }
    static int classCast(int a) { Object o = (a > 0) ? new Square(2) : (Object) new Node(1, null); return ((Base) o).kind(); }
    static int negSize(int a) { int[][] x = new int[2][]; x[0] = new int[a]; return x[0].length; }
    // ---- static state, recursion, locks ----
    static int fib(int n) { n &= 15; return n < 2 ? n : fib(n - 1) + fib(n - 2); }
    static long next(long s) { return (s * 0x5DEECE66DL + 0xBL) & ((1L << 48) - 1); }
    static long rng(int k) { long s = seed; for (int i = 0; i < (k & 15); i++) s = next(s); seed = s; return s >>> 16; }
    static int sync(int a) { Object lock = new Node(0, null); int r; synchronized (lock) { r = a * 2; } return r; }
    static int syncThrow(int a) { Node lock = new Node(0, null); try { synchronized (lock) { return 10 / a; } } catch (ArithmeticException e) { return -7; } }
    static int counterInc(int a) { counter += a; return counter; }
}

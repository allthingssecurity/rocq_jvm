package org.rocqjvm.corpus9;

/** Corpus 9: messages of the exceptions the machine itself throws (HotSpot 21's texts), observed
 *  both as uncaught exceptions (the harness prints getMessage()) and through getMessage() in a
 *  handler. */
public class Msg {
    static int div(int a, int b) { return a / b + a % (b | 1); }
    static long ldiv(long a, long b) { return a % b; }
    static int index(int i, int n) { int[] a = new int[n & 0xf]; a[i & 0x1f] = 1; return a[(i >> 5) & 0x1f]; }
    static int negIndex(int i) { long[] a = new long[3]; return (int) a[i]; }
    static int newArr(int n) { return new int[n].length; }
    static int newRefArr(int n) { return new String[n].length; }
    static int multi(int a, int b) { return new int[a][b][2].length; }
    static int store(int x) {
        Object[] a = (x & 1) != 0 ? new String[2] : (x & 2) != 0 ? new Integer[1] : new int[2][];
        Object v = (x & 4) != 0 ? "s" : (x & 8) != 0 ? (Object) Integer.valueOf(x) : (x & 16) != 0 ? new long[1] : new String[0];
        a[0] = v;
        return a.length;
    }
    static int monitor(int x) { Object o = new Object(); if ((x & 1) != 0) { synchronized (o) { o.notify(); } } else o.notifyAll(); return 1; }
    static class Bad { static int v = 1 / Msg.zero; }
    static class Sub extends Bad { static int w = 2; }
    static class Sub2 extends Sub { static int u = 3; }
    static int zero;
    static int init(int x) {
        int r = 0;
        if ((x & 1) != 0) { try { r += Bad.v; } catch (ExceptionInInitializerError e) { r += e.getMessage() == null ? 1 : 2; } }
        if ((x & 2) != 0) { try { r += Sub2.u; } catch (Throwable e) { r += 10 * e.getMessage().length(); } }
        if ((x & 4) != 0) { try { r += Sub.w; } catch (NoClassDefFoundError e) { r += 1000 * e.getMessage().length(); } }
        return r + Sub2.u;   // NoClassDefFoundError escapes: its message names the first erroneous class
    }
    static String caught(int x) {
        try {
            switch ((x & 0x7fffffff) % 6) {
                case 0: return "" + div(x, x & 3);
                case 1: return "" + index(x, x >> 8);
                case 2: return "" + newArr(x >> 28);
                case 3: return "" + store(x);
                case 4: return "" + monitor(x);
                default: return "" + ldiv(x, (long) (x & 1));
            }
        } catch (RuntimeException e) { return e.getMessage(); }
    }
}

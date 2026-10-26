package org.rocqjvm.jdkmodel;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

/** Differential tests of HotSpot's helpful NullPointerException messages (JEP 358): the failed
 *  action of invoke/getfield/putfield/array/athrow/monitor instructions and the description of
 *  the null value (locals, parameters, fields, statics, array elements, return values, nesting).
 *  Compiled with -g (local variable names) and, in a second copy, without. */
public final class NpeOps {
    String name;
    NpeOps next;
    int[] arr;
    NpeOps[] kids;
    int[][] grid;
    long lf;
    int cnt;
    static NpeOps sp;
    static Object[] sarr;

    static String sm() { return null; }
    NpeOps getNext() { return next; }
    NpeOps self() { return this; }
    static NpeOps mk() { return new NpeOps(); }
    private String priv() { return name; }

    static int f1(String s) { return s.length(); }
    static int f2(NpeOps p) { return p.name.length(); }
    static int f3(NpeOps p) { return p.next.next.name.length(); }
    static int f4() { return sp.name.length(); }
    static int f5() { return sm().length(); }
    static int f6(int[] a) { return a[0]; }
    static int f7(int[] a) { return a.length; }
    static void f8(int[] a) { a[1] = 3; }
    static Object f9(Object[] a, int i) { return a[i].toString(); }
    static void f10(RuntimeException e) { throw e; }
    static void f11(Object o) { synchronized (o) { o.hashCode(); } }
    static void f12(NpeOps p) { p.name = "x"; }
    static int f13(Map<String, String> m) { return m.get("k").length(); }
    static int f14(List<Integer> l) { return l.get(0); }
    static int f15(Integer i) { return i; }
    static int f16(NpeOps p) { return p.getNext().name.length(); }
    int f17() { return next.name.length(); }
    static int f18(String a, String b) { String c = a; return c.length() + b.length(); }
    static int f19(StringBuilder sb) { return sb.length(); }
    static int f20(Map.Entry<String, String> e) { return e.getKey().length(); }
    static int f21(NpeOps[] ps) { return ps[2].name.length(); }
    static long f22(long[] a) { return a[0]; }
    static String f23(Object o) { return ((String) o).trim(); }
    static int f24() { String s = null; return s.length(); }
    static int f25(boolean b, String x, String y) { return (b ? x : y).length(); }
    static int f26(NpeOps p) { return p.arr[0]; }
    static void f27(Object[] a) { a[0] = "s"; }
    static int f28(char[] c) { return c[0]; }
    static double f29(double[] d) { return d[0]; }
    static int f30(Integer[] a) { return a[0]; }
    static int g1() { return ((String) null).length(); }
    static void g3() { throw null; }
    static int g4(long a, String b, double c, Object d) { return b.length() + d.hashCode(); }
    static int g5(long a, String b, double c, Object d) { return d.hashCode(); }
    static int g6(NpeOps q) { return q.self().next.name.length(); }
    static int g8(NpeOps q) { return q.kids[0].kids[1].name.length(); }
    static int g9(NpeOps q) { return q.grid[1][2]; }
    static int g10(NpeOps q) { return q.next.next.next.next.next.next.name.length(); }
    int g11() { return priv().length(); }
    static int g12(List<String> l) { return l.size(); }
    static int g13(Iterator<String> it) { return it.next().length(); }
    static int g14(NpeOps q, int i) { return q.kids[i + 1].name.length(); }
    static int g15(NpeOps q) { NpeOps x = q; x = x.next; return x.name.length(); }
    static int g17() { return sarr[0].hashCode(); }
    static int g18(NpeOps[] a) { return a[a.length - 1].name.length(); }
    static int g19(String s) { return s.concat("x").length() + s.length(); }
    static int g20(NpeOps q) { return q.next.kids.length; }
    static int g21() { return mk().next.name.length(); }
    static void g22(NpeOps q) { q.next.arr[0] = 1; }
    static int g23(Object o, String[] k) { return o.equals(k[0]) ? 1 : k[1].length(); }
    static int g24(Map<Object, Object> m) { return m.put("a", null).hashCode(); }
    static int g25(NpeOps p) { int x = 0; for (int i = 0; i < 2; i++) x += i; return p.name.length() + x; }

    static int h2(NpeOps p) { p = p.next; return p.name.length(); }
    static int h3(NpeOps p, boolean b) { if (b) p = p.next; return p.name.length(); }
    static int h4(NpeOps p) { int n = p.name.length(); p = null; return n; }
    static int h5(String s) { try { return Integer.parseInt("x"); } catch (NumberFormatException e) { return s.length(); } }
    static int h6(String s, String t) { s = t; try { return Integer.parseInt("x"); } catch (RuntimeException e) { return s.length(); } }
    static int h7(int k, String a, String b) { String r; switch (k) { case 0: r = a; break; case 1: r = b; break; default: r = null; } return r.length(); }
    static int h8(NpeOps q, boolean b) { return (b ? q.next : q.kids[0]).name.length(); }
    static int h9(int[][] g, int k) { switch (k) { case 0: return g[100][0]; case 1: return g[200][0]; default: return g[35000][0]; } }
    static int h10(int[][] g, int[] ix) { return g[ix[ix[0]]][0]; }
    static int h11(NpeOps q) { return q.self().self().self().self().self().next.name.length(); }
    static int h12(Function<String, Integer> f) { return f.apply(null); }
    static int h13() { Function<String, Integer> f = x -> x.length(); return f.apply(null); }
    static void h14(NpeOps p) { p.lf = 5L; }
    static void h15(long[] a) { a[0] = 1L; }
    static String h16(StringBuilder sb) { return sb.append(1.5).toString(); }
    static void h17(NpeOps p) { p.cnt += 1; }
    static void h18(int[] a, int i) { a[i]++; }
    static int h19(List<String> l) { int n = 0; for (String s : l) n += s.length(); return n; }
    static int h20(int[] arr) { int n = 0; for (int x : arr) n += x; return n; }
    static int h21(Integer i, boolean b) { int x = b ? i : 0; return x; }
    static int h22(NpeOps p) { NpeOps x = p; while (x != null && x.cnt < 3) x = x.next; return x.name.length(); }
    static int h23(String a, String b, int k) { return (k > 0 ? a : b).length() + k; }
    static int h24(NpeOps p) { long w = 7L; double d = 2.0; NpeOps loc = p.next; return loc.name.length() + (int) (w + d); }

    public static String npes(int seed) {
        NpeOps q = new NpeOps();
        q.kids = new NpeOps[2];
        q.kids[0] = new NpeOps();
        q.kids[0].kids = new NpeOps[2];
        q.grid = new int[2][];
        NpeOps chain = new NpeOps();
        NpeOps c = chain;
        for (int i = 0; i < 5; i++) {
            c.next = new NpeOps();
            c = c.next;
        }
        try {
            switch (Math.floorMod(seed, 82)) {
                case 0: f1(null); break;
                case 1: f2(new NpeOps()); break;
                case 2: { NpeOps p = new NpeOps(); p.next = new NpeOps(); f3(p); break; }
                case 3: sp = new NpeOps(); f4(); break;
                case 4: f5(); break;
                case 5: f6(null); break;
                case 6: f7(null); break;
                case 7: f8(null); break;
                case 8: f9(new Object[1], 0); break;
                case 9: f10(null); break;
                case 10: f11(null); break;
                case 11: f12(null); break;
                case 12: f13(new HashMap<>()); break;
                case 13: { List<Integer> l = new ArrayList<>(); l.add(null); f14(l); break; }
                case 14: f15(null); break;
                case 15: f16(new NpeOps()); break;
                case 16: new NpeOps().f17(); break;
                case 17: f18(null, "b"); break;
                case 18: f19(null); break;
                case 19: f20(new AbstractMap.SimpleEntry<>(null, "v")); break;
                case 20: f21(new NpeOps[3]); break;
                case 21: f22(null); break;
                case 22: f23(null); break;
                case 23: f24(); break;
                case 24: f25(true, null, "y"); break;
                case 25: f26(new NpeOps()); break;
                case 26: f27(null); break;
                case 27: f28(null); break;
                case 28: f29(null); break;
                case 29: f30(new Integer[1]); break;
                case 30: g1(); break;
                case 31: g3(); break;
                case 32: g4(1, null, 2, "d"); break;
                case 33: g5(1, "b", 2, null); break;
                case 34: g6(new NpeOps()); break;
                case 35: g8(q); break;
                case 36: g9(q); break;
                case 37: g10(chain); break;
                case 38: new NpeOps().g11(); break;
                case 39: g12(null); break;
                case 40: { List<String> l = new ArrayList<>(); l.add(null); g13(l.iterator()); break; }
                case 41: g14(q, 0); break;
                case 42: g15(new NpeOps()); break;
                case 43: sarr = new Object[1]; g17(); break;
                case 44: g18(new NpeOps[2]); break;
                case 45: g19(null); break;
                case 46: g20(new NpeOps()); break;
                case 47: g21(); break;
                case 48: g22(new NpeOps()); break;
                case 49: g23(null, new String[2]); break;
                case 50: g23("x", new String[2]); break;
                case 51: g24(new HashMap<>()); break;
                case 52: g25(new NpeOps()); break;
                case 53: sp = null; f4(); break;
                case 54: sarr = null; g17(); break;
                case 55: h2(new NpeOps()); break;
                case 56: h3(new NpeOps(), false); break;
                case 57: h3(new NpeOps(), true); break;
                case 58: h4(null); break;
                case 59: h5(null); break;
                case 60: h6("s", null); break;
                case 61: h7(Math.floorMod(seed >> 7, 3), null, null); break;
                case 62: h8(q, true); break;
                case 63: h8(q, false); break;
                case 64: h9(new int[40000][], Math.floorMod(seed >> 7, 3)); break;
                case 65: { int[] ix = {1, 0}; h10(new int[2][], ix); break; }
                case 66: h11(new NpeOps()); break;
                case 67: h12(String::length); break;
                case 68: h13(); break;
                case 69: h14(null); break;
                case 70: h15(null); break;
                case 71: h16(null); break;
                case 72: h17(null); break;
                case 73: h18(null, 0); break;
                case 74: h19(null); break;
                case 75: h20(null); break;
                case 76: h21(null, true); break;
                case 77: h22(new NpeOps()); break;
                case 78: h23(null, "b", 1); break;
                case 79: h23("a", null, -1); break;
                case 80: h24(new NpeOps()); break;
                default: { NpeOps p = new NpeOps(); p.next = new NpeOps(); h22(p); break; }
            }
            return "no NPE";
        } catch (NullPointerException e) {
            return e.getMessage();
        }
    }
}

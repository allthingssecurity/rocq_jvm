package org.rocqjvm.jdkmodel;

import java.util.List;

/** Differential tests of record toString/hashCode/equals whose components call back into bytecode
 *  (user objects with toString/hashCode/equals that log their calls, nested records, lists, arrays,
 *  exceptions thrown by a component method). */
public final class RecordOps {
    private RecordOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static StringBuilder log;

    static final class P {
        final int v;
        P(int v) { this.v = v; }
        @Override public String toString() { log.append("t").append(v); if (v == 13) throw new IllegalStateException("bad " + v); return "P" + v; }
        @Override public int hashCode() { log.append("h").append(v); return v * 7; }
        @Override public boolean equals(Object o) { log.append("e").append(v); return o instanceof P && ((P) o).v == v; }
    }

    record A(int i, P p, String s) { }
    record B(P x, long l, P y, double d, char c) { }
    record C(A a, List<P> ps, Object o, boolean z, float f) { }
    record D(P p) { }

    static P p() { return r(5) == 0 ? null : new P(r(15)); }

    public static String records(int seed) {
        s = seed;
        log = new StringBuilder();
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 5; k++) {
            try {
                A a1 = new A(r(3), p(), r(3) == 0 ? null : "s" + r(3));
                A a2 = r(2) == 0 ? a1 : new A(a1.i(), r(2) == 0 ? a1.p() : p(), a1.s());
                B b1 = new B(p(), r(3), p(), r(4) == 0 ? Double.NaN : r(3) * 0.5, (char) ('a' + r(3)));
                B b2 = new B(b1.x(), b1.l(), r(2) == 0 ? b1.y() : p(), b1.d(), b1.c());
                C c1 = new C(a1, List.of(new P(r(5)), new P(r(5))), r(2) == 0 ? (Object) b1 : "obj", r(2) == 0, r(3) * 0.25f);
                C c2 = new C(a2, c1.ps(), c1.o(), c1.z(), c1.f());
                out.append(a1).append(a1.hashCode()).append(a1.equals(a2)).append(a2.equals(a1)).append(a1.equals(null)).append(a1.equals("x")).append('|');
                out.append(b1).append(b1.hashCode()).append(b1.equals(b2)).append('|');
                out.append(c1.hashCode()).append(c1.equals(c2)).append(c1).append('|');
                out.append(new D(null)).append(new D(null).hashCode()).append(new D(null).equals(new D(p())));
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append('[').append(log).append(']').append(';');
            log.setLength(0);
        }
        return out.toString();
    }

    static final class Q {
        static int inits;
        static int created = 1;
        final long v;
        Q(int v) { this.v = v; log.append("Q(int)"); }
        Q(long v, char c) { this.v = v + c; log.append("Q(long,char)"); }
        Q(Integer v, double d) { this.v = v == null ? -1 : v + (long) d; log.append("Q(Integer,double)"); }
        @Override public String toString() { return "Q" + v; }
    }

    interface IntToObj { Object make(Integer x); }
    interface LongMaker { Q make(int x, char c); }
    interface Boxing { Object make(int x, float d); }
    interface Sink { void make(int x); }

    /** Constructor references that need LambdaMetafactory's conversions (unboxing, widening,
     *  boxing, a dropped result), incl. a null to unbox and the class initialisation order. */
    public static String ctors(int seed) {
        s = seed;
        log = new StringBuilder();
        StringBuilder out = new StringBuilder();
        IntToObj a = Q::new;
        LongMaker b = Q::new;
        Boxing c = Q::new;
        Sink d = Q::new;
        java.util.function.Function<Integer, Q> e = Q::new;
        java.util.function.BiFunction<Integer, Double, Q> f = Q::new;
        for (int k = 0; k < 6; k++) {
            try {
                switch (r(6)) {
                    case 0: out.append(a.make(r(4) == 0 ? null : r(100))); break;
                    case 1: out.append(b.make(r(100), (char) ('a' + r(3)))); break;
                    case 2: out.append(c.make(r(100), r(10) * 0.5f)); break;
                    case 3: d.make(r(9)); break;
                    case 4: out.append(e.apply(r(4) == 0 ? null : r(50))); break;
                    default: out.append(f.apply(r(3) == 0 ? null : r(9), r(4) == 0 ? null : r(9) * 1.5)); break;
                }
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.append(log).toString();
    }
}

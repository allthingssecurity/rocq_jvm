package org.rocqjvm.corpus8;

import java.io.Serializable;
import java.util.function.*;

/** Corpus 8 (javac --release 21): invokedynamic beyond string concatenation and plain lambdas.
 *  Constructor references (REF_newInvokeSpecial), LambdaMetafactory.altMetafactory (serializable
 *  lambdas, marker interfaces, bridges), records (ObjectMethods.bootstrap: toString, equals,
 *  hashCode), pattern switches (SwitchBootstraps.typeSwitch, enumSwitch). */
public class Indy {
    // ---- constructor references
    static class Box { static int made; final int v; Box(int v) { this.v = v; made++; } Box() { this(-1); } }
    static class Pair { final int a; final long b; Pair(int a, long b) { this.a = a; this.b = b; } }
    static class Lazy { static int inits; static { inits = Box.made + 100; } final int v; Lazy(int v) { this.v = v + inits; } }
    static class BadNew { static int z = 1 / Indy.zero; BadNew(int v) { } }
    static int zero;
    interface PairMaker { Pair make(int a, long b); }
    static int ctorRefs(int x) {
        IntFunction<Box> f = Box::new;
        Supplier<Box> s = Box::new;
        PairMaker pm = Pair::new;
        Function<Integer, Box> g = Box::new;
        Box b1 = f.apply(x), b2 = s.get(), b3 = g.apply(x ^ 3);
        Pair p = pm.make(x, (long) x * 3);
        IntFunction<Lazy> lz = Lazy::new;          // Lazy is initialised when the constructor runs
        int before = Lazy.inits;                   // 0 + ... initialises Lazy here: inits = made + 100
        return b1.v + b2.v + b3.v + p.a + (int) p.b + Box.made * 1000 + lz.apply(x & 0xff).v + before;
    }
    static int ctorRefInit(int x) {
        IntFunction<Lazy> lz = Lazy::new;          // linking the call site does not initialise Lazy
        new Box(1); new Box(2);
        return lz.apply(x & 0xff).v;               // initialises Lazy now: inits = 2 + 100
    }
    static int ctorRefFail(int x) {
        IntFunction<BadNew> f = BadNew::new;
        int r = 0;
        try { f.apply(x); } catch (ExceptionInInitializerError e) { r += 1; }
        try { f.apply(x); } catch (NoClassDefFoundError e) { r += 10; }
        return r;
    }
    static int arrayCtorRef(int x) {
        IntFunction<int[]> f = int[]::new;
        try { return f.apply(x & 0x1ff).length; } catch (NegativeArraySizeException e) { return -1; }
    }

    // ---- altMetafactory
    interface Marker { }
    interface Gen<T> { T get(); }
    interface StrGen extends Gen<String> { String get(); }
    interface IntOp extends IntUnaryOperator, Serializable { }
    static int altMeta(int x) {
        Runnable r = (Runnable & Serializable) () -> { };
        IntSupplier m = (IntSupplier & Marker) () -> x + 1;
        StrGen sg = () -> "s" + x;
        Gen<String> gg = sg;                       // call through the bridge get()Ljava/lang/Object;
        IntOp op = v -> v * 2;
        Object o = (x & 1) != 0 ? r : m;
        int res = (o instanceof Serializable ? 1 : 0) + (o instanceof Marker ? 2 : 0) + (o instanceof Runnable ? 4 : 0)
                + (o instanceof IntSupplier ? 8 : 0) + m.getAsInt() * 16 + sg.get().length() * 100000 + gg.get().length() * 1000000
                + (op instanceof Serializable ? 10000000 : 0) + op.applyAsInt(3);
        try { Marker mk = (Marker) o; res += 1 << 30; } catch (ClassCastException e) { res -= 1; }
        r.run();
        return res;
    }

    // ---- records
    record Pt(int x, int y) { }
    record Mixed(long l, char c, boolean z, byte b, short s, String str, Integer boxed, Character ch, Boolean bo, Long lo) { }
    record Empty() { }
    record Fl(float f, double d) { }
    record Holder(Object o) { }
    static String recToString(int x) {
        Pt p = new Pt(x, -x);
        Mixed m = new Mixed((long) x << 20, (char) (x & 0x7f | 0x40), (x & 1) != 0, (byte) x, (short) x,
                            (x & 2) != 0 ? null : "q" + x, (x & 4) != 0 ? null : x, (char) (x & 0xff), (x & 8) != 0, (long) x * 7);
        return p.toString() + "|" + m.toString() + "|" + new Empty().toString();
    }
    static int recEquals(int x) {
        Pt a = new Pt(x, x >> 3), b = new Pt(x, (x & 0xff) >> 3), c = a;
        Mixed m1 = new Mixed(x, 'a', true, (byte) 1, (short) 2, (x & 1) != 0 ? "a" : null, x & 0xf, 'c', true, 5L);
        Mixed m2 = new Mixed(x, 'a', true, (byte) 1, (short) 2, (x & 2) != 0 ? "a" : null, x & 0x7, 'c', true, 5L);
        Fl f1 = new Fl(fl(x), (double) fl(x >> 1));
        Fl f2 = new Fl(fl(x | 1), (double) fl(x >> 1));
        Object other = (x & 4) != 0 ? "str" : null;
        return (a.equals(b) ? 1 : 0) + (a.equals(c) ? 2 : 0) + (a.equals(other) ? 4 : 0) + (m1.equals(m2) ? 8 : 0)
             + (f1.equals(f2) ? 16 : 0) + (f1.equals(f1) ? 32 : 0) + (new Empty().equals(new Empty()) ? 64 : 0)
             + (a.equals(m1) ? 128 : 0) + (f1.equals(new Fl(f1.f(), f1.d())) ? 256 : 0);
    }
    static int recHash(int x) {
        Pt a = new Pt(x, x * 31);
        Mixed m = new Mixed((long) x * 1000003L, (char) x, (x & 1) != 0, (byte) x, (short) (x >> 3),
                            (x & 2) != 0 ? null : "h" + (x & 0xff), (x & 4) != 0 ? null : x, (char) (x >> 5), (x & 8) == 0, (long) x << 17);
        Fl f = new Fl(fl(x), (double) x / (double) (x & 7) - 0.25);
        return a.hashCode() * 3 + m.hashCode() * 7 + f.hashCode() + new Empty().hashCode();
    }
    /** float values incl. NaN, infinities, -0.0 and ordinary ones, without Float.intBitsToFloat */
    static float fl(int x) { int k = x & 7; return k == 0 ? 0.0f / 0.0f : k == 1 ? -(float) (x & 0) : k == 2 ? (float) x / 0.0f : (float) x / (float) k; }
    static String recHolder(int x) { return new Holder((x & 1) != 0 ? null : "z" + x).toString(); }

    // ---- pattern switches
    sealed interface Shape permits Circle, Square, Rect { }
    record Circle(int r) implements Shape { }
    record Square(int side) implements Shape { }
    record Rect(int w, int h) implements Shape { }
    enum Color { RED, GREEN, BLUE, BLACK { int dark() { return 1; } }; int dark() { return 0; } }
    static int typeSwitch(int x) {
        Object o = switch ((x & 0x7fffffff) % 9) {
            case 0 -> "s" + x; case 1 -> x; case 2 -> (long) x; case 3 -> new Circle(x);
            case 4 -> new Rect(x, 2); case 5 -> null; case 6 -> Color.values()[(x >>> 4) & 3];
            case 7 -> (char) x; default -> new int[x & 3];
        };
        try {
            return switch (o) {
                case null -> -1;
                case String s when s.length() > 3 -> 1;
                case String s -> 2;
                case Integer i when i > 100 -> 3;
                case Integer i -> 4;
                case Long l -> 5;
                case Circle(int r) when r < 0 -> 6;
                case Circle c -> 7;
                case Rect(int w, int h) -> 8 + w * h;
                case Color c when c == Color.RED -> 9;
                case Color c -> 10 + c.dark();
                case Character c -> 11;
                case int[] a -> 12 + a.length;
                default -> 13;
            };
        } catch (MatchException e) { return -2; }
    }
    static int sealedSwitch(int x) {
        Shape s = switch ((x & 0x7fffffff) % 3) { case 0 -> new Circle(x); case 1 -> new Square(x >> 1); default -> new Rect(x, x >> 2); };
        return switch (s) {
            case Circle c -> c.r();
            case Square q -> q.side() * 2;
            case Rect r -> r.w() - r.h();
        };
    }
    static int stringSwitch(int x) {
        String s = switch ((x & 0x7fffffff) % 5) { case 0 -> "alpha"; case 1 -> "beta"; case 2 -> "gamma" + x; case 3 -> null; default -> ""; };
        return switch (s) {
            case null -> -1;
            case "alpha" -> 1;
            case "beta" -> 2;
            case String t when t.startsWith("gamma") -> 3;
            case String t -> 4;
        };
    }
    static int boxSwitch(int x) {
        Integer i = (x & 1) != 0 ? null : x % 7;
        return switch (i) {
            case null -> -1;
            case 1 -> 10;
            case 2 -> 20;
            case Integer j when j > 3 -> 30 + j;
            case Integer j -> 40 + j;
        };
    }
    static int enumSwitch(int x) {
        Color c = (x & 0x10) != 0 ? null : Color.values()[(x & 0x7fffffff) % 4];
        return switch (c) {
            case null -> -1;
            case RED -> 1;
            case GREEN -> 2;
            case Color k when k.dark() == 1 -> 3;
            case Color k -> 4 + k.ordinal();
        };
    }
}

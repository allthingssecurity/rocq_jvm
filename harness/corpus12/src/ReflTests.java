// corpus12: java.lang.reflect (Method, Constructor, Field) against HotSpot.
import java.lang.reflect.*;

class Hidden {
    private int secret(int x) { return x * 7; }
    int pkg(int x) { return x + 1; }
    private static String hush() { return "hush"; }
    private int f = 3;
}

public class ReflTests {
    static int small(int n) { return Math.floorMod(n, 50); }

    public static int add(int a, int b) { return a + b; }
    public static long widen(long a) { return a * 2; }
    public static String concat(String a, Object b) { return a + "/" + b; }
    public static void boom(int x) { if (x % 2 == 0) throw new IllegalStateException("even " + x); else throw new ArithmeticException(); }
    public static boolean flag(boolean b, char c) { return b && c == 'x'; }

    static class Base { public int who() { return 1; } public int base() { return 10; } }
    static class Derived extends Base { @Override public int who() { return 2; } private int priv() { return 99; } }

    static class Point {
        public int x; private final int y; public static int count; static String label = "pt";
        public Point(int x, int y) { this.x = x; this.y = y; count++; }
        private Point() { this(-1, -1); }
        public int sum() { return x + y; }
    }

    static int initCount;
    static class Lazy { static { initCount++; } public static int get() { return 42 + initCount; } }

    static String exc(Throwable t) {
        if (t instanceof InvocationTargetException) {
            Throwable c = ((InvocationTargetException) t).getCause();
            return "ITE(" + c.getClass().getName() + ":" + c.getMessage() + ")";
        }
        return t.getClass().getName() + ":" + t.getMessage();
    }

    public static String invokeStatic(int n) throws Exception {
        Method m = ReflTests.class.getMethod("add", int.class, int.class);
        Object r = m.invoke(null, n, small(n));
        Method w = ReflTests.class.getMethod("widen", long.class);
        Object r2 = w.invoke(null, small(n));            // Integer widened to long
        Method c = ReflTests.class.getDeclaredMethod("concat", String.class, Object.class);
        Object r3 = c.invoke(null, "a", n % 3 == 0 ? null : (Object) small(n));
        Method f = ReflTests.class.getMethod("flag", boolean.class, char.class);
        return r + " " + r2 + " " + r3 + " " + f.invoke(null, n % 2 == 0, 'x') + " " + m.getName() + " " + m.getParameterCount()
            + " " + m.getReturnType().getName() + " " + m.getParameterTypes()[1].getName() + " " + m.getModifiers();
    }

    public static String invokeVirtual(int n) throws Exception {
        Base b = n % 2 == 0 ? new Base() : new Derived();
        Method m = Base.class.getMethod("who");
        Method k = Derived.class.getMethod("base");
        return m.invoke(b) + " " + k.invoke(new Derived()) + " " + k.getDeclaringClass().getSimpleName() + " " + small(n);
    }

    public static String invokeErrors(int n) {
        String out = "";
        try {
            Method m = ReflTests.class.getMethod("boom", int.class);
            m.invoke(null, small(n));
        } catch (Exception e) { out += exc(e); }
        try { ReflTests.class.getMethod("add", int.class, int.class).invoke(null, 1); } catch (Exception e) { out += " " + exc(e); }
        try { ReflTests.class.getMethod("add", int.class, int.class).invoke(null, 1, "two"); } catch (Exception e) { out += " " + exc(e); }
        try { Base.class.getMethod("who").invoke(null); } catch (Exception e) { out += " " + e.getClass().getName(); }
        try { Base.class.getMethod("who").invoke("str"); } catch (Exception e) { out += " " + exc(e); }
        try { ReflTests.class.getMethod("nope", int.class, String[].class); } catch (Exception e) { out += " " + exc(e); }
        try { ReflTests.class.getMethod("add", long.class, int.class); } catch (Exception e) { out += " " + exc(e); }
        return out + " " + small(n);
    }

    public static String access(int n) throws Exception {
        Hidden h = new Hidden();
        String out = "";
        Method s = Hidden.class.getDeclaredMethod("secret", int.class);
        try { out += s.invoke(h, small(n)); } catch (IllegalAccessException e) { out += "IAE[" + e.getMessage() + "]"; }
        s.setAccessible(true);
        out += " " + s.invoke(h, small(n));
        Method p = Hidden.class.getDeclaredMethod("pkg", int.class);
        out += " " + p.invoke(h, small(n));
        Method hs = Hidden.class.getDeclaredMethod("hush");
        try { out += " " + hs.invoke(null); } catch (IllegalAccessException e) { out += " IAE[" + e.getMessage() + "]"; }
        Method dp = Derived.class.getDeclaredMethod("priv");     // a nestmate: allowed
        out += " " + dp.invoke(new Derived());
        try { Derived.class.getMethod("priv"); } catch (NoSuchMethodException e) { out += " NSME[" + e.getMessage() + "]"; }
        return out;
    }

    public static String constructors(int n) throws Exception {
        Constructor<Point> c = Point.class.getConstructor(int.class, int.class);
        int before = Point.count;
        Point p = c.newInstance(small(n), 5);
        Constructor<Point> d = Point.class.getDeclaredConstructor();
        String out = p.sum() + " " + (Point.count - before) + " " + c.getParameterCount() + " " + c.getName() + " " + c.getModifiers();
        try { d.newInstance(); } catch (IllegalAccessException e) { out += " IAE"; }
        d.setAccessible(true);
        out += " " + d.newInstance().sum();
        try { c.newInstance(1); } catch (IllegalArgumentException e) { out += " " + exc(e); }
        try { Point.class.getConstructor(String.class); } catch (NoSuchMethodException e) { out += " " + exc(e); }
        return out;
    }

    public static String fields(int n) throws Exception {
        Point p = new Point(small(n), 2);
        Field fx = Point.class.getField("x");
        Field fy = Point.class.getDeclaredField("y");
        Field fc = Point.class.getField("count");
        Field fl = Point.class.getDeclaredField("label");
        String out = fx.get(p) + " " + fx.getType().getName() + " " + fx.getModifiers() + " " + fy.getModifiers() + " " + fc.getModifiers();
        fx.set(p, 40 + small(n));
        out += " " + p.x + " " + fl.get(null) + " " + fy.getName() + " " + fy.getDeclaringClass().getSimpleName();
        try { fy.get(p); out += " noIAE"; } catch (IllegalAccessException e) { out += " IAE"; }
        try { Point.class.getField("y"); } catch (NoSuchFieldException e) { out += " NSFE[" + e.getMessage() + "]"; }
        try { Point.class.getField("zz"); } catch (NoSuchFieldException e) { out += " NSFE[" + e.getMessage() + "]"; }
        Field hf = Hidden.class.getDeclaredField("f");
        try { hf.get(new Hidden()); } catch (IllegalAccessException e) { out += " [" + e.getMessage() + "]"; }
        return out;
    }

    public static int staticInit(int n) throws Exception {
        Method g = Lazy.class.getMethod("get");
        int before = initCount;
        int r = (Integer) g.invoke(null);
        return r * 100 + before * 10 + initCount + small(n) * 1000;
    }
}

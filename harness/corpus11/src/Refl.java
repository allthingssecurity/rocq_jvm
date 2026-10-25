// corpus11: reflection on class objects (java.lang.Class) and exception messages of
// exceptions created by user code. Results are Strings compared with HotSpot.
import java.util.Map;
import java.util.List;
import java.io.Serializable;

public class Refl {
    static final class Inner { }
    interface Shape { }
    static class Base implements Shape { }
    static final class Derived extends Base { }
    enum Color { RED, GREEN }
    static class MyEx extends RuntimeException { MyEx(String m) { super(m); } }

    static Object pick(int n) {
        switch (Math.floorMod(n, 8)) {
            case 0: return "str";
            case 1: return new int[3];
            case 2: return new Derived();
            case 3: return new Base();
            case 4: return new String[1][2];
            case 5: return Color.GREEN;
            case 6: return new Inner();
            default: return new Object();
        }
    }

    public static String names(int n) {
        Class<?> c = pick(n).getClass();
        return c.getName() + "|" + c.getSimpleName() + "|" + c.isArray() + "|" + c.isInterface();
    }

    public static String hierarchy(int n) {
        Class<?> c = pick(n).getClass();
        Class<?> s = c.getSuperclass();
        Class<?> k = c.getComponentType();
        return (s == null ? "null" : s.getName()) + "|" + (k == null ? "null" : k.getName()) + "|" + c.isEnum();
    }

    public static String instances(int n) {
        Object o = pick(n);
        Class<?>[] cs = { Object.class, Shape.class, Base.class, Derived.class, String.class, Serializable.class,
                          Comparable.class, Object[].class, int[].class, Enum.class, CharSequence.class };
        StringBuilder sb = new StringBuilder();
        for (Class<?> c : cs) sb.append(c.isInstance(o) ? '1' : '0');
        sb.append('|');
        for (Class<?> c : cs) sb.append(c.isAssignableFrom(o.getClass()) ? '1' : '0');
        return sb.toString();
    }

    public static String casts(int n) {
        Object o = pick(n);
        try { Base b = Base.class.cast(o); return "ok " + (b == null ? "null" : b.getClass().getSimpleName()); }
        catch (ClassCastException e) { return "CCE"; }
    }

    public static String simpleNames(int n) {
        Class<?>[] cs = { Map.Entry.class, List.class, Inner.class, Color.class, int[].class, Derived[][].class,
                          new Object() { }.getClass(), Refl.class };
        Class<?> c = cs[Math.floorMod(n, cs.length)];
        return c.getSimpleName() + "|" + c.getName() + "|" + c.isInterface() + "|" + c.toString();
    }

    public static String forName(int n) throws Exception {
        String[] ns = { "java.lang.String", "Refl$Base", "java.util.Map", "[I", "[Ljava.lang.Object;" };
        Class<?> c = Class.forName(ns[Math.floorMod(n, ns.length)]);
        return c.getName() + "|" + (c == String.class) + "|" + (c == Base.class);
    }

    static int checked(int x) { assert x > 0 : "x must be positive"; return x * 2; }

    public static int assertions(int n) { return checked(n) + (Refl.class.desiredAssertionStatus() ? 1 : 0); }

    public static String messages(int n) {
        RuntimeException[] es = { new IllegalStateException("bad state " + n), new IllegalArgumentException(),
                                  new RuntimeException("x", null), new RuntimeException((Throwable) null),
                                  new MyEx("mine " + (n % 7)), new UnsupportedOperationException("nope") };
        RuntimeException e = es[Math.floorMod(n, es.length)];
        try { throw e; }
        catch (RuntimeException r) { return r.getClass().getName() + "|" + r.getMessage(); }
    }

    public static String exToString(int n) {
        RuntimeException[] es = { new IllegalStateException("s" + n), new ArithmeticException(), new IndexOutOfBoundsException("i") };
        return es[Math.floorMod(n, es.length)].toString();
    }
}

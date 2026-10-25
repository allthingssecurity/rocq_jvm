// toString() called back from the JDK models: String.valueOf(Object), StringBuilder.append(Object)
// and string concatenation with object arguments (invokedynamic makeConcatWithConstants).
public class ToStr {
    static int calls;
    static final class P {
        final int x; P(int x) { this.x = x; }
        public String toString() { calls++; return "P(" + x + ")"; }
    }
    static final class N { public String toString() { calls++; return null; } }
    static final class Bad { public String toString() { calls++; throw new IllegalStateException("bad" + calls); } }
    static class Base { public String toString() { return "base"; } }
    static class Sub extends Base { public String toString() { return "sub/" + super.toString(); } }
    static final class Self { int n; public String toString() { return n < 3 ? "s" + (n++) + this : "end"; } }

    public static String valueOfs(int n) {
        calls = 0;
        Object o = (n & 3) == 0 ? new P(n) : (n & 3) == 1 ? new N() : (n & 3) == 2 ? new Sub() : new Base();
        String v = String.valueOf(o);
        return v + "|" + (v == null) + "|" + calls;
    }
    public static String appends(int n) {
        calls = 0;
        StringBuilder sb = new StringBuilder();
        sb.append(new P(n % 7)).append(',').append(new N()).append(',').append((Object) "str").append(new Sub());
        Object[] arr = { new P(1), null, Integer.valueOf(n % 5), new Base() };
        for (Object o : arr) sb.append(o);
        return sb + "#" + calls;
    }
    public static String concats(int n) {
        calls = 0;
        P p = new P(n % 100);
        Object nul = (n & 1) == 0 ? new N() : null;
        long l = n * 3L;
        char c = (char) ('a' + (n & 7));
        boolean b = n > 0;
        String s = "x" + p + "-" + nul + ":" + l + c + b + new Sub() + (n % 3) + p;
        return s + "#" + calls;
    }
    public static String throwing(int n) {
        calls = 0;
        try {
            String s = (n & 1) == 0 ? "a" + new Bad() : String.valueOf(new Bad());
            return s;
        } catch (IllegalStateException e) {
            return "caught " + e.getMessage() + " " + calls;
        }
    }
    public static String nested(int n) {
        Self s = new Self();
        s.n = n & 3;
        return "<" + s + ">";
    }
}

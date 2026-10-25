// corpus13: lambdas and method references that need LambdaMetafactory's conversions (boxing,
// unboxing, widening, casts, dropped results), against HotSpot.
import java.util.*;
import java.util.function.*;

public class LamConv {
    static int twice(int x) { return 2 * x; }
    static long wide(long x) { return x + 1; }
    static Integer boxed(int x) { return x * 3; }
    static void sink(int x) { last = x; }
    static int last;
    int field = 5;
    int add(int y) { return field + y; }

    public static int supplierBox(int n) {
        Supplier<Integer> s = () -> twice(n);             // lambda body: boxing in the body (no conversion)
        IntSupplier is = () -> n + 1;
        Supplier<Object> o = LamConv::counter;            // ()I as ()Object: boxing by the metafactory
        return s.get() + is.getAsInt() + (Integer) o.get();
    }
    static int counter() { return 7; }

    public static int unboxArgs(int n) {
        BinaryOperator<Integer> max = Math::max;          // (II)I as (Object,Object)Object: unbox args, box result
        Comparator<Integer> cmp = Integer::compare;       // (II)I as (Object,Object)I
        Function<Integer, Integer> tw = LamConv::twice;   // (I)I as (Object)Object
        return max.apply(n, 3) + cmp.compare(n, 0) * 100 + tw.apply(n % 1000);
    }

    public static long widening(int n) {
        IntToLongFunction w = LamConv::wide;              // (J)J as (I)J: int widened to long
        ToLongFunction<Integer> u = LamConv::wide;        // Integer unboxed then widened
        IntFunction<Integer> b = LamConv::boxed;
        return w.applyAsLong(n) + u.applyAsLong(n % 100) + b.apply(n % 50);
    }

    public static int casts(int n) {
        ToIntFunction<String> len = String::length;       // receiver cast from Object to String
        Function<String, Integer> len2 = String::length;  // and the result boxed
        BiFunction<LamConv, Integer, Integer> add = LamConv::add;  // receiver and unboxing
        String s = "x".repeat(Math.floorMod(n, 9));
        return len.applyAsInt(s) * 10 + len2.apply(s + "ab") + add.apply(new LamConv(), n % 10);
    }

    public static int dropped(int n) {
        Consumer<Integer> c = LamConv::twice;             // the int result dropped
        IntConsumer k = LamConv::sink;
        Runnable r = LamConv::counter;
        c.accept(n % 100); k.accept(n % 77); r.run();
        return last;
    }

    public static int bound(int n) {
        LamConv me = new LamConv();
        me.field = n % 13;
        IntUnaryOperator op = me::add;                    // bound receiver, no conversion
        Function<Integer, Integer> f = me::add;           // bound receiver, unbox/box
        return op.applyAsInt(1) + f.apply(2) * 100;
    }

    public static String nulls(int n) {
        Function<Integer, Integer> tw = LamConv::twice;
        try { return "" + tw.apply(n % 2 == 0 ? null : 1); } catch (NullPointerException e) { return "NPE"; }
    }

    public static String wrongType(int n) {
        @SuppressWarnings({"rawtypes", "unchecked"})
        Function raw = (Function<Integer, Integer>) LamConv::twice;
        try { return "" + raw.apply(n % 2 == 0 ? "str" : (Object) 4); } catch (ClassCastException e) { return "CCE"; }
    }
}

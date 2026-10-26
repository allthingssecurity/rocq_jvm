package org.rocqjvm.jdkmodel;

import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.function.DoubleBinaryOperator;
import java.util.function.DoubleFunction;
import java.util.function.DoubleUnaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.function.ToDoubleFunction;

/** Differential tests of Arrays.toString/equals/hashCode for every array type, deepToString /
 *  deepEquals / deepHashCode (nested and self-containing arrays), equals/hashCode consistency of
 *  lambda objects, and reflection with float/double parameters and results. */
public final class ArraysOps {
    private ArraysOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static double dv() {
        double[] e = {0.0, -0.0, Double.NaN, 1.5, -2.25, 1e300, Double.MIN_VALUE};
        return r(3) == 0 ? e[r(e.length)] : (r(2000) - 1000) / 8.0;
    }

    public static String arrays(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int n = r(5);
        byte[] b = new byte[n]; short[] sh = new short[n]; char[] c = new char[n]; boolean[] z = new boolean[n];
        float[] f = new float[n]; double[] d = new double[n]; long[] l = new long[n]; int[] in = new int[n];
        for (int i = 0; i < n; i++) {
            b[i] = (byte) (r(256) - 128); sh[i] = (short) (r(65536) - 32768); c[i] = (char) ('a' + r(26)); z[i] = r(2) == 0;
            f[i] = (float) dv(); d[i] = dv(); l[i] = ((long) r(1 << 20) << 30) - r(1000); in[i] = r(1000) - 500;
        }
        out.append(Arrays.toString(b)).append(Arrays.toString(sh)).append(Arrays.toString(c)).append(Arrays.toString(z))
           .append(Arrays.toString(f)).append(Arrays.toString(d)).append(Arrays.toString(l)).append(';');
        out.append(Arrays.hashCode(b)).append(',').append(Arrays.hashCode(sh)).append(',').append(Arrays.hashCode(c)).append(',')
           .append(Arrays.hashCode(z)).append(',').append(Arrays.hashCode(f)).append(',').append(Arrays.hashCode(d)).append(',')
           .append(Arrays.hashCode(l)).append(';');
        double[] d2 = d.clone();
        if (n > 0 && r(2) == 0) d2[r(n)] = dv();
        float[] f2 = f.clone();
        if (n > 0 && r(2) == 0) f2[r(n)] = (float) dv();
        out.append(Arrays.equals(d, d2)).append(Arrays.equals(f, f2)).append(Arrays.equals(l, l.clone()))
           .append(Arrays.equals(b, (byte[]) null)).append(Arrays.equals((char[]) null, (char[]) null)).append(Arrays.equals(z, z.clone()))
           .append(Arrays.equals(sh, sh.clone())).append(';');
        Object[] deep = {b, sh, c, z, f, d, l, in, "s", null, new Object[]{1, new int[]{2}}, r(10)};
        Object[] deep2 = deep.clone();
        if (r(2) == 0) deep2[r(deep2.length)] = r(2) == 0 ? (Object) in.clone() : "x";
        out.append(Arrays.deepToString(deep)).append(Arrays.deepEquals(deep, deep2)).append(Arrays.deepHashCode(deep)).append(',')
           .append(Arrays.deepHashCode(deep2)).append(';');
        Object[] self = new Object[2];
        self[0] = self;
        self[1] = new Object[]{self, "t"};
        out.append(Arrays.deepToString(self)).append(Arrays.deepToString(null)).append(Arrays.deepToString(new Object[0]));
        return out.toString();
    }

    static float fl(int k) { return k / 3f; }

    /** Lambdas and method references converting float/double (boxing, unboxing, widening). */
    public static String lamd(int seed) {
        s = seed;
        double x = dv();
        int k = r(100);
        DoubleUnaryOperator sq = v -> v * v;
        Function<Double, Double> neg = v -> -v;
        ToDoubleFunction<Integer> td = Integer::doubleValue;
        DoubleFunction<String> ds = Double::toString;
        DoubleBinaryOperator mx = Math::max;
        Function<Integer, Float> f3 = ArraysOps::fl;
        Supplier<Double> sup = () -> x;
        Function<Float, Double> wid = Float::doubleValue;
        StringBuilder out = new StringBuilder();
        out.append(sq.applyAsDouble(x)).append(',').append(neg.apply(x)).append(',').append(td.applyAsDouble(k)).append(',')
           .append(ds.apply(x)).append(',').append(mx.applyAsDouble(x, k)).append(',').append(f3.apply(k)).append(',')
           .append(sup.get()).append(',').append(wid.apply((float) x)).append(',').append(sq.andThen(v -> v + 1).applyAsDouble(k));
        try {
            Function<Double, Double> nn = v -> v + 1;
            out.append(nn.apply(null));
        } catch (NullPointerException e) {
            out.append("!NPE");
        }
        return out.toString();
    }

    static double twice(double x) { return 2 * x; }
    static float half(float x, int k) { return x / k; }

    public static String misc(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        Supplier<String> a = () -> "a";
        Supplier<String> a2 = a;
        Supplier<String> bb = () -> "b";
        out.append(a.equals(a2)).append(a.equals(bb)).append(a.hashCode() == a2.hashCode()).append(a.equals(null)).append(';');
        try {
            Method m = ArraysOps.class.getDeclaredMethod("twice", double.class);
            Method h = ArraysOps.class.getDeclaredMethod("half", float.class, int.class);
            Object[] args = {r(3) == 0 ? (Object) Integer.valueOf(r(100)) : r(3) == 0 ? (Object) Float.valueOf(r(100) / 4f) : (Object) Double.valueOf(dv())};
            out.append(m.invoke(null, args)).append(',');
            out.append(h.invoke(null, r(2) == 0 ? (Object) Float.valueOf(r(100) / 8f) : (Object) Long.valueOf(r(100)), r(5) + 1)).append(',');
            out.append(h.invoke(null, Double.valueOf(1.5), 2));
        } catch (ReflectiveOperationException e) {
            out.append('!').append(e.getClass().getSimpleName());
        } catch (IllegalArgumentException e) {
            out.append("!IAE:").append(e.getMessage());
        }
        return out.toString();
    }
}

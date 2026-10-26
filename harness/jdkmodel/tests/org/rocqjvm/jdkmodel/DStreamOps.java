package org.rocqjvm.jdkmodel;

import java.util.Arrays;
import java.util.DoubleSummaryStatistics;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.DoubleStream;
import java.util.stream.IntStream;
import java.util.stream.LongStream;
import java.util.stream.Stream;

/** Differential tests of sequential DoubleStream pipelines (sources, intermediate operations,
 *  compensated sum/average, summary statistics incl. toString), the int/long/ref conversions to
 *  DoubleStream, Int/LongSummaryStatistics and the double collectors. */
public final class DStreamOps {
    private DStreamOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static final double[] SPECIAL = {0.0, -0.0, 1.0, 0.1, 0.2, 0.3, 1e16, -1e16, 1e-16, Double.NaN, Double.POSITIVE_INFINITY,
        Double.NEGATIVE_INFINITY, Double.MAX_VALUE, -1.5, 2.5, 1e300, 3.0};

    static double dv() {
        return r(3) == 0 ? SPECIAL[r(SPECIAL.length)] : (r(20000) - 10000) / 64.0;
    }

    static double[] arr() {
        double[] a = new double[r(8)];
        for (int i = 0; i < a.length; i++) a[i] = r(4) == 0 ? SPECIAL[r(SPECIAL.length)] : (r(2000) - 1000) / 10.0;
        if (r(4) == 0) for (int i = 0; i < a.length; i++) if (Double.isNaN(a[i]) || Double.isInfinite(a[i])) a[i] = 1;
        return a;
    }

    static DoubleStream src() {
        switch (r(6)) {
            case 0: return DoubleStream.of(arr());
            case 1: { double[] a = arr(); return Arrays.stream(a, 0, a.length / 2 + (a.length > 0 ? 1 : 0)); }
            case 2: { double seed = dv(); return DoubleStream.iterate(seed, x -> x / 2 + 1).limit(r(6)); }
            case 3: { DoubleStream.Builder b = DoubleStream.builder(); for (int i = r(5); i > 0; i--) b.add(dv()); return b.build(); }
            case 4: return DoubleStream.concat(DoubleStream.of(arr()), IntStream.range(0, r(4)).asDoubleStream());
            default: return Stream.of("1.5", "-2", "0.25", "1e3").limit(r(5)).mapToDouble(Double::parseDouble);
        }
    }

    static DoubleStream stage(DoubleStream st) {
        switch (r(12)) {
            case 0: return st.filter(x -> x > 0);
            case 1: return st.map(x -> x * 3 - 1);
            case 2: return st.distinct();
            case 3: return st.sorted();
            case 4: return st.limit(r(4));
            case 5: return st.skip(r(3));
            case 6: return st.takeWhile(x -> x < 50);
            case 7: return st.dropWhile(x -> x < 0);
            case 8: return st.flatMap(x -> DoubleStream.of(x, -x));
            case 9: return st.mapToObj(x -> x).mapToDouble(Double::doubleValue);
            case 10: return st.boxed().mapToDouble(x -> x + 0.5);
            default: return st.mapToLong(x -> (long) x).asDoubleStream();
        }
    }

    public static String pipes(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 5; k++) {
            DoubleStream st = src();
            for (int i = r(3); i > 0; i--) st = stage(st);
            try {
                switch (r(12)) {
                    case 0: out.append(st.sum()); break;
                    case 1: out.append(st.average()); break;
                    case 2: out.append(st.min()).append(',').append(DoubleStream.of(arr()).max()); break;
                    case 3: out.append(st.count()); break;
                    case 4: { DoubleSummaryStatistics ds = st.summaryStatistics();
                              out.append(ds).append(ds.getSum()).append(ds.getAverage()).append(ds.getMin()).append(ds.getCount()); break; }
                    case 5: out.append(st.reduce(1, (a, b) -> a * b)).append(',').append(DoubleStream.of(arr()).reduce(Double::sum)); break;
                    case 6: out.append(Arrays.toString(st.toArray())); break;
                    case 7: out.append(st.anyMatch(x -> x == 0)).append(DoubleStream.of(arr()).allMatch(x -> x < 100)).append(DoubleStream.of(arr()).noneMatch(Double::isNaN)); break;
                    case 8: out.append(st.findFirst()).append(DoubleStream.empty().findAny()); break;
                    case 9: { StringBuilder sb = st.collect(StringBuilder::new, (b, x) -> b.append(x).append('/'), (b1, b2) -> b1.append(b2)); out.append(sb); break; }
                    case 10: out.append(st.mapToInt(x -> (int) x).summaryStatistics()); break;
                    default: { List<Double> l = st.boxed().collect(Collectors.toList()); out.append(l); break; }
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String collectors(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        double[] a = arr();
        Stream<Double> bs = Arrays.stream(a).boxed();
        List<Double> l = Arrays.stream(a).boxed().collect(Collectors.toList());
        out.append(l.stream().collect(Collectors.summingDouble(x -> x))).append(',')
           .append(l.stream().collect(Collectors.averagingDouble(x -> x))).append(',')
           .append(l.stream().collect(Collectors.summarizingDouble(x -> x))).append(',')
           .append(l.stream().collect(Collectors.summarizingInt(Double::intValue))).append(',')
           .append(l.stream().collect(Collectors.summarizingLong(Double::longValue))).append(',')
           .append(bs.count()).append(',')
           .append(IntStream.range(0, r(10)).average()).append(IntStream.range(0, r(10)).summaryStatistics())
           .append(LongStream.rangeClosed(-r(5), r(5)).summaryStatistics()).append(',')
           .append(l.stream().mapToDouble(x -> x).sum()).append(DoubleStream.generate(() -> 0.1).limit(10).sum())
           .append(DoubleStream.of(1e16, 1, -1e16).sum()).append(DoubleStream.of(Double.POSITIVE_INFINITY, 1).sum())
           .append(DoubleStream.of(Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY).sum());
        try {
            new DoubleSummaryStatistics(r(3) - 1, r(3), r(3), r(2) == 0 ? Double.NaN : 1);
            out.append("ok");
        } catch (IllegalArgumentException e) {
            out.append("!IAE:").append(e.getMessage());
        }
        return out.toString();
    }
}

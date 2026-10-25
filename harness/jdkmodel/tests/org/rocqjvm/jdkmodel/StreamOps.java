package org.rocqjvm.jdkmodel;

import java.util.*;
import java.util.function.*;
import java.util.stream.*;

/** Differential tests of sequential java.util.stream (Stream, IntStream, LongStream, Collectors),
 *  Optional/OptionalInt/OptionalLong, StringJoiner and the default/static methods of the
 *  java.util.function interfaces. Lambdas log their calls into the output, so the order in which
 *  the pipeline calls them (laziness, short-circuiting, SIZED count elision) is compared too.
 *  Exceptions are recorded as simple class name + ':' + message. */
public final class StreamOps {
    private StreamOps() {
    }

    static int s;

    static int r(int n) {
        s = s * 1103515245 + 12345;
        return ((s >>> 8) & 0x7fffff) % n;
    }

    static StringBuilder log;

    static void ex(StringBuilder out, RuntimeException e) {
        out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
    }

    static List<Integer> randList(int max) {
        int n = r(max);
        List<Integer> l = new ArrayList<>();
        for (int i = 0; i < n; i++) l.add(r(12) - 2);
        return l;
    }

    // ------------------------------------------------------------------ reference pipelines

    static Stream<Integer> source(int depth) {
        List<Integer> l = randList(8);
        switch (r(20)) {
            case 0: return l.stream();
            case 1: return Stream.of(l.toArray(new Integer[0]));
            case 2: return Arrays.asList(l.toArray(new Integer[0])).stream();
            case 3: return new HashSet<>(l).stream();
            case 4: return new TreeSet<>(l).stream();
            case 5: return new LinkedHashSet<>(l).stream();
            case 6: { int lim = r(8); return Stream.iterate(r(5), x -> { log.append('n'); return x + 1 + (x & 1); }).limit(lim); }
            case 7: return Stream.iterate(r(5), x -> x < 12, x -> x + 2);
            case 8: { int[] c = { r(4) }; int lim = r(6); return Stream.generate(() -> c[0]++ * 3 % 7).limit(lim); }
            case 9: return IntStream.range(r(4), r(10)).boxed();
            case 10: if (depth < 1) return Stream.concat(source(depth + 1), source(depth + 1)); return l.stream();
            case 11: {
                Stream.Builder<Integer> b = Stream.builder();
                for (Integer x : l) b.add(x);
                return b.build();
            }
            case 12: return Stream.empty();
            case 13: return r(2) == 0 ? Stream.of(r(5)) : Stream.ofNullable(r(3) == 0 ? null : 7);
            case 14: {
                HashMap<Integer, Integer> m = new HashMap<>();
                for (Integer x : l) m.merge(x, 1, Integer::sum);
                int k = r(3);
                if (k == 0) return m.keySet().stream();
                if (k == 1) return m.values().stream();
                return m.entrySet().stream().map(e -> e.getKey() * 10 + e.getValue());
            }
            case 15: {
                TreeMap<Integer, Integer> m = new TreeMap<>(Comparator.reverseOrder());
                for (Integer x : l) m.put(x, x * x);
                int k = r(3);
                if (k == 0) return m.keySet().stream();
                if (k == 1) return m.values().stream();
                return m.entrySet().stream().map(Map.Entry::getValue);
            }
            case 16: return new ArrayDeque<>(l).stream();
            case 17: {
                LinkedHashMap<Integer, String> m = new LinkedHashMap<>();
                for (Integer x : l) m.put(x, "v" + x);
                return r(2) == 0 ? m.keySet().stream() : m.values().stream().map(String::length);
            }
            case 18: return Collections.unmodifiableList(l).stream();
            default: return Arrays.stream(l.toArray(new Integer[0]), 0, l.size() / 2);
        }
    }

    static Stream<Integer> inner(int x) {
        switch (r(5)) {
            case 0: return Stream.of(x, x + 100).peek(y -> log.append('i').append(y));
            case 1: return IntStream.range(0, Math.floorMod(x, 3)).boxed();
            case 2: return null;
            case 3: return Stream.iterate(x, y -> y + 1).limit(2).onClose(() -> log.append('c'));
            default: return Stream.empty();
        }
    }

    static Stream<Integer> op(Stream<Integer> st) {
        switch (r(20)) {
            case 0: return st.filter(x -> { log.append('f').append(x); return x % 2 == 0; });
            case 1: return st.map(x -> x * 3 - 1);
            case 2: return st.peek(x -> log.append('p').append(x));
            case 3: return st.distinct();
            case 4: return st.sorted();
            case 5: return st.sorted(Comparator.reverseOrder());
            case 6: return st.limit(r(6));
            case 7: return st.skip(r(4));
            case 8: return st.takeWhile(x -> { log.append('t'); return x < 7; });
            case 9: return st.dropWhile(x -> { log.append('d'); return x < 3; });
            case 10: return st.flatMap(x -> inner(x));
            case 11: return st.mapMulti((x, c) -> { if (x % 3 != 0) { c.accept(x); c.accept(-x); } });
            case 12: return st.mapToInt(x -> x * 2).boxed();
            case 13: return st.unordered();
            case 14: return st.sorted(Comparator.comparing((Integer x) -> Math.floorMod(x, 3)).thenComparing(Comparator.naturalOrder()));
            case 15: return st.onClose(() -> log.append('C'));
            case 16: return st.mapToLong(x -> x * 1000000007L).mapToObj(v -> (int) (v % 1000));
            case 17: return st.limit(r(3) + 1).peek(x -> log.append('q').append(x));
            case 18: return st.flatMapToInt(x -> IntStream.of(x, x / 2)).boxed();
            default: return st.skip(0);
        }
    }

    static String terminal(Stream<Integer> st) {
        switch (r(26)) {
            case 0: return String.valueOf(st.toList());
            case 1: return String.valueOf(st.collect(Collectors.toList()));
            case 2: return String.valueOf(st.count());
            case 3: st.forEach(x -> log.append('e').append(x)); return "fe";
            case 4: return String.valueOf(st.reduce(0, Integer::sum));
            case 5: return String.valueOf(st.reduce(Integer::max));
            case 6: return String.valueOf(st.reduce(0, (a, x) -> a * 2 + x, Integer::sum));
            case 7: return String.valueOf(st.min(Comparator.naturalOrder()));
            case 8: return String.valueOf(st.max(Comparator.comparing(x -> -x)));
            case 9: return String.valueOf(st.anyMatch(x -> { log.append('a'); return x > 5; }));
            case 10: return String.valueOf(st.allMatch(x -> { log.append('l'); return x < 9; }));
            case 11: return String.valueOf(st.noneMatch(x -> x == 4));
            case 12: return String.valueOf(st.findFirst());
            case 13: return String.valueOf(st.findAny());
            case 14: return Arrays.toString(st.toArray());
            case 15: return Arrays.toString(st.toArray(Integer[]::new));
            case 16: {
                Iterator<Integer> it = st.iterator();
                StringBuilder b = new StringBuilder("it");
                for (int i = 0; i < 3 && it.hasNext(); i++) b.append(it.next()).append(';');
                return b.toString();
            }
            case 17: return st.collect(StringBuilder::new, StringBuilder::append, StringBuilder::append).toString();
            case 18: return String.valueOf(st.collect(Collectors.groupingBy(x -> Math.floorMod(x, 3))));
            case 19: return st.map(String::valueOf).collect(Collectors.joining(",", "[", "]"));
            case 20: return String.valueOf(st.collect(Collectors.toSet()));
            case 21: return String.valueOf(st.collect(Collectors.partitioningBy(x -> x > 2, Collectors.counting())));
            case 22: return String.valueOf(st.collect(Collectors.toMap(x -> x, x -> 1, Integer::sum, TreeMap::new)));
            case 23: return String.valueOf(st.mapToInt(x -> x).sum());
            case 24: st.forEachOrdered(x -> log.append('o').append(x)); return "fo";
            default: {
                Iterator<Integer> it = st.iterator();
                StringBuilder b = new StringBuilder("all");
                it.forEachRemaining(x -> b.append(x).append(','));
                return b.append(it.hasNext()).toString();
            }
        }
    }

    /** Random reference pipelines: a source, up to 5 intermediate operations, a terminal one;
     *  sometimes a stage is reused (IllegalStateException) or the stream is closed. */
    public static String fuzz(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        log = out;
        for (int round = 0; round < 3; round++) {
            try {
                Stream<Integer> st = source(0);
                Stream<Integer> first = st;
                int n = r(6);
                List<Stream<Integer>> stages = new ArrayList<>();
                for (int i = 0; i < n; i++) {
                    stages.add(st);
                    st = op(st);
                }
                out.append('=').append(terminal(st));
                int k = r(6);
                if (k == 0) out.append(" again=").append(terminal(st));
                else if (k == 1 && !stages.isEmpty()) out.append(" up=").append(terminal(stages.get(r(stages.size()))));
                else if (k == 2) { st.close(); out.append(" closed"); }
                else if (k == 3) { first.close(); out.append(" fclosed"); st.close(); }
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append('|');
        }
        return out.toString();
    }

    // ------------------------------------------------------------------ primitive pipelines

    static IntStream intSource(int depth) {
        switch (r(12)) {
            case 0: return IntStream.range(r(5) - 2, r(10));
            case 1: return IntStream.rangeClosed(r(5), r(8));
            case 2: { int[] a = new int[r(7)]; for (int i = 0; i < a.length; i++) a[i] = r(9) - 3; return IntStream.of(a); }
            case 3: { int lim = r(7); return IntStream.iterate(r(4), x -> x * 2 + 1).limit(lim); }
            case 4: return IntStream.iterate(1, x -> x < 40, x -> x * 3);
            case 5: { int[] c = { 5 }; int lim = r(5); return IntStream.generate(() -> c[0]-- * c[0]).limit(lim); }
            case 6: { int[] a = new int[r(7) + 2]; for (int i = 0; i < a.length; i++) a[i] = r(20); return Arrays.stream(a, 1, a.length - 1); }
            case 7: if (depth < 1) return IntStream.concat(intSource(depth + 1), intSource(depth + 1)); return IntStream.of(r(9));
            case 8: { IntStream.Builder b = IntStream.builder(); int n = r(5); for (int i = 0; i < n; i++) b.add(r(7)); return b.build(); }
            case 9: return IntStream.empty();
            case 10: return randList(7).stream().mapToInt(Integer::intValue);
            default: return LongStream.range(0, r(6)).mapToInt(v -> (int) (v * v));
        }
    }

    static IntStream intOp(IntStream st) {
        switch (r(16)) {
            case 0: return st.filter(x -> { log.append('f'); return x % 3 != 1; });
            case 1: return st.map(x -> x * x - 4);
            case 2: return st.peek(x -> log.append('p').append(x));
            case 3: return st.distinct();
            case 4: return st.sorted();
            case 5: return st.limit(r(5));
            case 6: return st.skip(r(3));
            case 7: return st.takeWhile(x -> x < 10);
            case 8: return st.dropWhile(x -> x < 2);
            case 9: return st.flatMap(x -> IntStream.range(0, Math.floorMod(x, 3)).map(y -> x * 10 + y));
            case 10: return st.boxed().mapToInt(x -> x + 1);
            case 11: return st.asLongStream().map(v -> v * 3).mapToInt(v -> (int) v);
            case 12: return st.mapMulti((x, c) -> { c.accept(x); if (x > 3) c.accept(x - 3); });
            case 13: return st.mapToObj(x -> "s" + x).mapToInt(String::length);
            case 14: return st.unordered();
            default: return st.mapToLong(x -> (long) x << 33).mapToInt(v -> (int) (v >> 33));
        }
    }

    static String intTerminal(IntStream st) {
        switch (r(16)) {
            case 0: return String.valueOf(st.sum());
            case 1: return String.valueOf(st.count());
            case 2: return String.valueOf(st.min());
            case 3: return String.valueOf(st.max());
            case 4: { OptionalDouble a = st.average(); return a.isPresent() ? "avg" + (long) (a.getAsDouble() * 1000) : "noavg"; }
            case 5: return String.valueOf(st.reduce(7, (a, b) -> a * 31 + b));
            case 6: return String.valueOf(st.reduce((a, b) -> a - b));
            case 7: return Arrays.toString(st.toArray());
            case 8: return String.valueOf(st.findFirst());
            case 9: return String.valueOf(st.anyMatch(x -> { log.append('a'); return x > 4; }));
            case 10: return String.valueOf(st.allMatch(x -> x >= 0));
            case 11: return String.valueOf(st.noneMatch(x -> x == 2));
            case 12: { ArrayList<Integer> al = st.collect(ArrayList::new, ArrayList::add, ArrayList::addAll); return String.valueOf(al); }
            case 13: return String.valueOf(st.boxed().collect(Collectors.toList()));
            case 14: st.forEach(x -> log.append('e').append(x)); return "fe";
            default: return String.valueOf(st.findAny());
        }
    }

    static LongStream longSource() {
        switch (r(8)) {
            case 0: return LongStream.range(r(5) - 2, r(10));
            case 1: return LongStream.rangeClosed(r(5) + 4000000000L, 4000000000L + r(9));
            case 2: { long[] a = new long[r(6)]; for (int i = 0; i < a.length; i++) a[i] = (long) r(9) * 1000000000L; return LongStream.of(a); }
            case 3: { int lim = r(6); return LongStream.iterate(3, x -> x * x).limit(lim); }
            case 4: return LongStream.iterate(1, x -> x < 1000000, x -> x * 7);
            case 5: { LongStream.Builder b = LongStream.builder(); int n = r(4); for (int i = 0; i < n; i++) b.accept(r(5)); return b.build(); }
            case 6: return IntStream.range(0, r(6)).asLongStream();
            default: return LongStream.concat(LongStream.of(r(3)), LongStream.empty());
        }
    }

    static LongStream longOp(LongStream st) {
        switch (r(12)) {
            case 0: return st.filter(x -> x % 2 == 0);
            case 1: return st.map(x -> x * 5 - 1);
            case 2: return st.peek(x -> log.append('p').append(x));
            case 3: return st.distinct();
            case 4: return st.sorted();
            case 5: return st.limit(r(4));
            case 6: return st.skip(r(3));
            case 7: return st.takeWhile(x -> x < 5000000000L);
            case 8: return st.dropWhile(x -> x < 3);
            case 9: return st.flatMap(x -> LongStream.of(x, -x));
            case 10: return st.boxed().mapToLong(x -> x + 1);
            default: return st.mapToInt(x -> (int) (x % 1000)).asLongStream();
        }
    }

    static String longTerminal(LongStream st) {
        switch (r(10)) {
            case 0: return String.valueOf(st.sum());
            case 1: return String.valueOf(st.count());
            case 2: return String.valueOf(st.min());
            case 3: return String.valueOf(st.max());
            case 4: { OptionalDouble a = st.average(); return a.isPresent() ? "avg" + (long) (a.getAsDouble() * 10) : "noavg"; }
            case 5: return String.valueOf(st.reduce(1, (a, b) -> a * 3 + b));
            case 6: return Arrays.toString(st.toArray());
            case 7: return String.valueOf(st.findFirst());
            case 8: return String.valueOf(st.anyMatch(x -> x > 4));
            default: return String.valueOf(st.boxed().toList());
        }
    }

    /** Random IntStream and LongStream pipelines. */
    public static String ints(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        log = out;
        for (int round = 0; round < 4; round++) {
            try {
                if (round % 2 == 0) {
                    IntStream st = intSource(0);
                    int n = r(5);
                    for (int i = 0; i < n; i++) st = intOp(st);
                    out.append('=').append(intTerminal(st));
                    if (r(4) == 0) out.append(" again=").append(intTerminal(st));
                } else {
                    LongStream st = longSource();
                    int n = r(4);
                    for (int i = 0; i < n; i++) st = longOp(st);
                    out.append('=').append(longTerminal(st));
                    if (r(4) == 0) out.append(" again=").append(longTerminal(st));
                }
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append('|');
        }
        return out.toString();
    }

    // ------------------------------------------------------------------ collectors

    static final String[] WORDS = { "a", "bb", "ab", "ccc", "b", "abc", "bca", "dd", "a", "cab" };

    static Collector<? super String, ?, ?> downstream() {
        switch (r(12)) {
            case 0: return Collectors.toList();
            case 1: return Collectors.counting();
            case 2: return Collectors.joining("/");
            case 3: return Collectors.mapping(String::length, Collectors.toList());
            case 4: return Collectors.summingInt(String::length);
            case 5: return Collectors.minBy(Comparator.naturalOrder());
            case 6: return Collectors.toCollection(TreeSet::new);
            case 7: return Collectors.filtering(w -> w.length() > 1, Collectors.toList());
            case 8: return Collectors.reducing("", (a, b) -> a + b);
            case 9: return Collectors.collectingAndThen(Collectors.toList(), List::size);
            case 10: return Collectors.flatMapping(w -> Stream.of(w, w + w).limit(w.length() % 3), Collectors.toList());
            default: return Collectors.toSet();
        }
    }

    static Object collect(Stream<String> st) {
        switch (r(28)) {
            case 0: return st.collect(Collectors.groupingBy(String::length));
            case 1: return st.collect(Collectors.groupingBy(w -> w.charAt(0), TreeMap::new, downstream()));
            case 2: return st.collect(Collectors.groupingBy(w -> w.length() % 2, downstream()));
            case 3: return st.collect(Collectors.partitioningBy(w -> w.contains("a")));
            case 4: return st.collect(Collectors.partitioningBy(w -> w.length() > 1, downstream()));
            case 5: return st.collect(Collectors.toMap(w -> w, String::length));
            case 6: return st.collect(Collectors.toMap(String::length, w -> w, (a, b) -> a + "+" + b));
            case 7: return st.collect(Collectors.toMap(w -> w.charAt(0), w -> 1, Integer::sum, LinkedHashMap::new));
            case 8: return st.collect(Collectors.joining());
            case 9: return st.collect(Collectors.joining(", "));
            case 10: return st.collect(Collectors.joining("-", "{", "}"));
            case 11: return st.collect(Collectors.counting());
            case 12: return st.collect(Collectors.summingLong(w -> (long) w.hashCode()));
            case 13: return st.collect(Collectors.maxBy(Comparator.comparing(String::length)));
            case 14: return st.collect(Collectors.reducing((a, b) -> b + a));
            case 15: return st.collect(Collectors.reducing(0, String::length, Integer::sum));
            case 16: return st.collect(Collectors.teeing(Collectors.counting(), Collectors.joining(), (c, j) -> c + ":" + j));
            case 17: return st.collect(Collectors.toUnmodifiableList());
            case 18: return st.collect(Collectors.toCollection(ArrayDeque::new));
            case 19: return st.collect(Collectors.collectingAndThen(Collectors.joining(","), x -> "<" + x + ">"));
            case 20: return st.collect(Collectors.groupingBy(w -> w.length() == 3 ? null : w.length()));
            case 21: return st.collect(Collectors.toMap(w -> w, w -> w.length() > 2 ? null : w));
            case 22: return st.collect(Collectors.flatMapping(w -> Stream.of(w, w.toUpperCase()), Collectors.joining("")));
            case 23: return st.collect(Collector.of(StringBuilder::new, StringBuilder::append, StringBuilder::append, StringBuilder::length));
            case 24: return st.collect(Collector.of(ArrayList::new, ArrayList::add, (a, b) -> { a.addAll(b); return a; }, Collector.Characteristics.UNORDERED));
            case 25: return st.collect(Collectors.mapping(String::length, Collectors.groupingBy(n -> n, Collectors.counting())));
            case 26: return st.collect(Collectors.groupingBy(String::length, LinkedHashMap::new, Collectors.mapping(w -> w.charAt(0), Collectors.toList())));
            default: return st.collect(Collectors.filtering(w -> w.startsWith("a"), Collectors.toList()));
        }
    }

    /** Random collectors (nested downstream collectors) over word streams. */
    public static String collectors(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        log = out;
        for (int round = 0; round < 4; round++) {
            try {
                List<String> words = new ArrayList<>();
                int n = r(8);
                for (int i = 0; i < n; i++) words.add(WORDS[r(WORDS.length)]);
                Stream<String> st = r(3) == 0 ? words.stream().sorted() : words.stream();
                Object res = collect(st);
                out.append(res);
                if (res instanceof List && r(2) == 0) {
                    List<?> l = (List<?>) res;
                    try { out.append(" g").append(l.get(r(5))); } catch (RuntimeException e) { ex(out, e); }
                    try { out.append(" c").append(l.contains(null)); } catch (RuntimeException e) { ex(out, e); }
                    try { out.append(" i").append(l.indexOf("a")).append(l.lastIndexOf("a")); } catch (RuntimeException e) { ex(out, e); }
                    try { ((List<Object>) l).add("x"); out.append(" added"); } catch (RuntimeException e) { ex(out, e); }
                    out.append(" h").append(l.hashCode()).append(l.equals(new ArrayList<>(l)));
                }
                if (res instanceof Map && r(2) == 0) {
                    Map<?, ?> m = (Map<?, ?>) res;
                    out.append(" k").append(m.keySet()).append(" v").append(m.values()).append(" s").append(m.size());
                    out.append(" t").append(m.get(true)).append(m.containsKey(false)).append(m.get(1));
                }
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append('|');
        }
        return out.toString();
    }

    // ------------------------------------------------------------------ typical uses

    static final class Person {
        final String name;
        final int age;
        final String city;

        Person(String name, int age, String city) {
            this.name = name;
            this.age = age;
            this.city = city;
        }

        String getName() { return name; }
        int getAge() { return age; }
        String getCity() { return city; }
        public String toString() { return name + "(" + age + ")"; }
    }

    static List<Person> people() {
        return new ArrayList<>(Arrays.asList(new Person("ann", 31, "Oslo"), new Person("bob", 25, "Rome"),
            new Person("cid", 31, "Oslo"), new Person("dee", 19, "Lima"), new Person("eve", 25, "Rome"),
            new Person("fay", 44, "Oslo")));
    }

    static String common(int k, int seed) {
        StringBuilder out = log;
        List<Person> ps = people();
        switch (k) {
            case 0: return ps.stream().filter(p -> p.getAge() > 24).map(Person::getName).collect(Collectors.joining(","));
            case 1: return String.valueOf(ps.stream().collect(Collectors.groupingBy(Person::getCity, TreeMap::new, Collectors.counting())));
            case 2: return String.valueOf(ps.stream().sorted(Comparator.comparingInt(Person::getAge).thenComparing(Person::getName, Comparator.reverseOrder())).toList());
            case 3: return String.valueOf(ps.stream().mapToInt(Person::getAge).max().getAsInt() + ps.stream().mapToLong(Person::getAge).sum());
            case 4: return String.valueOf(ps.stream().collect(Collectors.toMap(Person::getName, Person::getAge)));
            case 5: return String.valueOf(ps.stream().map(Person::getCity).distinct().sorted().collect(Collectors.toList()));
            case 6: return String.valueOf(ps.stream().max(Comparator.comparingInt(Person::getAge)).map(Person::getName).orElse("none"));
            case 7: return String.valueOf(ps.stream().collect(Collectors.partitioningBy(p -> p.getAge() >= 30, Collectors.mapping(Person::getName, Collectors.toList()))));
            case 8: return String.valueOf(ps.stream().collect(Collectors.toMap(Person::getCity, Person::getName)));
            case 9: return String.valueOf(ps.stream().anyMatch(p -> p.getCity().equals("Lima")) + " " + ps.stream().allMatch(p -> p.getAge() > 18) + " " + ps.stream().noneMatch(p -> p.getName().isEmpty()));
            case 10: return String.valueOf(IntStream.rangeClosed(1, 5).mapToObj(i -> "#" + i).collect(Collectors.toList()));
            case 11: return String.valueOf(Stream.of("x", "yy", "zzz").collect(Collectors.toMap(Function.identity(), String::length, (a, b) -> a, LinkedHashMap::new)));
            case 12: return String.valueOf(ps.stream().map(Person::getAge).reduce(0, Integer::sum));
            case 13: return String.valueOf(Arrays.stream(new int[] { 4, 1, 3 }).map(x -> x * x).sorted().boxed().toList());
            case 14: return String.valueOf(Stream.of("b", "a", "c").sorted(Comparator.reverseOrder()).findFirst().get());
            case 15: return String.valueOf(ps.stream().collect(Collectors.groupingBy(Person::getAge, TreeMap::new, Collectors.mapping(Person::getName, Collectors.joining("+")))));
            case 16: return String.valueOf(ps.stream().map(Person::getName).filter(n -> n.startsWith("z")).findAny().isPresent());
            case 17: return String.valueOf(Stream.of(Arrays.asList(1, 2), Arrays.asList(3), new ArrayList<Integer>()).flatMap(List::stream).map(x -> x * 10).toList());
            case 18: return String.valueOf(ps.stream().skip(2).limit(3).map(Person::getName).toList());
            case 19: return String.valueOf(ps.stream().count() + IntStream.of(3, 4).count());
            case 20: {
                // count() of a SIZED pipeline does not run peek/map
                long c = Stream.of(1, 2, 3).peek(x -> out.append('P')).map(x -> { out.append('M'); return x; }).count();
                long d = Stream.of(1, 2, 3).filter(x -> { out.append('F'); return true; }).count();
                long e = ps.stream().peek(x -> out.append('Q')).skip(1).limit(3).sorted(Comparator.comparing(Person::getName)).count();
                long f = Stream.concat(Stream.of(1).peek(x -> out.append('R')), ps.stream()).count();
                return c + "," + d + "," + e + "," + f;
            }
            case 21: {
                // laziness and short-circuiting
                Optional<Integer> o = Stream.of(5, 6, 7, 8).peek(x -> out.append('a').append(x)).filter(x -> x % 2 == 0).peek(x -> out.append('b').append(x)).findFirst();
                Optional<Integer> o2 = Stream.of(3, 1, 2).peek(x -> out.append('u').append(x)).sorted().peek(x -> out.append('s').append(x)).findFirst();
                boolean m = Stream.of(1, 2, 3).flatMap(x -> Stream.of(x, x * 10).peek(y -> out.append('i').append(y))).anyMatch(x -> x == 10);
                return o + " " + o2 + " " + m;
            }
            case 22: {
                // stream linkage
                Stream<Integer> st = Stream.of(1, 2);
                Stream<Integer> m = st.map(x -> x);
                try { st.filter(x -> true); } catch (IllegalStateException e) { out.append(e.getMessage()); }
                m.close();
                try { m.count(); } catch (IllegalStateException e) { out.append('/').append(e.getMessage()); }
                Stream<Integer> a = Stream.of(1);
                Stream<Integer> b = a.peek(x -> { });
                a.close();
                try { b.count(); } catch (IllegalStateException e) { out.append('/').append(e.getMessage()); }
                Stream<Integer> c = Stream.of(9);
                out.append(c.skip(0) == c).append(c.sequential() == c).append(c.isParallel());
                return "linked";
            }
            case 23: {
                // close handlers: order, exceptions, concat
                Stream<Integer> st = Stream.of(1).onClose(() -> out.append("h1")).onClose(() -> out.append("h2"));
                st.close();
                st.close();
                Stream<Integer> x = Stream.of(1).onClose(() -> { throw new IllegalArgumentException("first"); }).onClose(() -> out.append("h3"));
                try { x.close(); } catch (IllegalArgumentException e) { out.append(e.getMessage()); }
                Stream<Integer> c = Stream.concat(Stream.of(1).onClose(() -> out.append("ca")), Stream.of(2).onClose(() -> out.append("cb")));
                try (Stream<Integer> cc = c.map(v -> v + 1)) { out.append(cc.toList()); }
                try { Stream.of(1).map(v -> v).onClose(null); } catch (NullPointerException e) { out.append("npe"); }
                return "closed";
            }
            case 24: {
                // argument checks
                try { Stream.of(1).limit(-1); } catch (IllegalArgumentException e) { out.append(e.getMessage()); }
                try { IntStream.of(1).skip(-3); } catch (IllegalArgumentException e) { out.append(e.getMessage()); }
                try { Stream.of(1).map(null); } catch (NullPointerException e) { out.append("npe" + e.getMessage()); }
                Stream<Integer> st = Stream.of(1);
                try { st.sorted(null); } catch (NullPointerException e) { out.append("npe2"); }
                try { st.count(); } catch (IllegalStateException e) { out.append(e.getMessage()); }
                try { Stream.of(1, 2).toArray(String[]::new); } catch (ArrayStoreException e) { out.append(e.getMessage()); }
                try { Stream.of(1, 2).toArray(n -> new Integer[n + 1]); } catch (IllegalStateException e) { out.append(e.getMessage()); }
                try { out.append(Stream.of(1, 2).filter(v -> true).toArray(n -> new Integer[n + 1]).length); } catch (RuntimeException e) { out.append(e.getMessage()); }
                try { Stream.of(1, 2).filter(v -> true).toArray(n -> new Integer[0]); } catch (IndexOutOfBoundsException e) { out.append(e.getMessage()); }
                try { Arrays.stream(new Integer[3], 2, 1); } catch (ArrayIndexOutOfBoundsException e) { out.append(e.getMessage()); }
                try { Arrays.stream(new int[3], -1, 1); } catch (ArrayIndexOutOfBoundsException e) { out.append(e.getMessage()); }
                try { Arrays.stream(new long[3], 0, 4); } catch (ArrayIndexOutOfBoundsException e) { out.append(e.getMessage()); }
                return "args";
            }
            case 25: {
                // builders and iterators
                Stream.Builder<String> b = Stream.builder();
                b.add("x").add("y").accept("z");
                Stream<String> st = b.build();
                try { b.add("w"); } catch (IllegalStateException e) { out.append("ise"); }
                try { b.build(); } catch (IllegalStateException e) { out.append("ise2"); }
                Iterator<String> it = st.iterator();
                out.append(it.next()).append(it.hasNext()).append(it.next()).append(it.next()).append(it.hasNext());
                try { it.next(); } catch (NoSuchElementException e) { out.append("nse"); }
                try { it.remove(); } catch (UnsupportedOperationException e) { out.append(e.getMessage()); }
                Iterator<Integer> i2 = Stream.of(4, 5, 6).filter(v -> { out.append('f'); return true; }).iterator();
                out.append(i2.hasNext()).append(i2.hasNext());
                i2.forEachRemaining(v -> out.append('e').append(v));
                return "built";
            }
            case 26: {
                // Stream.toList(): unmodifiable, nulls allowed
                List<Integer> l = Stream.of(1, null, 3).toList();
                out.append(l).append(l.contains(null)).append(l.indexOf(3)).append(l.hashCode()).append(l.equals(Arrays.asList(1, null, 3)));
                try { l.add(4); } catch (UnsupportedOperationException e) { out.append("uoe"); }
                try { l.set(0, 4); } catch (UnsupportedOperationException e) { out.append("uoe"); }
                try { l.get(5); } catch (IndexOutOfBoundsException e) { out.append(e.getClass().getSimpleName()).append(e.getMessage()); }
                try { Stream.<Integer>empty().toList().clear(); } catch (UnsupportedOperationException e) { out.append("uoe"); }
                List<Integer> u = Stream.of(1, 2).collect(Collectors.toUnmodifiableList());
                try { u.get(2); } catch (IndexOutOfBoundsException e) { out.append(e.getClass().getSimpleName()).append(e.getMessage()); }
                try { u.contains(null); } catch (NullPointerException e) { out.append("npe"); }
                try { Stream.of(1, null).collect(Collectors.toUnmodifiableList()); } catch (NullPointerException e) { out.append("npe2"); }
                out.append(Stream.of(7, 8).toList().stream().map(x -> x + 1).toList());
                return "lists";
            }
            case 27: {
                // Optional / OptionalInt / OptionalLong
                Optional<String> o = Optional.of("v");
                Optional<String> e = Optional.empty();
                out.append(o.map(String::toUpperCase)).append(o.filter(x -> x.isEmpty())).append(e.or(() -> Optional.of("w")));
                out.append(o.flatMap(x -> Optional.of(x + x)).get()).append(e.orElse("d")).append(e.orElseGet(() -> "g"));
                out.append(o.isPresent()).append(e.isEmpty()).append(o.equals(Optional.of("v"))).append(o.hashCode()).append(Optional.ofNullable((String) null) == e);
                o.ifPresent(x -> out.append("ip"));
                e.ifPresentOrElse(x -> out.append("no"), () -> out.append("else"));
                out.append(o.stream().count()).append(e.stream().count());
                try { e.get(); } catch (NoSuchElementException x) { out.append(x.getMessage()); }
                try { e.orElseThrow(); } catch (NoSuchElementException x) { out.append(x.getMessage()); }
                try { e.orElseThrow(() -> new IllegalStateException("custom")); } catch (IllegalStateException x) { out.append(x.getMessage()); }
                try { Optional.of(null); } catch (NullPointerException x) { out.append("npe"); }
                OptionalInt oi = OptionalInt.of(3);
                OptionalLong ol = OptionalLong.of(1L << 40);
                out.append(oi).append(oi.getAsInt()).append(OptionalInt.empty().orElse(9)).append(oi.equals(OptionalInt.of(3))).append(oi.hashCode());
                out.append(ol).append(ol.hashCode()).append(OptionalLong.empty()).append(OptionalLong.empty().isPresent());
                try { OptionalLong.empty().getAsLong(); } catch (NoSuchElementException x) { out.append(x.getMessage()); }
                out.append(oi.stream().sum()).append(OptionalInt.empty().stream().count()).append(OptionalInt.empty().equals(OptionalInt.empty()));
                return "opt";
            }
            case 28: {
                // StringJoiner
                StringJoiner j = new StringJoiner(", ", "{", "}");
                out.append(j).append(j.length());
                j.setEmptyValue("EMPTY");
                out.append(j).append(j.length());
                j.add("a").add(null).add("bc");
                out.append(j).append(j.length());
                StringJoiner k2 = new StringJoiner("-");
                k2.add("x").add("y");
                j.merge(k2);
                out.append(j);
                j.merge(new StringJoiner("+"));
                out.append(j).append(j.length());
                try { new StringJoiner(null); } catch (NullPointerException e) { out.append(e.getMessage()); }
                try { new StringJoiner(",", "[", null); } catch (NullPointerException e) { out.append(e.getMessage()); }
                try { j.setEmptyValue(null); } catch (NullPointerException e) { out.append(e.getMessage()); }
                StringJoiner self = new StringJoiner("|").add("p").add("q");
                self.merge(self);
                out.append(self);
                return "sj";
            }
            case 29: {
                // java.util.function default and static methods
                Function<Integer, Integer> f = x -> x + 1;
                Function<Integer, Integer> g = x -> x * 2;
                out.append(f.andThen(g).apply(3)).append(f.compose(g).apply(3)).append(Function.<Integer>identity().apply(7));
                Predicate<String> p = String::isEmpty;
                out.append(p.negate().test("")).append(p.and(x -> true).test("")).append(p.or(x -> x.length() > 2).test("abc"));
                out.append(Predicate.not(p).test("x")).append(Predicate.isEqual("q").test("q")).append(Predicate.isEqual(null).test(null));
                BiFunction<Integer, Integer, Integer> add = Integer::sum;
                out.append(add.andThen(x -> -x).apply(2, 3));
                BinaryOperator<String> mn = BinaryOperator.minBy(Comparator.comparing(String::length));
                out.append(mn.apply("aa", "b")).append(BinaryOperator.<String>maxBy(Comparator.naturalOrder()).apply("aa", "b"));
                Consumer<StringBuilder> c1 = sb -> sb.append('1');
                c1.andThen(sb -> sb.append('2')).accept(out);
                BiConsumer<StringBuilder, String> bc = StringBuilder::append;
                bc.andThen((sb, x) -> sb.append(x.length())).accept(out, "zz");
                BiPredicate<Integer, Integer> lt = (a, b2) -> a < b2;
                out.append(lt.negate().test(1, 2)).append(lt.and((a, b2) -> a > 0).test(1, 2)).append(lt.or((a, b2) -> true).test(3, 2));
                IntUnaryOperator iu = x -> x + 3;
                out.append(iu.andThen(x -> x * x).applyAsInt(1)).append(iu.compose(x -> x * x).applyAsInt(2)).append(IntUnaryOperator.identity().applyAsInt(5));
                LongUnaryOperator lu = x -> x - 1;
                out.append(lu.andThen(x -> x << 2).applyAsLong(3)).append(LongUnaryOperator.identity().applyAsLong(-4));
                IntPredicate ip = x -> x > 2;
                out.append(ip.negate().test(1)).append(ip.and(x -> x < 5).test(4)).append(ip.or(x -> x == 0).test(0));
                LongPredicate lp = x -> x != 0;
                out.append(lp.negate().test(0)).append(lp.and(x -> x > 0).test(-1));
                IntConsumer ic = x -> out.append('i').append(x);
                ic.andThen(x -> out.append('j')).accept(4);
                LongConsumer lc = x -> out.append('l').append(x);
                lc.andThen(x -> out.append('m')).accept(5);
                out.append(UnaryOperator.<String>identity().apply("u"));
                try { f.andThen(null); } catch (NullPointerException e) { out.append("npe"); }
                try { p.and(null); } catch (NullPointerException e) { out.append("npe"); }
                try { Predicate.not(null); } catch (NullPointerException e) { out.append("npe"); }
                return "fn";
            }
            case 30: {
                // collections as sources
                TreeSet<String> ts = new TreeSet<>(Arrays.asList("q", "a", "m"));
                HashMap<String, Integer> hm = new HashMap<>();
                hm.put("one", 1); hm.put("two", 2); hm.put("three", 3);
                LinkedHashMap<String, Integer> lm = new LinkedHashMap<>(hm);
                lm.put("zero", 0);
                out.append(ts.stream().map(String::toUpperCase).toList());
                out.append(hm.entrySet().stream().filter(e -> e.getValue() > 1).map(Map.Entry::getKey).sorted().toList());
                out.append(lm.values().stream().mapToInt(Integer::intValue).sum());
                out.append(lm.keySet().stream().collect(Collectors.joining("")));
                out.append(Collections.unmodifiableMap(hm).entrySet().stream().map(e -> e.getKey().length()).toList());
                out.append(Collections.singletonList(5).stream().count()).append(Collections.emptySet().stream().findFirst());
                out.append(new ArrayDeque<>(Arrays.asList(3, 2, 1)).stream().map(x -> x * x).toList());
                out.append(ts.stream().sorted().distinct().count()).append(ts.stream().unordered().findFirst());
                out.append(new TreeMap<>(hm).keySet().stream().toList()).append(new TreeMap<>(hm).values().stream().toList());
                List<Integer> al = new ArrayList<>(Arrays.asList(1, 2, 3));
                Stream<Integer> late = al.stream();
                al.add(4);
                out.append(late.toList());
                return "colls";
            }
            case 31: {
                // IntStream / LongStream specifics
                out.append(IntStream.range(0, 5).average().getAsDouble() == 2.0).append(IntStream.empty().average().isPresent());
                out.append(IntStream.of(5, 2, 8).max()).append(IntStream.of(5, 2, 8).min().getAsInt()).append(IntStream.rangeClosed(3, 3).count());
                out.append(Arrays.toString(IntStream.iterate(1, x -> x <= 100, x -> x * 4).toArray()));
                out.append(LongStream.rangeClosed(1, 5).map(x -> x * x).sum()).append(LongStream.of(4, 9).boxed().toList());
                out.append(IntStream.range(0, 3).mapToObj(i -> "x" + i).collect(Collectors.joining()));
                out.append(IntStream.of(3, 3, 1, 3).distinct().boxed().toList()).append(IntStream.range(0, 4).boxed().distinct().count());
                out.append(Stream.of("a", "bb").flatMapToInt(w -> IntStream.of(w.length(), w.charAt(0))).sum()).append(Stream.of(2, 3).mapToLong(x -> 1L << (x * 20)).sum());
                out.append(Stream.of("ab", "c").mapMultiToInt((w, c) -> { for (int i = 0; i < w.length(); i++) c.accept(w.charAt(i)); }).boxed().toList());
                out.append(IntStream.range(Integer.MAX_VALUE - 2, Integer.MAX_VALUE).count()).append(IntStream.rangeClosed(Integer.MAX_VALUE - 1, Integer.MAX_VALUE).sum());
                out.append(LongStream.range(0, 3000000000L).count()).append(LongStream.range(2999999990L, 3000000000L).skip(8).sum()).append(LongStream.range(0, 3000000000L).limit(3).sum());
                StringBuilder isb = IntStream.of(1, 2, 3).collect(StringBuilder::new, StringBuilder::append, StringBuilder::append);
                out.append(isb.toString());
                IntStream is = IntStream.of(1);
                out.append(is.unordered() == is).append(IntStream.empty().unordered().count());
                return "prims";
            }
            case 32: {
                // concat / flatMap closing and laziness
                Stream<Integer> a = Stream.of(1, 2).onClose(() -> out.append("A"));
                Stream<Integer> b = Stream.of(3).onClose(() -> out.append("B"));
                Stream<Integer> c = Stream.concat(a, b);
                try { a.count(); } catch (IllegalStateException e) { out.append("ise"); }
                out.append(c.filter(x -> x > 1).toList());
                c.close();
                out.append(Stream.of(1, 2, 3).flatMap(x -> Stream.of(x).onClose(() -> out.append("c" + x))).limit(2).toList());
                out.append(Stream.of(1, 2).flatMap(x -> Stream.iterate(x, y -> y + 10)).limit(3).toList());
                out.append(Stream.of(3, 1, 2).sorted().iterator().next());
                Iterator<Integer> it = Stream.of(1, 2).flatMap(x -> Stream.of(x, -x).peek(y -> out.append('k').append(y))).iterator();
                out.append(it.next());
                out.append(Stream.iterate(1, x -> x + 1).takeWhile(x -> x < 4).dropWhile(x -> x < 2).toList());
                return "concat";
            }
            default: {
                // collectors with custom functions
                Collector<String, ?, String> rev = Collector.of(StringBuilder::new, (sb, x) -> sb.append(x).append('.'), (l, r2) -> r2.append(l), StringBuilder::toString);
                out.append(Stream.of("a", "b", "c").collect(rev));
                out.append(rev.characteristics()).append(Collectors.toList().characteristics()).append(Collectors.toSet().characteristics());
                out.append(Collectors.joining().characteristics().isEmpty()).append(Collectors.collectingAndThen(Collectors.toSet(), Set::size).characteristics());
                String tee = Stream.of(1, 2, 3, 4).collect(Collectors.teeing(Collectors.summingInt(x -> x), Collectors.counting(), (sum, n) -> sum + "/" + n));
                out.append(tee);
                out.append(Stream.of("x", "y").collect(Collectors.toMap(x -> x, x -> 1, (p, q) -> p + q, TreeMap::new)).firstKey());
                out.append(Stream.of(1, 2, 1).collect(Collectors.groupingBy(x -> x, Collectors.reducing(0, Integer::sum))));
                out.append(Stream.<String>empty().collect(Collectors.maxBy(Comparator.naturalOrder())));
                Map<Boolean, List<Integer>> pm = Stream.of(1, 2, 3).collect(Collectors.partitioningBy(x -> x > 1));
                out.append(pm.get(true)).append(pm.get("x")).append(pm.containsValue(Arrays.asList(1))).append(pm.entrySet()).append(pm.hashCode());
                try { pm.put(true, null); } catch (UnsupportedOperationException e) { out.append("uoe"); }
                return "custom";
            }
        }
    }

    static final int COMMON = 34;

    /** Typical uses, one scenario per input (plus a few more for coverage). */
    public static String common(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        log = out;
        int k = Math.floorMod(seed, COMMON);
        for (int i = 0; i < 2; i++) {
            try {
                out.append(common(k, seed));
            } catch (RuntimeException e) {
                ex(out, e);
            }
            out.append('|');
            k = r(COMMON);
        }
        return out.toString();
    }
}

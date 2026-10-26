package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of PriorityQueue (heap order as seen by iteration/toString/toArray,
 *  comparators with ties, iterator removal, fail-fast iteration, constructors, bulk removal,
 *  type and null errors) and BitSet (single bits and ranges, searches, logical operations,
 *  size/length growth, conversions, index-check messages). Exceptions are printed as class
 *  simple name ':' message. */
public final class PqOps {
    private PqOps() {
    }

    static final class Log {
        final StringBuilder sb = new StringBuilder();
        int s;

        Log(int seed) {
            s = seed;
        }

        int r(int n) {
            s = s * 1103515245 + 12345;
            return ((s >>> 8) & 0x7fffff) % n;
        }

        boolean b() {
            return r(2) == 0;
        }

        void a(Object o) {
            sb.append(o).append(';');
        }

        void e(Throwable t) {
            sb.append('!').append(t.getClass().getSimpleName()).append(':').append(t.getMessage()).append(';');
        }
    }

    /** An element ordered by a key with ties (equals by identity): exposes the heap algorithm. */
    static final class Job implements Comparable<Job> {
        final int pri;
        final int id;

        Job(int pri, int id) {
            this.pri = pri;
            this.id = id;
        }

        public int compareTo(Job o) {
            if (o == null) throw new IllegalStateException("null job");
            return Integer.compare(pri, o.pri);
        }

        public String toString() {
            return pri + "#" + id;
        }
    }

    static int cmpRev(Object a, Object b) {
        if (!(a instanceof Integer) || !(b instanceof Integer)) throw new IllegalStateException("cmpRev");
        return Integer.compare((Integer) b, (Integer) a);
    }

    static int cmpMod(Object a, Object b) {
        if (!(a instanceof Integer) || !(b instanceof Integer)) throw new IllegalStateException("cmpMod");
        return Integer.compare(Math.floorMod((Integer) a, 5), Math.floorMod((Integer) b, 5));
    }

    /** 0: natural Integer, 1: reverse comparator, 2: natural String, 3: comparator mod 5 (ties),
     *  4: Comparable with ties (Job). */
    static Object elem(Log t, int mode, int[] ids) {
        int x = t.r(100);
        if (x == 0) return null;
        if (x == 1 && mode != 4) return mode == 2 ? (Object) 7 : "str";
        if (x == 2 && (mode == 0 || mode == 2 || mode == 4)) return new Object();   // natural: never stored
        switch (mode) {
            case 2: return "e" + t.r(30);
            case 4: return new Job(t.r(8), ids[0]++);
            default: return t.r(60) - 10;
        }
    }

    static PriorityQueue<Object> make(Log t, int mode, List<Object> init) {
        Comparator<Object> c = mode == 1 ? PqOps::cmpRev : mode == 3 ? PqOps::cmpMod : null;
        switch (t.r(6)) {
            case 0: return c == null ? new PriorityQueue<>() : new PriorityQueue<>(c);
            case 1: return new PriorityQueue<>(1 + t.r(3), c);
            case 2: if (c == null) return new PriorityQueue<>(init); break;
            case 3: {
                PriorityQueue<Object> q = new PriorityQueue<>(c);
                for (Object o : init) if (o != null) q.offer(o);
                return new PriorityQueue<>(q);
            }
            case 4: {
                if (c == null && mode != 4) {
                    TreeSet<Object> ts = new TreeSet<>();
                    for (Object o : init) if (o != null) ts.add(o);
                    return new PriorityQueue<>((Collection<Object>) ts);
                }
                break;
            }
            default: break;
        }
        PriorityQueue<Object> q = new PriorityQueue<>(c);
        q.addAll(init);
        return q;
    }

    static String drain(PriorityQueue<Object> q) {
        PriorityQueue<Object> c = new PriorityQueue<>(q);
        StringBuilder b = new StringBuilder("(");
        Object x;
        while ((x = c.poll()) != null) b.append(x).append(' ');
        return b.append(')').toString();
    }

    public static String pq(int seed) {
        Log t = new Log(seed);
        int mode = t.r(5);
        int[] ids = {0};
        List<Object> init = new ArrayList<>();
        for (int i = t.r(14); i > 0; i--) init.add(elem(t, mode, ids));
        PriorityQueue<Object> q;
        try {
            q = make(t, mode, init);
        } catch (RuntimeException ex) {
            t.e(ex);
            init.removeIf(o -> !(o instanceof Integer || o instanceof String || o instanceof Job));
            if (mode == 2) init.removeIf(o -> !(o instanceof String));
            else init.removeIf(o -> o instanceof String);
            q = make(t, mode, init);
        }
        t.a(q);
        int n = 20 + t.r(60);
        for (int i = 0; i < n; i++) {
            Object x = elem(t, mode, ids);
            try {
                switch (t.r(26)) {
                    case 0: case 1: case 2: case 3: t.a(q.offer(x) + "" + q); break;
                    case 4: t.a(q.add(x)); break;
                    case 5: case 6: t.a(q.poll()); break;
                    case 7: t.a(q.peek() + "," + q.size()); break;
                    case 8: t.a(q.element()); break;
                    case 9: t.a(q.remove()); break;
                    case 10: t.a(q.remove(x) + "," + q.contains(x) + "," + q); break;
                    case 11: {
                        Object y = q.peek();
                        t.a(q.remove(y) + "," + q);
                        break;
                    }
                    case 12: t.a(Arrays.toString(q.toArray()) + Arrays.toString(q.toArray(new Object[t.r(4)]))); break;
                    case 13: {
                        Iterator<Object> it = q.iterator();
                        StringBuilder b = new StringBuilder();
                        while (it.hasNext()) {
                            Object y = it.next();
                            b.append(y).append(' ');
                            if (t.r(3) == 0) {
                                it.remove();
                                if (t.r(6) == 0) it.remove();   // IllegalStateException
                            }
                        }
                        t.a(b + "" + q);
                        break;
                    }
                    case 14: {
                        Iterator<Object> it = q.iterator();
                        if (it.hasNext()) {
                            it.next();
                            if (t.b()) q.offer(x); else q.poll();
                            t.a(it.hasNext());
                            it.next();
                        }
                        break;
                    }
                    case 15: t.a(q.removeIf(y -> String.valueOf(y).length() % 3 == 0) + "," + q); break;
                    case 16: t.a(q.removeAll(Arrays.asList(x, q.peek())) + "," + q.retainAll(new ArrayList<>(init)) + "," + q); break;
                    case 17: {
                        StringBuilder b = new StringBuilder();
                        q.forEach(y -> b.append(y).append(','));
                        t.a(b);
                        break;
                    }
                    case 18: t.a(drain(q)); break;
                    case 19: if (t.r(5) == 0) { q.clear(); t.a(q + "" + q.isEmpty()); } else t.a(q.size()); break;
                    case 20: t.a(q.addAll(Arrays.asList(x, elem(t, mode, ids))) + "," + q); break;
                    case 21: t.a(q.addAll(q)); break;
                    case 22: {
                        PriorityQueue<Object> c = new PriorityQueue<>(q);
                        c.offer(x);
                        t.a(c + "/" + q + "/" + (c.comparator() == q.comparator()));
                        break;
                    }
                    case 23: t.a(new PriorityQueue<>(t.r(3) - 1)); break;
                    case 24: t.a(q.containsAll(Arrays.asList(x)) + "," + q.isEmpty()); break;
                    default: {
                        Iterator<Object> it = q.iterator();
                        try {
                            for (;;) it.next();
                        } catch (NoSuchElementException ex) {
                            t.e(ex);
                        }
                        break;
                    }
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(q);
        t.a(drain(q));
        return t.sb.toString();
    }

    static String str(long[] a) {
        StringBuilder b = new StringBuilder("[");
        for (long x : a) b.append(x).append(' ');
        return b.append(']').toString();
    }

    static String str(byte[] a) {
        StringBuilder b = new StringBuilder("[");
        for (byte x : a) b.append(x).append(' ');
        return b.append(']').toString();
    }

    static int idx(Log t) {
        int x = t.r(40);
        if (x == 0) return -1 - t.r(3);
        if (x < 4) return 60 + t.r(10);
        if (x < 6) return 120 + t.r(20);
        if (x == 6) return 300 + t.r(400);
        return t.r(80);
    }

    public static String bitset(int seed) {
        Log t = new Log(seed);
        BitSet a;
        try {
            a = t.b() ? new BitSet() : new BitSet(t.r(200) - 5);
        } catch (RuntimeException ex) {
            t.e(ex);
            a = new BitSet(t.r(10));
        }
        BitSet b = new BitSet(t.r(130));
        int n = 20 + t.r(60);
        for (int i = 0; i < n; i++) {
            BitSet w = t.r(4) == 0 ? b : a;
            int x = idx(t), y = idx(t);
            try {
                switch (t.r(30)) {
                    case 0: case 1: case 2: w.set(x); t.a(w); break;
                    case 3: w.set(x, y); t.a(w); break;
                    case 4: w.set(x, t.b()); t.a(w.cardinality()); break;
                    case 5: w.set(x, y, t.b()); t.a(w); break;
                    case 6: w.clear(x); t.a(w); break;
                    case 7: w.clear(x, y); t.a(w); break;
                    case 8: w.flip(x); t.a(w); break;
                    case 9: w.flip(x, y); t.a(w); break;
                    case 10: t.a(w.get(x)); break;
                    case 11: t.a(w.get(x, y) + "/" + w.get(x, y).size() + "/" + w.get(x, y).length()); break;
                    case 12: t.a(w.nextSetBit(x) + "," + w.nextClearBit(x) + "," + w.previousSetBit(x) + "," + w.previousClearBit(x)); break;
                    case 13: t.a(w.length() + "," + w.size() + "," + w.cardinality() + "," + w.isEmpty()); break;
                    case 14: { BitSet c = (BitSet) a.clone(); c.and(b); t.a(c + "/" + c.size()); break; }
                    case 15: a.or(b); t.a(a + "/" + a.size()); break;
                    case 16: a.xor(b); t.a(a + "/" + a.size()); break;
                    case 17: b.andNot(a); t.a(b); break;
                    case 18: t.a(a.intersects(b) + "," + a.equals(b) + "," + a.hashCode() + "," + b.hashCode()); break;
                    case 19: t.a(str(w.toLongArray()) + str(w.toByteArray())); break;
                    case 20: { BitSet c = BitSet.valueOf(w.toLongArray()); t.a(c.equals(w) + "," + c.size() + "," + BitSet.valueOf(w.toByteArray()).equals(w)); break; }
                    case 21: { BitSet c = (BitSet) w.clone(); c.set(x); t.a(c.size() + "," + w.size() + "," + c.equals(w)); break; }
                    case 22: { BitSet c = BitSet.valueOf(new long[] {t.r(1000) - 500L, 0, t.b() ? 0 : -1L << t.r(64)}); t.a(c + "/" + c.length() + "/" + c.size()); break; }
                    case 23: { BitSet c = BitSet.valueOf(new byte[] {(byte) t.r(256), 0, (byte) (t.r(256) - 128), (byte) t.r(2)}); t.a(c + "/" + str(c.toByteArray())); break; }
                    case 24: { w.and(w); w.or(w); t.a(w); w.xor(w); t.a(w + "/" + w.isEmpty()); break; }
                    case 25: { BitSet c = null; if (t.b()) w.and(c); else if (t.b()) w.or(c); else w.intersects(c); break; }
                    case 26: { if (t.r(4) == 0) w.clear(); t.a(w.size()); break; }
                    case 27: { int k = 0; StringBuilder sb = new StringBuilder(); for (int j = w.nextSetBit(0); j >= 0 && k < 40; j = w.nextSetBit(j + 1), k++) sb.append(j).append(' '); t.a(sb); break; }
                    case 28: t.a(new BitSet(x).size()); break;
                    default: { int k = 0; StringBuilder sb = new StringBuilder(); for (int j = w.length(); (j = w.previousSetBit(j - 1)) >= 0 && k < 40; k++) sb.append(j).append(' '); t.a(sb); break; }
                }
            } catch (RuntimeException ex) {
                t.e(ex);
            }
        }
        t.a(a);
        t.a(b);
        return t.sb.toString();
    }

    /** Typical uses: a task scheduler, top-k, merging sorted runs, a sieve with BitSet. */
    public static String common(int seed) {
        Log t = new Log(seed);
        StringBuilder out = new StringBuilder();
        PriorityQueue<int[]> tasks = new PriorityQueue<>((p, q) -> p[0] != q[0] ? Integer.compare(p[0], q[0]) : Integer.compare(q[1], p[1]));
        for (int i = 0; i < 15; i++) tasks.add(new int[] {t.r(5), i});
        while (!tasks.isEmpty()) {
            int[] x = tasks.poll();
            out.append(x[0]).append(':').append(x[1]).append(' ');
        }
        PriorityQueue<Integer> top = new PriorityQueue<>();
        for (int i = 0; i < 30; i++) {
            top.offer(t.r(1000));
            if (top.size() > 5) top.poll();
        }
        out.append(top).append(top.peek()).append('|');
        PriorityQueue<String> words = new PriorityQueue<>(Comparator.comparing(String::length).thenComparing(Comparator.reverseOrder()));
        words.addAll(Arrays.asList("delta", "alpha", "be", "gamma", "pi", "omega", "chi", "x"));
        out.append(words).append(words.poll()).append(words.poll()).append(words).append('|');
        PriorityQueue<Integer> pq = new PriorityQueue<>(Collections.reverseOrder());
        for (int i = 0; i < 12; i++) pq.add(t.r(40));
        Iterator<Integer> it = pq.iterator();
        while (it.hasNext()) if (it.next() % 2 == 0) it.remove();
        out.append(pq).append(pq.size()).append('|');
        int limit = 100 + t.r(100);
        BitSet composite = new BitSet(limit + 1);
        composite.set(0, 2);
        for (int p = 2; p * p <= limit; p = composite.nextClearBit(p + 1)) {
            for (int m = p * p; m <= limit; m += p) composite.set(m);
        }
        BitSet primes = (BitSet) composite.clone();
        primes.flip(0, limit + 1);
        out.append(primes.cardinality()).append(primes).append(primes.length()).append(primes.size()).append(composite.size());
        BitSet even = new BitSet();
        for (int i = 0; i < 64; i += 2) even.set(i);
        BitSet x = (BitSet) primes.clone();
        x.and(even);
        out.append(x).append(str(even.toLongArray())).append(even.hashCode());
        return out.toString();
    }
}

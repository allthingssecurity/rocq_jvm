// ConcurrentHashMap (classes/jdkmodel) under the thread layer (classes/threadmodel): results that
// do not depend on the schedule. Keys are small Integers, so the iteration order is the slot order.
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicInteger;

public class ChmThreads {
    static int small(int n) { return Math.floorMod(n, 20); }

    /** merge(k, 1, sum) from three threads on a few keys: every increment counted. */
    public static String mergeCounts(int n) throws Exception {
        int k = 3 + small(n);
        ConcurrentHashMap<Integer, Integer> m = new ConcurrentHashMap<>();
        Runnable r = () -> { for (int i = 0; i < k; i++) m.merge(i % 5, 1, Integer::sum); };
        Thread a = new Thread(r), b = new Thread(r);
        a.start(); b.start(); r.run(); a.join(); b.join();
        return m.toString() + " " + m.size();
    }

    /** computeIfAbsent from two threads: the function runs once per key. */
    public static String computeOnce(int n) throws Exception {
        int k = 2 + small(n);
        ConcurrentHashMap<Integer, Integer> m = new ConcurrentHashMap<>();
        AtomicInteger calls = new AtomicInteger();
        Runnable r = () -> { for (int i = 0; i < k; i++) m.computeIfAbsent(i, x -> { calls.incrementAndGet(); return x * 10; }); };
        Thread a = new Thread(r);
        a.start(); r.run(); a.join();
        return calls.get() + " " + m;
    }

    /** putIfAbsent from three threads: exactly one winner per key. */
    public static int putIfAbsentWinners(int n) throws Exception {
        int k = 1 + small(n);
        ConcurrentHashMap<Integer, Integer> m = new ConcurrentHashMap<>();
        AtomicInteger wins = new AtomicInteger();
        Thread[] ts = new Thread[3];
        for (int t = 0; t < 3; t++) {
            int id = t;
            ts[t] = new Thread(() -> { for (int i = 0; i < k; i++) if (m.putIfAbsent(i, id) == null) wins.incrementAndGet(); });
            ts[t].start();
        }
        for (Thread t : ts) t.join();
        return wins.get() * 100 + m.size();
    }

    /** Two threads insert disjoint keys while the table resizes several times. */
    public static String resizeRace(int n) throws Exception {
        int k = 10 + small(n) * 2;
        ConcurrentHashMap<Integer, Integer> m = new ConcurrentHashMap<>(2);
        Thread a = new Thread(() -> { for (int i = 0; i < k; i++) m.put(2 * i, i); });
        a.start();
        for (int i = 0; i < k; i++) m.put(2 * i + 1, -i);
        a.join();
        int sum = 0;
        for (int v : m.values()) sum += v;
        return m.size() + " " + sum + " " + m.keySet();
    }

    /** CAS loop with replace(k, old, new) from two threads. */
    public static int replaceLoop(int n) throws Exception {
        int k = 1 + small(n);
        ConcurrentHashMap<String, Integer> m = new ConcurrentHashMap<>();
        m.put("c", 0);
        Runnable r = () -> { for (int i = 0; i < k; i++) { Integer v; do { v = m.get("c"); } while (!m.replace("c", v, v + 1)); } };
        Thread a = new Thread(r);
        a.start(); r.run(); a.join();
        return m.get("c");
    }

    /** A reader iterates while a writer inserts and removes: no exception, only keys that were
     *  ever in the map, each at most once. */
    public static String iterateWhileWriting(int n) throws Exception {
        int k = 5 + small(n);
        ConcurrentHashMap<Integer, Integer> m = new ConcurrentHashMap<>();
        for (int i = 0; i < 4; i++) m.put(100 + i, i);
        Thread w = new Thread(() -> { for (int i = 0; i < k; i++) { m.put(i, i); if (i % 3 == 0) m.remove(100 + (i % 4)); } });
        w.start();
        Set<Integer> seen = new HashSet<>();
        boolean ok = true;
        for (Integer x : m.keySet()) {
            if (!seen.add(x)) ok = false;
            if (!((x >= 0 && x < k) || (x >= 100 && x < 104))) ok = false;
        }
        w.join();
        return ok + " " + m.size();
    }

    /** compute() increments from two threads on keys of one bin (lists then a tree). */
    public static String computeSameBin(int n) throws Exception {
        int k = 4 + small(n);
        ConcurrentHashMap<Integer, Integer> m = new ConcurrentHashMap<>(64);
        Runnable r = () -> { for (int i = 0; i < k; i++) m.compute((i % 10) * 128, (x, v) -> v == null ? 1 : v + 1); };
        Thread a = new Thread(r);
        a.start(); r.run(); a.join();
        int sum = 0;
        for (int v : m.values()) sum += v;
        return sum + " " + m.size();
    }
}

// CopyOnWriteArrayList/Set and ConcurrentLinkedQueue/Deque (classes/jdkmodel) under the thread
// layer (classes/threadmodel): results that do not depend on the schedule.
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicInteger;

public class CowThreads {
    static int small(int n) { return Math.floorMod(n, 6); }

    /** Three threads add to a COW list; an iterator snapshot taken first stays unchanged. */
    public static String cowAdds(int n) throws Exception {
        int k = 2 + small(n);
        CopyOnWriteArrayList<Integer> l = new CopyOnWriteArrayList<>(Arrays.asList(-1, -2));
        Iterator<Integer> snap = l.iterator();
        Thread[] ts = new Thread[3];
        for (int t = 0; t < 3; t++) {
            int id = t;
            ts[t] = new Thread(() -> { for (int i = 0; i < k; i++) l.add(id * 100 + i); });
            ts[t].start();
        }
        for (Thread t : ts) t.join();
        int c = 0;
        while (snap.hasNext()) { snap.next(); c++; }
        List<Integer> sorted = new ArrayList<>(l);
        Collections.sort(sorted);
        return c + " " + l.size() + " " + sorted;
    }

    /** addIfAbsent from three threads on overlapping values: each value once. */
    public static String cowAbsent(int n) throws Exception {
        int k = 2 + small(n);
        CopyOnWriteArraySet<Integer> st = new CopyOnWriteArraySet<>();
        AtomicInteger wins = new AtomicInteger();
        Runnable r = () -> { for (int i = 0; i < k; i++) if (st.add(i)) wins.incrementAndGet(); };
        Thread a = new Thread(r), b = new Thread(r);
        a.start(); b.start(); r.run(); a.join(); b.join();
        List<Integer> sorted = new ArrayList<>(st);
        Collections.sort(sorted);
        return wins.get() + " " + sorted;
    }

    /** Two producers, two consumers on a ConcurrentLinkedQueue: every element consumed once. */
    public static String clqProdCons(int n) throws Exception {
        int k = 2 + small(n);
        ConcurrentLinkedQueue<Integer> q = new ConcurrentLinkedQueue<>();
        ConcurrentLinkedQueue<Integer> got = new ConcurrentLinkedQueue<>();
        AtomicInteger done = new AtomicInteger();
        Runnable prod = () -> { for (int i = 0; i < k; i++) q.offer(i); done.incrementAndGet(); };
        Runnable cons = () -> {
            while (true) {
                Integer x = q.poll();
                if (x != null) got.add(x);
                else if (done.get() == 2 && q.isEmpty()) return;
                else Thread.yield();
            }
        };
        Thread p1 = new Thread(prod), p2 = new Thread(prod), c1 = new Thread(cons), c2 = new Thread(cons);
        p1.start(); p2.start(); c1.start(); c2.start();
        p1.join(); p2.join(); c1.join(); c2.join();
        List<Integer> sorted = new ArrayList<>(got);
        Collections.sort(sorted);
        return sorted + " " + q.size();
    }

    /** Work stealing on a ConcurrentLinkedDeque: owner pops from the head, thief from the tail. */
    public static String cldSteal(int n) throws Exception {
        int k = 3 + small(n);
        ConcurrentLinkedDeque<Integer> d = new ConcurrentLinkedDeque<>();
        for (int i = 0; i < k; i++) d.addLast(i);
        AtomicInteger sum = new AtomicInteger(), cnt = new AtomicInteger();
        Thread thief = new Thread(() -> { Integer x; while ((x = d.pollLast()) != null) { sum.addAndGet(x); cnt.incrementAndGet(); } });
        thief.start();
        Integer x;
        while ((x = d.pollFirst()) != null) { sum.addAndGet(x); cnt.incrementAndGet(); }
        thief.join();
        return cnt.get() + " " + sum.get() + " " + d.isEmpty();
    }
}

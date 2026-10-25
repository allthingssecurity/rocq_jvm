// CompletableFuture (+ CompletionStage, CompletionException, the default async executor, the
// delayer) and StampedLock models under the thread layer. Results do not depend on the schedule:
// single-threaded parts check the JDK's exact order of dependent actions; multi-threaded parts
// use latches so that the thread that runs an action is determined, and check only values.
// Thread names are read only for threads the test names itself.
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;
import java.util.concurrent.locks.*;

public class CfTests {
    static int small(int n) { return Math.floorMod(n, 10); }

    static ThreadFactory named(String prefix) {
        AtomicInteger k = new AtomicInteger();
        return r -> new Thread(r, prefix + k.incrementAndGet());
    }

    static String ex(Throwable t) {
        if (t == null) return "null";
        return t.getClass().getName() + "(" + t.getMessage() + ")";
    }

    /** supplyAsync on a pool, then thenApply / thenCompose / thenCombine / thenAccept / thenRun. */
    public static String chain(int n) throws Exception {
        int k = small(n);
        ExecutorService es = Executors.newFixedThreadPool(2, named("w"));
        CompletableFuture<Integer> a = CompletableFuture.supplyAsync(() -> k * 3, es);
        CompletableFuture<Integer> b = CompletableFuture.supplyAsync(() -> k + 100, es);
        CompletableFuture<String> c = a.thenApply(x -> x + 1)
            .thenCompose(x -> CompletableFuture.supplyAsync(() -> "v" + x, es))
            .thenCombine(b, (s, y) -> s + "/" + y);
        AtomicInteger acc = new AtomicInteger();
        CompletableFuture<Void> d = c.thenAccept(s -> acc.addAndGet(s.length()));
        CompletableFuture<Void> e = d.thenRun(() -> acc.addAndGet(1000));
        String r = c.join() + " " + c.get() + " " + e.get(1, TimeUnit.MINUTES) + " " + acc.get() + " " + e.isDone()
            + " " + CompletableFuture.runAsync(() -> acc.incrementAndGet(), es).thenApplyAsync(v -> acc.get(), es).join();
        es.shutdown();
        return r + " " + es.awaitTermination(1, TimeUnit.MINUTES);
    }

    /** Exception wrapping: completeExceptionally keeps the exception, actions' exceptions are wrapped. */
    public static String errors(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        ExecutorService es = Executors.newSingleThreadExecutor(named("e"));
        int k = small(n);
        CompletableFuture<Integer> f = CompletableFuture.supplyAsync(() -> { if (k >= 0) throw new IllegalStateException("bad" + k); return 1; }, es);
        try { f.join(); } catch (CompletionException e) { b.append("J ").append(ex(e)).append(' ').append(ex(e.getCause())).append(' '); }
        try { f.get(); } catch (ExecutionException e) { b.append("G ").append(ex(e)).append(' ').append(ex(e.getCause())).append(' '); }
        b.append(f.isCompletedExceptionally()).append(f.isCancelled()).append(f.isDone()).append(' ');
        b.append(f.exceptionally(t -> { b.append("X ").append(ex(t)).append(' '); return -1; }).join()).append(' ');
        b.append(f.handle((v, t) -> v + " " + (t instanceof CompletionException) + " " + ex(t.getCause())).join()).append(' ');
        CompletableFuture<Integer> g = new CompletableFuture<>();
        CompletableFuture<Integer> g1 = g.thenApply(x -> x + 1);
        CompletableFuture<Integer> g2 = g.whenComplete((v, t) -> b.append("W ").append(v).append(' ').append(ex(t)).append(' '));
        b.append(g.completeExceptionally(new ArithmeticException("ar" + k))).append(g.completeExceptionally(new RuntimeException())).append(' ');
        try { g.join(); } catch (CompletionException e) { b.append("gJ ").append(ex(e)).append(' ').append(ex(e.getCause())).append(' '); }
        try { g.get(); } catch (ExecutionException e) { b.append("gG ").append(ex(e)).append(' '); }
        try { g1.join(); } catch (CompletionException e) { b.append("g1J ").append(ex(e)).append(' '); }
        try { g2.getNow(7); } catch (CompletionException e) { b.append("g2N ").append(ex(e)).append(' '); }
        b.append(g.exceptionally(t -> { b.append("gX ").append(ex(t)).append(' '); return 0; }).join()).append(' ');
        b.append(g1.exceptionally(t -> { b.append("g1X ").append(ex(t)).append(' '); return 0; }).join()).append(' ');
        // the action itself throws
        CompletableFuture<Integer> h = CompletableFuture.completedFuture(k).thenApply(x -> 10 / (x - x));
        try { h.join(); } catch (CompletionException e) { b.append("hJ ").append(ex(e)).append(' '); }
        CompletableFuture<Object> ff = CompletableFuture.failedFuture(new CompletionException("pre", new IllegalArgumentException("ia")));
        try { ff.join(); } catch (CompletionException e) { b.append("ffJ ").append(ex(e)).append(' ').append(ex(e.getCause())).append(' '); }
        try { ff.get(); } catch (ExecutionException e) { b.append("ffG ").append(ex(e)).append(' '); }
        try { ff.thenRun(() -> { }).join(); } catch (CompletionException e) { b.append("ffR ").append(ex(e)).append(' '); }
        // whenComplete whose action throws on a normal source
        CompletableFuture<Integer> w = CompletableFuture.completedFuture(1).whenComplete((v, t) -> { throw new UnsupportedOperationException("wc"); });
        try { w.join(); } catch (CompletionException e) { b.append("wJ ").append(ex(e)).append(' '); }
        try { CompletableFuture.completedFuture(1).thenApply(null); } catch (NullPointerException e) { b.append("npe "); }
        try { new CompletableFuture<Integer>().completeExceptionally(null); } catch (NullPointerException e) { b.append("npe2 "); }
        es.shutdown();
        es.awaitTermination(1, TimeUnit.MINUTES);
        return b.toString();
    }

    /** The JDK's order of several dependents of one future, nested dependents included (one thread). */
    public static String order(int n) {
        StringBuilder log = new StringBuilder();
        int k = 1 + small(n) % 4;
        CompletableFuture<Integer> f = new CompletableFuture<>();
        List<CompletableFuture<Integer>> deps = new ArrayList<>();
        for (int i = 0; i < k; i++) {
            int id = i;
            CompletableFuture<Integer> d = f.thenApply(x -> { log.append("a").append(id); return x + id; });
            deps.add(d);
            for (int j = 0; j <= (id + n) % 3; j++) {
                int jd = j;
                d.thenAccept(x -> log.append("b").append(id).append(jd));
            }
            if (id % 2 == 1) d.thenRun(() -> log.append("r").append(id)).thenRun(() -> log.append("s").append(id));
        }
        f.whenComplete((v, t) -> log.append("w"));
        CompletableFuture<Integer> other = new CompletableFuture<>();
        f.thenCombine(other, (x, y) -> { log.append("c"); return x * y; }).thenAccept(z -> log.append("C").append(z));
        f.applyToEither(other, x -> { log.append("e"); return x; });
        log.append("|");
        f.complete(5);
        log.append("|");
        other.complete(3);
        log.append("|");
        f.thenRun(() -> log.append("late"));
        int sum = 0;
        for (CompletableFuture<Integer> d : deps) sum += d.join();
        return log + " " + sum;
    }

    /** Order with dependents on both sources of thenCombine / either, allOf trees and anyOf. */
    public static String order2(int n) {
        StringBuilder log = new StringBuilder();
        int k = 2 + small(n) % 4;
        List<CompletableFuture<Integer>> fs = new ArrayList<>();
        for (int i = 0; i < k; i++) fs.add(new CompletableFuture<>());
        CompletableFuture<?>[] arr = fs.toArray(new CompletableFuture<?>[0]);
        CompletableFuture<Void> all = CompletableFuture.allOf(arr);
        CompletableFuture<Object> any = CompletableFuture.anyOf(arr);
        all.thenRun(() -> log.append("ALL"));
        any.thenAccept(v -> log.append("ANY").append(v));
        for (int i = 0; i < k; i++) {
            int id = i;
            fs.get(i).thenAccept(v -> log.append("d").append(id));
            if (i > 0) fs.get(i).thenAcceptBoth(fs.get(i - 1), (x, y) -> log.append("B").append(id));
            if (i > 0) fs.get(i - 1).acceptEither(fs.get(i), x -> log.append("E").append(id));
            if (i > 0) fs.get(i).runAfterBoth(fs.get(i - 1), () -> log.append("R").append(id));
            if (i > 0) fs.get(i).runAfterEither(fs.get(i - 1), () -> log.append("Q").append(id));
        }
        int start = Math.floorMod(n, k);
        for (int j = 0; j < k; j++) {
            int i = (start + j * (n % 2 == 0 ? 1 : k - 1)) % k;
            log.append('[').append(i);
            if (j == k - 1 && (n & 4) != 0) fs.get(i).completeExceptionally(new IllegalStateException("x" + i));
            else fs.get(i).complete(i * 10);
            log.append(']');
        }
        String a;
        try { all.join(); a = "ok"; } catch (CompletionException e) { a = ex(e); }
        return log + " " + a + " " + any.join() + " " + all.isCompletedExceptionally()
            + " " + CompletableFuture.allOf().isDone() + CompletableFuture.anyOf().isDone();
    }

    /** cancel: the future is cancelled, its dependents complete with a CompletionException. */
    public static String cancel(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        CompletableFuture<String> f = new CompletableFuture<>();
        CompletableFuture<String> d = f.thenApply(s -> s + "!");
        CompletableFuture<String> h = f.handle((s, t) -> s + " " + ex(t));
        b.append(f.cancel(small(n) % 2 == 0)).append(f.cancel(true)).append(f.complete("x")).append(' ');
        b.append(f.isCancelled()).append(f.isDone()).append(f.isCompletedExceptionally()).append(' ');
        b.append(d.isCancelled()).append(d.isCompletedExceptionally()).append(' ');
        try { f.join(); } catch (CancellationException e) { b.append("fJ ").append(ex(e)).append(' '); }
        try { f.get(); } catch (CancellationException e) { b.append("fG ").append(ex(e)).append(' '); }
        try { f.getNow("n"); } catch (CancellationException e) { b.append("fN "); }
        try { d.join(); } catch (CompletionException e) { b.append("dJ ").append(ex(e)).append(' ').append(ex(e.getCause())).append(' '); }
        try { d.get(); } catch (ExecutionException e) { b.append("dG ").append(ex(e)).append(' '); }
        b.append(h.join()).append(' ');
        CompletableFuture<Integer> done = CompletableFuture.completedFuture(1);
        b.append(done.cancel(true)).append(done.isCancelled()).append(' ');
        b.append(new CompletableFuture<Integer>().getNow(small(n)));
        return b.toString();
    }

    /** obtrude*, completedFuture, copy, minimal stages, completeAsync, toCompletableFuture. */
    public static String misc(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        int k = small(n);
        CompletableFuture<Integer> f = CompletableFuture.completedFuture(k);
        CompletableFuture<Integer> c = f.copy();
        b.append(c.join()).append(c == f).append(f.toCompletableFuture() == f).append(' ');
        f.obtrudeValue(k + 1);
        b.append(f.join()).append(c.join()).append(f.complete(3)).append(' ');
        f.obtrudeException(new IllegalStateException("ob"));
        try { f.join(); } catch (CompletionException e) { b.append(ex(e)).append(' '); }
        CompletableFuture<Integer> g = new CompletableFuture<>();
        CompletableFuture<Integer> gc = g.copy();
        CompletionStage<Integer> m = g.minimalCompletionStage();
        CompletableFuture<Integer> mt = m.toCompletableFuture();
        CompletionStage<Integer> m2 = m.thenApply(x -> x * 2);
        try { ((CompletableFuture<Integer>) m).complete(1); } catch (UnsupportedOperationException e) { b.append("uoe "); }
        try { ((CompletableFuture<Integer>) m2).join(); } catch (UnsupportedOperationException e) { b.append("uoe2 "); }
        try { ((CompletableFuture<Integer>) m2).isDone(); } catch (UnsupportedOperationException e) { b.append("uoe3 "); }
        g.complete(k * 7);
        b.append(gc.join()).append(' ').append(mt.join()).append(' ').append(m2.toCompletableFuture().join()).append(' ');
        b.append(CompletableFuture.completedStage("cs").toCompletableFuture().join()).append(' ');
        try { CompletableFuture.failedStage(new IllegalStateException("fs")).toCompletableFuture().join(); }
        catch (CompletionException e) { b.append(ex(e)).append(' '); }
        CompletableFuture<Object> nul = CompletableFuture.completedFuture(null);
        b.append(nul.join()).append(nul.getNow("x")).append(nul.isCompletedExceptionally()).append(' ');
        ExecutorService es = Executors.newSingleThreadExecutor(named("m"));
        CompletableFuture<String> ca = new CompletableFuture<String>().completeAsync(() -> Thread.currentThread().getName(), es);
        b.append(ca.get()).append(' ');
        CompletableFuture<Integer> ex1 = CompletableFuture.<Integer>failedFuture(new IllegalStateException("e1"))
            .exceptionallyCompose(t -> CompletableFuture.completedFuture(42));
        CompletableFuture<Integer> ex2 = CompletableFuture.<Integer>failedFuture(new IllegalStateException("e2"))
            .exceptionallyAsync(t -> 43, es);
        CompletableFuture<Integer> ex3 = CompletableFuture.completedFuture(44).exceptionallyComposeAsync(t -> null, es);
        b.append(ex1.join()).append(ex2.join()).append(ex3.join());
        es.shutdown();
        es.awaitTermination(1, TimeUnit.MINUTES);
        return b.toString();
    }

    /** The default async executor: values only (the thread's identity is host-dependent). */
    public static String asyncDefault(int n) throws Exception {
        int k = small(n);
        Thread main = Thread.currentThread();
        CompletableFuture<Integer> a = CompletableFuture.supplyAsync(() -> k * k);
        CompletableFuture<Boolean> other = CompletableFuture.supplyAsync(() -> Thread.currentThread() != main);
        CompletableFuture<Integer> b = a.thenApplyAsync(x -> x + 1);
        CompletableFuture<Void> r = CompletableFuture.runAsync(() -> { });
        CompletableFuture<String> c = b.thenCombineAsync(other, (x, y) -> x + ":" + y);
        CompletableFuture<Integer> d = CompletableFuture.supplyAsync(() -> { throw new IllegalArgumentException("ia" + k); });
        String de;
        try { d.join(); de = "no"; } catch (CompletionException e) { de = ex(e); }
        return c.get() + " " + r.join() + " " + de + " " + a.thenAcceptAsync(x -> { }).thenApply(v -> "t").join();
    }

    /** Which thread runs an action: the completing one, or the caller if already complete; async on the executor. */
    public static String threads(int n) throws Exception {
        ExecutorService es = Executors.newFixedThreadPool(1, named("p"));
        ExecutorService es2 = Executors.newFixedThreadPool(1, named("q"));
        CountDownLatch gate = new CountDownLatch(1), done = new CountDownLatch(3);
        List<String> log = Collections.synchronizedList(new ArrayList<>());
        CompletableFuture<Integer> f = CompletableFuture.supplyAsync(() -> {
            try { gate.await(); } catch (InterruptedException e) { }
            return small(n);
        }, es);
        // the async one first: it is fired last, so its task finds no other dependent to run
        f.thenRunAsync(() -> { log.add("B@" + Thread.currentThread().getName()); done.countDown(); }, es2);
        f.thenRun(() -> { log.add("A@" + Thread.currentThread().getName()); done.countDown(); });
        f.thenApply(x -> x + 1).thenAccept(x -> { log.add("C" + x + "@" + Thread.currentThread().getName()); done.countDown(); });
        gate.countDown();
        done.await();
        List<String> sorted = new ArrayList<>(log);
        Collections.sort(sorted);
        Thread main = Thread.currentThread();
        boolean late = f.thenApply(x -> Thread.currentThread() == main).join();
        String lateAsync = f.thenApplyAsync(x -> Thread.currentThread().getName(), es2).join();
        CompletableFuture<Integer> direct = f.thenApplyAsync(x -> x * 2, Runnable::run);
        es.shutdown(); es2.shutdown();
        return sorted + " " + late + " " + lateAsync + " " + direct.join() + " " + es.awaitTermination(1, TimeUnit.MINUTES)
            + es2.awaitTermination(1, TimeUnit.MINUTES);
    }

    /** Several waiters; interrupting get() and join(); get with a timeout. */
    public static String waiters(int n) throws Exception {
        int k = 1 + small(n) % 3;
        CompletableFuture<Integer> f = new CompletableFuture<>();
        AtomicInteger sum = new AtomicInteger();
        CountDownLatch started = new CountDownLatch(k);
        Thread[] ts = new Thread[k];
        for (int i = 0; i < k; i++) {
            ts[i] = new Thread(() -> { started.countDown(); sum.addAndGet(f.join()); });
            ts[i].start();
        }
        started.await();
        String to;
        try { f.get(20, TimeUnit.MILLISECONDS); to = "no"; } catch (TimeoutException e) { to = ex(e); }
        AtomicReference<String> intr = new AtomicReference<>();
        Thread getter = new Thread(() -> {
            try { f.get(); intr.set("value"); } catch (InterruptedException e) { intr.set("IE " + Thread.currentThread().isInterrupted()); }
            catch (ExecutionException e) { intr.set("EE"); }
        });
        getter.start();
        AtomicReference<String> jr = new AtomicReference<>();
        CountDownLatch jStarted = new CountDownLatch(1);
        Thread joiner = new Thread(() -> { jStarted.countDown(); int v = f.join(); jr.set(v + " " + Thread.currentThread().isInterrupted()); });
        joiner.start();
        jStarted.await();
        Thread.sleep(50);
        getter.interrupt();
        getter.join();
        joiner.interrupt();
        Thread.sleep(50);
        f.complete(5);
        for (Thread t : ts) t.join();
        joiner.join();
        Thread.currentThread().interrupt();
        String pre;
        try { new CompletableFuture<Integer>().get(); pre = "no"; } catch (InterruptedException e) { pre = "IE" + Thread.currentThread().isInterrupted(); }
        Thread.currentThread().interrupt();
        int quick = f.get();   // complete: no interrupt check
        boolean still = Thread.interrupted();
        return sum.get() + " " + to + " " + intr.get() + " " + jr.get() + " " + pre + " " + quick + still
            + " " + f.get(1, TimeUnit.MILLISECONDS);
    }

    /** orTimeout / completeOnTimeout / delayedExecutor (the delayer thread). */
    public static String timeouts(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        CompletableFuture<Integer> never = new CompletableFuture<>();
        CompletableFuture<Integer> t1 = never.orTimeout(50, TimeUnit.MILLISECONDS);
        b.append(t1 == never).append(' ');
        CompletableFuture<String> dep = never.thenApply(x -> "x");
        try { t1.join(); } catch (CompletionException e) { b.append(ex(e)).append(' ').append(ex(e.getCause())).append(' '); }
        try { never.get(); } catch (ExecutionException e) { b.append(ex(e)).append(' '); }
        try { dep.join(); } catch (CompletionException e) { b.append(ex(e)).append(' '); }
        CompletableFuture<Integer> c2 = new CompletableFuture<Integer>().completeOnTimeout(small(n), 30, TimeUnit.MILLISECONDS);
        b.append(c2.join()).append(' ');
        CompletableFuture<String> ok = new CompletableFuture<String>().orTimeout(5, TimeUnit.SECONDS);
        Thread main = Thread.currentThread();
        CompletableFuture<String> okDep = ok.thenApply(s -> s + "!" + (Thread.currentThread() == main));
        ok.complete("fast");
        b.append(okDep.join()).append(' ');
        CompletableFuture<String> where = new CompletableFuture<String>().completeOnTimeout("late", 20, TimeUnit.MILLISECONDS);
        b.append(where.thenApply(s -> s).join()).append(' ');
        AtomicReference<String> who = new AtomicReference<>();
        CompletableFuture<Integer> slow = new CompletableFuture<>();
        CompletableFuture<Integer> whoDep = slow.whenComplete((v, t) -> who.set(Thread.currentThread().getName() + " " + Thread.currentThread().isDaemon() + " " + ex(t)));
        slow.orTimeout(10, TimeUnit.MILLISECONDS);
        try { whoDep.join(); } catch (CompletionException e) { b.append(who.get()).append(' '); }
        ExecutorService es = Executors.newSingleThreadExecutor(named("d"));
        long t0 = System.nanoTime();
        CompletableFuture<String> delayed = CompletableFuture.supplyAsync(() -> Thread.currentThread().getName(),
            CompletableFuture.delayedExecutor(100, TimeUnit.MILLISECONDS, es));
        String dn = delayed.join();
        long el = (System.nanoTime() - t0) / 1000000L;
        b.append(dn).append(' ').append(el >= 100 && el < 5000);
        try { CompletableFuture.delayedExecutor(1, null); } catch (NullPointerException e) { b.append(" npe"); }
        String gt;
        try { new CompletableFuture<Integer>().get(0, TimeUnit.SECONDS); gt = "no"; } catch (TimeoutException e) { gt = "TE"; }
        es.shutdown();
        es.awaitTermination(1, TimeUnit.MINUTES);
        return b + " " + gt;
    }

    /** Rejected async tasks: the dependent completes exceptionally; supplyAsync throws. */
    public static String rejected(int n) {
        StringBuilder b = new StringBuilder();
        Executor no = r -> { throw new RejectedExecutionException("no" + small(n)); };
        CompletableFuture<Integer> f = CompletableFuture.completedFuture(1);
        CompletableFuture<Integer> a = f.thenApplyAsync(x -> x + 1, no);
        try { a.join(); } catch (CompletionException e) { b.append(ex(e)).append(' ').append(ex(e.getCause())).append(' '); }
        CompletableFuture<Integer> g = new CompletableFuture<>();
        CompletableFuture<Integer> ga = g.thenApplyAsync(x -> x + 1, no);
        g.complete(2);
        try { ga.join(); } catch (CompletionException e) { b.append(ex(e)).append(' '); }
        try { CompletableFuture.supplyAsync(() -> 1, no); } catch (RejectedExecutionException e) { b.append("thrown ").append(ex(e)).append(' '); }
        try { CompletableFuture.supplyAsync(() -> 1, null); } catch (NullPointerException e) { b.append("npe "); }
        // an exceptional source completes an async dependent without the executor
        CompletableFuture<Integer> bad = CompletableFuture.failedFuture(new IllegalStateException("s"));
        CompletableFuture<Integer> bd = bad.thenApplyAsync(x -> x, no);
        try { bd.join(); } catch (CompletionException e) { b.append(ex(e)).append(' '); }
        AtomicInteger seen = new AtomicInteger();
        Executor counting = r -> { seen.incrementAndGet(); b.append(r instanceof CompletableFuture.AsynchronousCompletionTask).append(' '); r.run(); };
        b.append(f.thenApplyAsync(x -> x * 5, counting).join()).append(' ').append(seen.get());
        return b.toString();
    }

    // ---- StampedLock ----

    /** Stamp values, validation, conversions, bad stamps, views, reader overflow. */
    public static String stamps(int n) throws Exception {
        StringBuilder b = new StringBuilder();
        StampedLock l = new StampedLock();
        long o = l.tryOptimisticRead();
        long w = l.writeLock();
        b.append(o).append(' ').append(w).append(' ').append(l.validate(o)).append(l.isWriteLocked()).append(l.tryOptimisticRead()).append(' ');
        b.append(l.tryReadLock()).append(l.tryWriteLock()).append(' ');
        try { l.unlockRead(w); } catch (IllegalMonitorStateException e) { b.append("imse1 "); }
        try { l.unlockWrite(w + 1); } catch (IllegalMonitorStateException e) { b.append("imse2 "); }
        l.unlockWrite(w);
        b.append(l.validate(o)).append(' ');
        try { l.unlockWrite(w); } catch (IllegalMonitorStateException e) { b.append("imse3 "); }
        int k = 1 + small(n);
        long[] rs = new long[k];
        for (int i = 0; i < k; i++) rs[i] = l.readLock();
        b.append(Arrays.toString(rs)).append(' ').append(l.getReadLockCount()).append(l.isReadLocked()).append(' ');
        long o2 = l.tryOptimisticRead();
        b.append(o2).append(l.validate(o2)).append(l.tryConvertToWriteLock(rs[0])).append(' ');
        for (int i = 1; i < k; i++) l.unlockRead(rs[i]);
        long cw = l.tryConvertToWriteLock(rs[0]);
        b.append(cw).append(StampedLock.isWriteLockStamp(cw)).append(l.validate(o2)).append(' ');
        long cr = l.tryConvertToReadLock(cw);
        b.append(cr).append(StampedLock.isReadLockStamp(cr)).append(' ');
        long co = l.tryConvertToOptimisticRead(cr);
        b.append(co).append(StampedLock.isOptimisticReadStamp(co)).append(l.isReadLocked()).append(' ');
        long ow = l.tryConvertToWriteLock(co);
        b.append(ow).append(l.tryConvertToOptimisticRead(ow)).append(l.tryConvertToReadLock(l.tryOptimisticRead())).append(' ');
        b.append(l.tryUnlockRead()).append(l.tryUnlockRead()).append(l.tryUnlockWrite()).append(' ');
        try { l.unlock(0L); } catch (IllegalMonitorStateException e) { b.append("imse4 "); }
        b.append(StampedLock.isLockStamp(0)).append(StampedLock.isOptimisticReadStamp(0)).append(' ');
        // reader overflow beyond 126 holds
        int many = 120 + small(n);
        long last = 0;
        for (int i = 0; i < many; i++) last = (n & 1) == 0 ? l.tryReadLock() : l.readLock();
        b.append(last).append(' ').append(l.getReadLockCount()).append(' ');
        for (int i = 0; i < many; i++) l.tryUnlockRead();
        b.append(l.getReadLockCount()).append(l.isReadLocked()).append(' ');
        // views
        Lock rl = l.asReadLock(), wl = l.asWriteLock();
        ReadWriteLock rw = l.asReadWriteLock();
        b.append(rl == l.asReadLock()).append(rw.readLock() == rl).append(rw.writeLock() == wl).append(' ');
        wl.lock();
        b.append(rl.tryLock()).append(l.isWriteLocked()).append(' ');
        wl.unlock();
        try { wl.unlock(); } catch (IllegalMonitorStateException e) { b.append("imse5 "); }
        rl.lock(); rl.lock();
        b.append(l.getReadLockCount()).append(wl.tryLock()).append(wl.tryLock(1, TimeUnit.MILLISECONDS)).append(' ');
        rl.unlock(); rl.unlock();
        try { rl.unlock(); } catch (IllegalMonitorStateException e) { b.append("imse6 "); }
        try { rl.newCondition(); } catch (UnsupportedOperationException e) { b.append("uoe "); }
        b.append(l.tryOptimisticRead());
        return b.toString();
    }

    /** Blocking: writers exclude readers, queued threads acquire in order, timeouts, interrupts. */
    public static String stampThreads(int n) throws Exception {
        StampedLock l = new StampedLock();
        List<String> order = Collections.synchronizedList(new ArrayList<>());
        long w = l.writeLock();
        int k = 2 + small(n) % 3;
        Thread[] ts = new Thread[k];
        for (int i = 0; i < k; i++) {
            String name = "t" + i;
            boolean writer = (i + n) % 2 == 0;
            ts[i] = new Thread(() -> {
                if (writer) { long s = l.writeLock(); order.add("W" + name); l.unlockWrite(s); }
                else { long s = l.readLock(); order.add("R" + name); l.unlockRead(s); }
            });
            ts[i].start();
            Thread.sleep(50);   // queue in this order
        }
        long tr = l.tryReadLock(20, TimeUnit.MILLISECONDS);
        long tw = l.tryWriteLock(20, TimeUnit.MILLISECONDS);
        AtomicReference<String> ir = new AtomicReference<>();
        Thread intr = new Thread(() -> {
            try { l.writeLockInterruptibly(); ir.set("got"); } catch (InterruptedException e) { ir.set("IE " + Thread.currentThread().isInterrupted()); }
        });
        intr.start();
        Thread.sleep(50);
        intr.interrupt();
        intr.join();
        l.unlockWrite(w);
        for (Thread t : ts) t.join();
        // readers share: two readers hold together while a writer waits
        long r1 = l.readLock();
        CountDownLatch in = new CountDownLatch(1);
        AtomicLong r2 = new AtomicLong();
        Thread rd = new Thread(() -> { r2.set(l.readLock()); in.countDown(); });
        rd.start();
        in.await();
        int both = l.getReadLockCount();
        Thread wr = new Thread(() -> { long s = l.writeLock(); order.add("late" + l.isWriteLocked()); l.unlockWrite(s); });
        wr.start();
        Thread.sleep(50);
        long tr2 = l.tryReadLock(10, TimeUnit.MILLISECONDS);   // a writer is queued: waits behind it, times out
        long tr3 = l.tryReadLock();                            // barges
        l.unlockRead(r1);
        l.unlockRead(r2.get());
        l.unlockRead(tr3);
        rd.join();
        wr.join();
        Thread.currentThread().interrupt();
        String ie;
        try { l.readLockInterruptibly(); ie = "no"; } catch (InterruptedException e) { ie = "IE"; }
        return order + " " + tr + " " + tw + " " + ir.get() + " " + both + " " + tr2 + " " + (tr3 != 0) + " " + ie
            + " " + l.isReadLocked() + l.isWriteLocked() + " " + l.tryOptimisticRead();
    }

    /** thenCompose with incomplete inner stages, exceptionallyCompose, handle/whenComplete chains (one thread). */
    public static String order3(int n) {
        StringBuilder log = new StringBuilder();
        int k = small(n);
        CompletableFuture<Integer> src = new CompletableFuture<>();
        CompletableFuture<Integer> inner = new CompletableFuture<>();
        CompletableFuture<Integer> comp = src.thenCompose(x -> { log.append("C"); return inner; });
        comp.thenAccept(x -> log.append("c").append(x));
        comp.whenComplete((x, t) -> log.append("w"));
        CompletableFuture<Integer> ec = src.thenApply(x -> { if ((x & 1) == 0) throw new IllegalStateException("odd"); return x; })
            .exceptionallyCompose(t -> { log.append("X"); return inner.thenApply(y -> -y); });
        ec.thenRun(() -> log.append("e"));
        src.handle((x, t) -> { log.append("h"); return x; }).thenAccept(x -> log.append("H"));
        CompletableFuture<Integer> cp = src.copy();
        cp.thenRun(() -> log.append("p"));
        inner.thenRun(() -> log.append("i"));
        log.append('|');
        src.complete(k);
        log.append('|');
        inner.complete(k * 10 + 1);
        log.append('|');
        src.obtrudeValue(k + 1);
        cp.obtrudeValue(0);
        log.append('|');
        return log + " " + comp.join() + " " + ec.join() + " " + cp.join() + " " + src.join();
    }

    /** Readers queued behind a writer share a group; a writer queued after them waits for both. */
    public static String stampQueue(int n) throws Exception {
        StampedLock l = new StampedLock();
        List<String> order = Collections.synchronizedList(new ArrayList<>());
        long w = l.writeLock();
        int readers = 1 + small(n) % 3;
        List<Thread> ts = new ArrayList<>();
        for (int i = 0; i < readers; i++) {
            Thread t = new Thread(() -> { long s = l.readLock(); order.add("R"); try { Thread.sleep(30); } catch (InterruptedException e) { } l.unlockRead(s); });
            ts.add(t); t.start(); Thread.sleep(40);
        }
        Thread w2 = new Thread(() -> { long s = l.writeLock(); order.add("W@" + order.size()); l.unlockWrite(s); });
        ts.add(w2); w2.start(); Thread.sleep(40);
        Thread r3 = new Thread(() -> { long s = l.readLock(); order.add("R3@" + order.size()); l.unlockRead(s); });
        ts.add(r3); r3.start(); Thread.sleep(40);
        // a timed reader joins r3's group, gives up
        long tr = l.tryReadLock(10, TimeUnit.MILLISECONDS);
        // an interruptible reader joins the last group and is interrupted out of it
        AtomicReference<String> ir = new AtomicReference<>();
        Thread intr = new Thread(() -> {
            try { long s = l.readLockInterruptibly(); ir.set("got"); l.unlockRead(s); } catch (InterruptedException e) { ir.set("IE"); }
        });
        intr.start(); Thread.sleep(40);
        intr.interrupt(); intr.join();
        long cw = l.tryConvertToWriteLock(w);
        l.unlockWrite(cw);
        for (Thread t : ts) t.join();
        return order + " " + tr + " " + ir.get() + " " + (cw == w) + " " + l.tryOptimisticRead();
    }

    /** Not a target: the default executor's thread name is host-dependent (the model is STUCK). */
    public static String hostThread(int n) {
        return CompletableFuture.supplyAsync(() -> Thread.currentThread().getName()).join().startsWith("Thread-") + " " + n;
    }
}

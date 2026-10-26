/*
 * rocq-jvm model (clean-room, Apache-2.0): a sequential stream pipeline. Each stage links to its
 * upstream stage; a stage can be linked to at most one downstream stage or terminal operation
 * (else IllegalStateException "stream has already been operated upon or closed"); the source is
 * consumed once ("source already consumed or closed"). Stream flags (SIZED, ORDERED, DISTINCT,
 * SORTED, SHORT_CIRCUIT, SIZE_ADJUSTING) are combined stage by stage; they decide which elements
 * are visited (a short-circuiting pipeline polls cancellationRequested between elements), whether
 * count() needs a traversal (a SIZED pipeline returns the size without visiting the elements) and
 * whether distinct()/sorted() have work to do. Only sequential streams are modelled: parallel()
 * and spliterator() are STUCK.
 */
package java.util.stream;

import java.util.Arrays;
import java.util.Comparator;
import java.util.HashSet;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.IntConsumer;
import java.util.function.LongConsumer;
import java.util.function.Predicate;
import java.util.function.Supplier;

abstract class Pipe {
    static final int SIZED = 1, ORDERED = 2, DISTINCT = 4, SORTED = 8, SHORT_CIRCUIT = 16, SIZE_ADJUSTING = 32;
    static final int STREAM_FLAGS = SIZED | ORDERED | DISTINCT | SORTED;
    static final String MSG_LINKED = "stream has already been operated upon or closed";
    static final String MSG_CONSUMED = "source already consumed or closed";
    static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;

    final Pipe source;
    final Pipe prev;
    Pipe next;
    final int depth;
    int flags;
    final Op op;
    // source stage only
    Src src;
    Runnable closeAction;
    boolean linked;

    Pipe(Src s) {
        this.source = this;
        this.prev = null;
        this.depth = 0;
        this.op = null;
        this.src = s;
        this.flags = s.characteristics() & STREAM_FLAGS;
    }

    Pipe(Pipe up, Op op) {
        if (up.linked) throw new IllegalStateException(MSG_LINKED);
        up.linked = true;
        up.next = this;
        this.prev = up;
        this.source = up.source;
        this.depth = up.depth + 1;
        this.op = op;
        this.flags = (up.flags & ~op.clear) | op.set;
    }

    /** An intermediate operation: flags it sets/clears, and the sink it puts in front of the
     *  downstream sink (given the flags of the upstream stage). */
    abstract static class Op {
        final int set, clear;

        Op(int set, int clear) {
            this.set = set;
            this.clear = clear;
        }

        abstract Sink wrap(int upFlags, Sink down);

        long adjust(long size) {
            return size;
        }
    }

    // ---------------------------------------------------------------- evaluation

    final boolean isOrdered() {
        return (flags & ORDERED) != 0;
    }

    /** The linked check of a terminal operation, then the source (terminal flags combined). */
    final Src terminal(int set, int clear) {
        if (linked) throw new IllegalStateException(MSG_LINKED);
        linked = true;
        return sourceSrc(set, clear);
    }

    final Src sourceSrc(int set, int clear) {
        Src s = source.src;
        if (s == null) throw new IllegalStateException(MSG_CONSUMED);
        source.src = null;
        if ((set | clear) != 0) flags = (flags & ~clear) | set;
        return s;
    }

    final Sink wrapSink(Sink sink) {
        if (sink == null) throw new NullPointerException();
        for (Pipe p = this; p.depth > 0; p = p.prev) sink = p.op.wrap(p.prev.flags, sink);
        return sink;
    }

    final void copyInto(Sink ws, Src s) {
        if ((flags & SHORT_CIRCUIT) == 0) {
            ws.begin(s.exactSize());
            s.forEachRemaining(ws);
            ws.end();
        } else {
            ws.begin(s.exactSize());
            do {
            } while (!ws.cancellationRequested() && s.tryAdvance(ws));
            ws.end();
        }
    }

    final <S extends Sink> S wrapAndCopyInto(S sink, Src s) {
        copyInto(wrapSink(sink), s);
        return sink;
    }

    final long exactOutputSize(Src s) {
        long size = (flags & SIZED) != 0 ? s.exactSize() : -1;
        if (size != -1 && (flags & SIZE_ADJUSTING) != 0) {
            for (Pipe st = source.next; st != null; st = st.next) size = st.op.adjust(size);
        }
        return size;
    }

    /** BaseStream.spliterator() without the public type: the source itself for a source stage,
     *  else a wrapping source that evaluates the pipeline lazily. */
    final Src spliteratorInternal() {
        if (linked) throw new IllegalStateException(MSG_LINKED);
        linked = true;
        if (this == source) {
            Src s = src;
            if (s == null) throw new IllegalStateException(MSG_CONSUMED);
            src = null;
            return s;
        }
        return new Wrap(this);
    }

    static Src srcOf(BaseStream<?, ?> st) {
        if (st instanceof Pipe) return ((Pipe) st).spliteratorInternal();
        throw ModelStuckS.unsupported("spliterator of a stream that is not a model pipeline");
    }

    // ---------------------------------------------------------------- close

    final void closeInternal() {
        linked = true;
        if (this == source) src = null;
        if (source.closeAction != null) {
            Runnable a = source.closeAction;
            source.closeAction = null;
            a.run();
        }
    }

    final void onCloseInternal(Runnable closeHandler) {
        if (linked) throw new IllegalStateException(MSG_LINKED);
        if (closeHandler == null) throw new NullPointerException();
        Runnable existing = source.closeAction;
        source.closeAction = (existing == null) ? closeHandler : composeWithExceptions(existing, closeHandler);
    }

    static Runnable composeWithExceptions(Runnable a, Runnable b) {
        return new Runnable() {
            public void run() {
                try {
                    a.run();
                } catch (Throwable e1) {
                    try {
                        b.run();
                    } catch (Throwable e2) {
                        try {
                            e1.addSuppressed(e2);
                        } catch (Throwable ignore) {
                        }
                    }
                    throw e1;
                }
                b.run();
            }
        };
    }

    static Runnable composedClose(BaseStream<?, ?> a, BaseStream<?, ?> b) {
        return new Runnable() {
            public void run() {
                try {
                    a.close();
                } catch (Throwable e1) {
                    try {
                        b.close();
                    } catch (Throwable e2) {
                        try {
                            e1.addSuppressed(e2);
                        } catch (Throwable ignore) {
                        }
                    }
                    throw e1;
                }
                b.close();
            }
        };
    }

    // ---------------------------------------------------------------- shared intermediate ops

    static Op filterOp(Predicate<Object> p) {
        return new Op(0, SIZED) {
            Sink wrap(int fl, Sink down) {
                return new Sink.Chained(down) {
                    void begin(long size) {
                        down.begin(-1);
                    }

                    public void accept(Object u) {
                        if (p.test(u)) down.accept(u);
                    }
                };
            }
        };
    }

    /** map / mapToX / boxed / asLongStream: one output per element. */
    static Op mapOp(Function<Object, Object> f, int clear) {
        return new Op(0, clear) {
            Sink wrap(int fl, Sink down) {
                return new Sink.Chained(down) {
                    public void accept(Object u) {
                        down.accept(f.apply(u));
                    }
                };
            }
        };
    }

    static Op peekOp(Consumer<Object> action) {
        return new Op(0, 0) {
            Sink wrap(int fl, Sink down) {
                return new Sink.Chained(down) {
                    public void accept(Object u) {
                        action.accept(u);
                        down.accept(u);
                    }
                };
            }
        };
    }

    static Op unorderedOp() {
        return new Op(0, ORDERED) {
            Sink wrap(int fl, Sink down) {
                return down;
            }
        };
    }

    /** mapMulti: the mapper receives the downstream sink itself as the consumer. */
    static Op mapMultiOp(BiConsumer<Object, Sink> mapper) {
        return new Op(0, SORTED | DISTINCT | SIZED) {
            Sink wrap(int fl, Sink down) {
                return new Sink.Chained(down) {
                    void begin(long size) {
                        down.begin(-1);
                    }

                    public void accept(Object u) {
                        mapper.accept(u, down);
                    }
                };
            }
        };
    }

    /** flatMap: shape 0 = Stream, 1 = IntStream, 2 = LongStream, 3 = DoubleStream results. */
    static Op flatMapOp(Function<Object, Object> mapper, int shape) {
        return new Op(0, SORTED | DISTINCT | SIZED) {
            Sink wrap(int fl, Sink down) {
                return new Sink.Chained(down) {
                    boolean cancellationRequestedCalled;

                    void begin(long size) {
                        down.begin(-1);
                    }

                    public void accept(Object u) {
                        try (BaseStream<?, ?> result = (BaseStream<?, ?>) mapper.apply(u)) {
                            if (result != null) {
                                if (!cancellationRequestedCalled) {
                                    forEachInto(result.sequential(), shape, down);
                                } else {
                                    Src s = srcOf(result.sequential());
                                    do {
                                    } while (!down.cancellationRequested() && s.tryAdvance(down));
                                }
                            }
                        }
                    }

                    boolean cancellationRequested() {
                        cancellationRequestedCalled = true;
                        return down.cancellationRequested();
                    }
                };
            }
        };
    }

    @SuppressWarnings("unchecked")
    static void forEachInto(BaseStream<?, ?> st, int shape, Sink down) {
        if (shape == 0) ((Stream<Object>) st).forEach(down);
        else if (shape == 1) ((IntStream) st).forEach((IntConsumer) down);
        else if (shape == 2) ((LongStream) st).forEach((LongConsumer) down);
        else ((DoubleStream) st).forEach((java.util.function.DoubleConsumer) down);
    }

    /** skip/limit (limit < 0: no limit). */
    static Op sliceOp(long skip, long limit) {
        long normalizedLimit = limit >= 0 ? limit : Long.MAX_VALUE;
        return new Op(SIZE_ADJUSTING | ((limit != -1) ? SHORT_CIRCUIT : 0), 0) {
            long adjust(long size) {
                return calcSize(size, skip, normalizedLimit);
            }

            Sink wrap(int fl, Sink down) {
                return new Sink.Chained(down) {
                    long n = skip;
                    long m = normalizedLimit;

                    void begin(long size) {
                        down.begin(calcSize(size, skip, m));
                    }

                    public void accept(Object t) {
                        if (n == 0) {
                            if (m > 0) {
                                m--;
                                down.accept(t);
                            }
                        } else {
                            n--;
                        }
                    }

                    boolean cancellationRequested() {
                        return m == 0 || down.cancellationRequested();
                    }
                };
            }
        };
    }

    static long calcSize(long size, long skip, long limit) {
        if (size < 0) return -1;
        long v = size - skip;
        if (v < 0) v = 0;
        return v < limit ? v : limit;
    }

    static Op takeWhileOp(Predicate<Object> p) {
        return new Op(SHORT_CIRCUIT, SIZED) {
            Sink wrap(int fl, Sink down) {
                return new Sink.Chained(down) {
                    boolean take = true;

                    void begin(long size) {
                        down.begin(-1);
                    }

                    public void accept(Object t) {
                        if (take && (take = p.test(t))) down.accept(t);
                    }

                    boolean cancellationRequested() {
                        return !take || down.cancellationRequested();
                    }
                };
            }
        };
    }

    static Op dropWhileOp(Predicate<Object> p) {
        return new Op(0, SIZED) {
            Sink wrap(int fl, Sink down) {
                return new Sink.Chained(down) {
                    boolean take;

                    public void accept(Object t) {
                        boolean takeElement = take || (take = !p.test(t));
                        if (takeElement) down.accept(t);
                    }
                };
            }
        };
    }

    static Op distinctOp() {
        return new Op(DISTINCT, SIZED) {
            Sink wrap(int fl, Sink down) {
                if ((fl & DISTINCT) != 0) return down;
                if ((fl & SORTED) != 0) {
                    return new Sink.Chained(down) {
                        boolean seenNull;
                        Object lastSeen;

                        void begin(long size) {
                            seenNull = false;
                            lastSeen = null;
                            down.begin(-1);
                        }

                        void end() {
                            seenNull = false;
                            lastSeen = null;
                            down.end();
                        }

                        public void accept(Object t) {
                            if (t == null) {
                                if (!seenNull) {
                                    seenNull = true;
                                    down.accept(lastSeen = null);
                                }
                            } else if (lastSeen == null || !t.equals(lastSeen)) {
                                down.accept(lastSeen = t);
                            }
                        }
                    };
                }
                return new Sink.Chained(down) {
                    Set<Object> seen;

                    void begin(long size) {
                        seen = new HashSet<>();
                        down.begin(-1);
                    }

                    void end() {
                        seen = null;
                        down.end();
                    }

                    public void accept(Object t) {
                        if (seen.add(t)) down.accept(t);
                    }
                };
            }
        };
    }

    /**
     * sorted: natural (comparator null; sets SORTED, and is a no-op on a SORTED upstream) or by a
     * comparator (clears SORTED). The elements are buffered between begin and end, sorted with a
     * stable sort (as the JDK's), then pushed downstream (begin is sent downstream only then).
     * primitive: elements are Integer/Long boxes compared numerically.
     */
    static Op sortedOp(Comparator<Object> comparator, boolean primitive) {
        boolean natural = comparator == null;
        return new Op(natural ? (ORDERED | SORTED) : ORDERED, natural ? 0 : SORTED) {
            Sink wrap(int fl, Sink down) {
                if (natural && (fl & SORTED) != 0) return down;
                if (down == null) throw new NullPointerException();
                boolean sized = (fl & SIZED) != 0;
                return new Sink() {
                    boolean cancellationRequestedCalled;
                    Object[] array;
                    int offset;

                    void begin(long size) {
                        if (size >= MAX_ARRAY_SIZE) throw new IllegalArgumentException("Stream size exceeds max array size");
                        array = new Object[sized ? (int) size : (size >= 0 ? (int) size : 10)];
                        offset = 0;
                    }

                    public void accept(Object t) {
                        if (!sized && offset == array.length) array = copyOf(array, offset < 5 ? 10 : offset * 2);
                        array[offset++] = t;
                    }

                    void end() {
                        sortBuffer(array, offset, comparator, primitive);
                        down.begin(offset);
                        if (!cancellationRequestedCalled) {
                            for (int i = 0; i < offset; i++) down.accept(array[i]);
                        } else {
                            for (int i = 0; i < offset && !down.cancellationRequested(); i++) down.accept(array[i]);
                        }
                        down.end();
                        array = null;
                    }

                    boolean cancellationRequested() {
                        cancellationRequestedCalled = true;
                        return false;
                    }
                };
            }
        };
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    static void sortBuffer(Object[] a, int n, Comparator<Object> comparator, boolean primitive) {
        if (n < 2) return;
        Comparator c = comparator;
        if (c == null) {
            if (!primitive) {
                // natural order: elements of one class (String, boxes, a user Comparable); nulls and
                // mixed classes give JDK messages (ClassCastException / helpful NPE) that are not modelled
                Object first = a[0];
                if (first == null) throw ModelStuckS.unsupported("sorted(): null element");
                Class<?> k = first.getClass();
                for (int i = 1; i < n; i++) {
                    if (a[i] == null) throw ModelStuckS.unsupported("sorted(): null element");
                    if (a[i].getClass() != k) throw ModelStuckS.unsupported("sorted(): elements of different classes");
                }
                if (!(first instanceof Comparable)) throw ModelStuckS.unsupported("sorted(): element not Comparable (ClassCastException message)");
            }
            c = Comparator.naturalOrder();
        }
        Arrays.sort(a, 0, n, c);
    }

    // ---------------------------------------------------------------- shared terminal ops

    final void forEachT(Consumer<Object> action, boolean ordered) {
        Src s = terminal(0, ordered ? 0 : ORDERED);
        wrapAndCopyInto(new Sink() {
            public void accept(Object t) {
                action.accept(t);
            }
        }, s);
    }

    final Object reduceT(Object identity, BiFunction<Object, Object, Object> acc) {
        Src s = terminal(0, 0);
        return wrapAndCopyInto(new Sink() {
            Object state;

            void begin(long size) {
                state = identity;
            }

            public void accept(Object t) {
                state = acc.apply(state, t);
            }
        }, s).state;
    }

    /** reduce(BinaryOperator): null if empty, else a one-element array holding the result. */
    final Object[] reduceOptT(BinaryOperator<Object> op) {
        Src s = terminal(0, 0);
        class R extends Sink {
            boolean empty;
            Object state;

            void begin(long size) {
                empty = true;
                state = null;
            }

            public void accept(Object t) {
                if (empty) {
                    empty = false;
                    state = t;
                } else {
                    state = op.apply(state, t);
                }
            }
        }
        R r = wrapAndCopyInto(new R(), s);
        return r.empty ? null : new Object[] { r.state };
    }

    final Object collectT(Supplier<?> supplier, BiConsumer<Object, Object> acc, int clear) {
        return collectS(terminal(0, clear), supplier, acc);
    }

    final Object collectS(Src s, Supplier<?> supplier, BiConsumer<Object, Object> acc) {
        return wrapAndCopyInto(new Sink() {
            Object state;

            void begin(long size) {
                state = supplier.get();
            }

            public void accept(Object t) {
                acc.accept(state, t);
            }
        }, s).state;
    }

    /** kind 0 = any, 1 = all, 2 = none. */
    final boolean matchT(Predicate<Object> p, int kind) {
        boolean stopOnPredicateMatches = kind != 1;
        boolean shortCircuitResult = kind == 0;
        Src s = terminal(SHORT_CIRCUIT, ORDERED);
        class M extends Sink {
            boolean stop;
            boolean value = !shortCircuitResult;

            public void accept(Object t) {
                if (!stop && p.test(t) == stopOnPredicateMatches) {
                    stop = true;
                    value = shortCircuitResult;
                }
            }

            boolean cancellationRequested() {
                return stop;
            }
        }
        return wrapAndCopyInto(new M(), s).value;
    }

    /** findFirst/findAny: null if empty, else a one-element array. */
    final Object[] findT(boolean first) {
        Src s = terminal(SHORT_CIRCUIT, first ? 0 : ORDERED);
        class F extends Sink {
            boolean hasValue;
            Object value;

            public void accept(Object t) {
                if (!hasValue) {
                    hasValue = true;
                    value = t;
                }
            }

            boolean cancellationRequested() {
                return hasValue;
            }
        }
        F f = wrapAndCopyInto(new F(), s);
        return f.hasValue ? new Object[] { f.value } : null;
    }

    final long countT() {
        Src s = terminal(0, ORDERED);
        long size = exactOutputSize(s);
        if (size != -1) return size;
        class C extends Sink {
            long count;

            void begin(long sz) {
                count = 0L;
            }

            public void accept(Object t) {
                count++;
            }
        }
        return wrapAndCopyInto(new C(), s).count;
    }

    /** The elements in an Object[] of exactly the right length (primitive toArray). */
    final Object[] toObjectArrayT() {
        if (linked) throw new IllegalStateException(MSG_LINKED);
        linked = true;
        Src s = sourceSrc(0, 0);
        Buf b = wrapAndCopyInto(new Buf(), s);
        return copyOf(b.a, b.n);
    }

    /** A growable buffer sink (the JDK's SpinedBuffer). */
    static final class Buf extends Sink {
        Object[] a = new Object[16];
        int n;

        public void accept(Object t) {
            if (n == a.length) a = copyOf(a, n * 2);
            a[n++] = t;
        }

        void clear() {
            for (int i = 0; i < n; i++) a[i] = null;
            n = 0;
        }
    }

    static Object[] copyOf(Object[] a, int n) {
        Object[] r = new Object[n];
        for (int i = 0; i < n && i < a.length; i++) r[i] = a[i];
        return r;
    }

    static int[] copyOf(int[] a, int n) {
        int[] r = new int[n];
        for (int i = 0; i < n && i < a.length; i++) r[i] = a[i];
        return r;
    }

    static double[] copyOf(double[] a, int n) {
        double[] b = new double[n];
        System.arraycopy(a, 0, b, 0, Math.min(a.length, n));
        return b;
    }

    static long[] copyOf(long[] a, int n) {
        long[] r = new long[n];
        for (int i = 0; i < n && i < a.length; i++) r[i] = a[i];
        return r;
    }

    final Iterator<Object> iteratorInternal() {
        return new SrcIterator(spliteratorInternal());
    }

    /** Spliterators.iterator(spliterator): one element is fetched ahead by hasNext. */
    static final class SrcIterator extends Sink implements Iterator<Object> {
        final Src s;
        boolean valueReady;
        Object nextElement;

        SrcIterator(Src s) {
            this.s = s;
        }

        public void accept(Object t) {
            valueReady = true;
            nextElement = t;
        }

        public boolean hasNext() {
            if (!valueReady) s.tryAdvance(this);
            return valueReady;
        }

        public Object next() {
            if (!valueReady && !hasNext()) throw new NoSuchElementException();
            valueReady = false;
            Object t = nextElement;
            nextElement = null;
            return t;
        }

        public void remove() {
            throw new UnsupportedOperationException("remove");
        }

        public void forEachRemaining(Consumer<? super Object> action) {
            if (action == null) throw new NullPointerException();
            if (valueReady) {
                valueReady = false;
                Object t = nextElement;
                nextElement = null;
                action.accept(t);
            }
            @SuppressWarnings("unchecked")
            Consumer<Object> a = (Consumer<Object>) action;
            s.forEachRemaining(new Sink.Of(a));
        }
    }

    /** The spliterator of a non-source stage: evaluates the pipeline into a buffer on demand. */
    static final class Wrap extends Src {
        final Pipe ph;
        Src s;
        Sink bufferSink;
        Buf buffer;
        long nextToConsume;
        boolean finished;

        Wrap(Pipe ph) {
            this.ph = ph;
        }

        void init() {
            if (s == null) s = ph.sourceSrc(0, 0);
        }

        boolean doAdvance() {
            if (buffer == null) {
                if (finished) return false;
                init();
                Buf b = new Buf();
                buffer = b;
                bufferSink = ph.wrapSink(new Sink() {
                    public void accept(Object t) {
                        b.accept(t);
                    }
                });
                nextToConsume = 0;
                bufferSink.begin(s.exactSize());
                return fillBuffer();
            } else {
                ++nextToConsume;
                boolean hasNext = nextToConsume < buffer.n;
                if (!hasNext) {
                    nextToConsume = 0;
                    buffer.clear();
                    hasNext = fillBuffer();
                }
                return hasNext;
            }
        }

        private boolean fillBuffer() {
            while (buffer.n == 0) {
                if (bufferSink.cancellationRequested() || !s.tryAdvance(bufferSink)) {
                    if (finished) return false;
                    bufferSink.end();
                    finished = true;
                }
            }
            return true;
        }

        boolean tryAdvance(Sink c) {
            boolean hasNext = doAdvance();
            if (hasNext) c.accept(buffer.a[(int) nextToConsume]);
            return hasNext;
        }

        void forEachRemaining(Sink c) {
            if (buffer == null && !finished) {
                init();
                ph.wrapAndCopyInto(new Sink.Of(c), s);
                finished = true;
            } else {
                do {
                } while (tryAdvance(c));
            }
        }

        long exactSize() {
            init();
            return ph.exactOutputSize(s);
        }

        long estimateSize() {
            long e = exactSize();
            return e == -1 ? s.estimateSize() : e;
        }

        int characteristics() {
            init();
            int c = ph.flags & STREAM_FLAGS;
            if ((c & SIZED) != 0) {
                c &= ~SIZED;
                c |= s.characteristics() & SIZED;
            }
            return c;
        }
    }
}

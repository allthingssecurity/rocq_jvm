/*
 * rocq-jvm model (clean-room, Apache-2.0): the push protocol of a sequential stream pipeline, as
 * described in the java.util.stream package documentation: begin(size) / accept* / end, with
 * cancellationRequested() polled by short-circuiting traversals. Elements of int and long streams
 * travel boxed (Integer.valueOf / Long.valueOf at the producing stage), which is not observable.
 * A Sink is also the Consumer / IntConsumer / LongConsumer that mapMulti and flatMap hand on.
 */
package java.util.stream;

import java.util.function.Consumer;
import java.util.function.DoubleConsumer;
import java.util.function.IntConsumer;
import java.util.function.LongConsumer;

abstract class Sink implements Consumer<Object>, IntConsumer, LongConsumer, DoubleConsumer {
    void begin(long size) {
    }

    void end() {
    }

    boolean cancellationRequested() {
        return false;
    }

    public abstract void accept(Object t);

    public void accept(int value) {
        accept((Object) Integer.valueOf(value));
    }

    public void accept(long value) {
        accept((Object) Long.valueOf(value));
    }

    public void accept(double value) {
        accept((Object) Double.valueOf(value));
    }

    /** A stage's sink: begin/end/cancellationRequested go to the downstream sink. */
    abstract static class Chained extends Sink {
        final Sink down;

        Chained(Sink down) {
            if (down == null) throw new NullPointerException();
            this.down = down;
        }

        void begin(long size) {
            down.begin(size);
        }

        void end() {
            down.end();
        }

        boolean cancellationRequested() {
            return down.cancellationRequested();
        }
    }

    /** A consumer seen as a sink: only accept is forwarded (begin/end/cancellation are no-ops). */
    static final class Of extends Sink {
        final Consumer<Object> c;

        Of(Consumer<Object> c) {
            this.c = c;
        }

        public void accept(Object t) {
            c.accept(t);
        }
    }
}

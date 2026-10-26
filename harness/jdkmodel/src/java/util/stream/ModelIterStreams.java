/*
 * rocq-jvm helper (not a JDK class; clean-room, Apache-2.0): a sequential stream over an
 * Iterator, as StreamSupport.stream(Spliterators.spliteratorUnknownSize(it, ORDERED | ...),
 * false) builds it in the JDK (an ORDERED source of unknown size; tryAdvance is
 * hasNext()/next(), forEachRemaining the iterator's). Used by BufferedReader.lines(),
 * String.lines() and String.codePoints() (java.lang.ModelStrings).
 * HotSpot never loads this class.
 */
package java.util.stream;

import java.util.Iterator;

public final class ModelIterStreams {
    private ModelIterStreams() {
    }

    public static <T> Stream<T> orderedUnknownSize(Iterator<T> it) {
        return new RefPipe<>(new IterSrc(it));
    }

    /** An ordered IntStream of unknown size over Integer values (String.codePoints of a
     *  non-Latin-1 string). */
    public static IntStream orderedUnknownSizeInt(Iterator<Integer> it) {
        return new IntPipe(new IterSrc(it));
    }

    static final class IterSrc extends Src {
        final Iterator<?> it;

        IterSrc(Iterator<?> it) {
            this.it = it;
        }

        boolean tryAdvance(Sink c) {
            if (it.hasNext()) {
                c.accept(it.next());
                return true;
            }
            return false;
        }

        void forEachRemaining(Sink c) {
            while (it.hasNext()) c.accept(it.next());
        }

        long estimateSize() {
            return Long.MAX_VALUE;
        }

        int characteristics() {
            return ORDERED;
        }
    }
}

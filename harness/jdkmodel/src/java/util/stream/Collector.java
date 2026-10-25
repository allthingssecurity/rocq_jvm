/*
 * rocq-jvm model of java.util.stream.Collector (clean-room, Apache-2.0), from the Javadoc.
 * The characteristics sets are unmodifiable and iterate in declaration order (as the JDK's EnumSets).
 */
package java.util.stream;

import java.util.Set;
import java.util.function.BiConsumer;
import java.util.function.BinaryOperator;
import java.util.function.Function;
import java.util.function.Supplier;

public interface Collector<T, A, R> {
    Supplier<A> supplier();

    BiConsumer<A, T> accumulator();

    BinaryOperator<A> combiner();

    Function<A, R> finisher();

    Set<Characteristics> characteristics();

    /** Javadoc: IDENTITY_FINISH is always added. */
    public static <T, R> Collector<T, R, R> of(Supplier<R> supplier, BiConsumer<R, T> accumulator,
                                              BinaryOperator<R> combiner, Characteristics... characteristics) {
        if (supplier == null || accumulator == null || combiner == null || characteristics == null)
            throw new NullPointerException();
        int bits = CharSet.ID;
        for (Characteristics c : characteristics) bits |= CharSet.bit(c);
        return new Collectors.CollectorImpl<>(supplier, accumulator, combiner, null,
                                              characteristics.length == 0 ? Collectors.CH_ID : new CharSet(bits));
    }

    public static <T, A, R> Collector<T, A, R> of(Supplier<A> supplier, BiConsumer<A, T> accumulator,
                                                 BinaryOperator<A> combiner, Function<A, R> finisher,
                                                 Characteristics... characteristics) {
        if (supplier == null || accumulator == null || combiner == null || finisher == null || characteristics == null)
            throw new NullPointerException();
        Set<Characteristics> cs = Collectors.CH_NOID;
        if (characteristics.length > 0) {
            int bits = 0;
            for (Characteristics c : characteristics) bits |= CharSet.bit(c);
            cs = new CharSet(bits);
        }
        return new Collectors.CollectorImpl<>(supplier, accumulator, combiner, finisher, cs);
    }

    enum Characteristics {
        CONCURRENT,
        UNORDERED,
        IDENTITY_FINISH
    }
}

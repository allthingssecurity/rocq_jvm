/*
 * rocq-jvm model of java.util.OptionalLong (clean-room, Apache-2.0), from the Javadoc: a
 * container that may hold a long; empty() is one shared instance; getAsLong/orElseThrow throw
 * NoSuchElementException("No value present"); equals/hashCode/toString as documented.
 * A null functional argument that the JDK dereferences without an explicit check is STUCK
 * (the JDK's NullPointerException has a "helpful" message).
 */
package java.util;

import java.util.function.LongConsumer;
import java.util.function.LongSupplier;
import java.util.function.Supplier;
import java.util.stream.LongStream;

public final class OptionalLong {
    private static final OptionalLong EMPTY = new OptionalLong();

    private final boolean isPresent;
    private final long value;

    private OptionalLong() {
        this.isPresent = false;
        this.value = 0;
    }

    private OptionalLong(long value) {
        this.isPresent = true;
        this.value = value;
    }

    public static OptionalLong empty() {
        return EMPTY;
    }

    public static OptionalLong of(long value) {
        return new OptionalLong(value);
    }

    public long getAsLong() {
        if (!isPresent) throw new NoSuchElementException("No value present");
        return value;
    }

    public boolean isPresent() {
        return isPresent;
    }

    public boolean isEmpty() {
        return !isPresent;
    }

    public void ifPresent(LongConsumer action) {
        if (isPresent) {
            Optional.nn(action);
            action.accept(value);
        }
    }

    public void ifPresentOrElse(LongConsumer action, Runnable emptyAction) {
        if (isPresent) {
            Optional.nn(action);
            action.accept(value);
        } else {
            Optional.nn(emptyAction);
            emptyAction.run();
        }
    }

    public LongStream stream() {
        return isPresent ? LongStream.of(value) : LongStream.empty();
    }

    public long orElse(long other) {
        return isPresent ? value : other;
    }

    public long orElseGet(LongSupplier supplier) {
        if (isPresent) return value;
        Optional.nn(supplier);
        return supplier.getAsLong();
    }

    public long orElseThrow() {
        if (!isPresent) throw new NoSuchElementException("No value present");
        return value;
    }

    public <X extends Throwable> long orElseThrow(Supplier<? extends X> exceptionSupplier) throws X {
        if (isPresent) return value;
        Optional.nn(exceptionSupplier);
        X x = exceptionSupplier.get();
        Optional.nn(x);
        throw x;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof OptionalLong)) return false;
        OptionalLong other = (OptionalLong) obj;
        return (isPresent && other.isPresent) ? value == other.value : isPresent == other.isPresent;
    }

    @Override
    public int hashCode() {
        return isPresent ? (int) (value ^ (value >>> 32)) : 0;
    }

    @Override
    public String toString() {
        return isPresent ? ("OptionalLong[" + value + "]") : "OptionalLong.empty";
    }
}

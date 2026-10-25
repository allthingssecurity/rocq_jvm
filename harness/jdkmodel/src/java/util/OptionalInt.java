/*
 * rocq-jvm model of java.util.OptionalInt (clean-room, Apache-2.0), from the Javadoc: a
 * container that may hold a int; empty() is one shared instance; getAsInt/orElseThrow throw
 * NoSuchElementException("No value present"); equals/hashCode/toString as documented.
 * A null functional argument that the JDK dereferences without an explicit check is STUCK
 * (the JDK's NullPointerException has a "helpful" message).
 */
package java.util;

import java.util.function.IntConsumer;
import java.util.function.IntSupplier;
import java.util.function.Supplier;
import java.util.stream.IntStream;

public final class OptionalInt {
    private static final OptionalInt EMPTY = new OptionalInt();

    private final boolean isPresent;
    private final int value;

    private OptionalInt() {
        this.isPresent = false;
        this.value = 0;
    }

    private OptionalInt(int value) {
        this.isPresent = true;
        this.value = value;
    }

    public static OptionalInt empty() {
        return EMPTY;
    }

    public static OptionalInt of(int value) {
        return new OptionalInt(value);
    }

    public int getAsInt() {
        if (!isPresent) throw new NoSuchElementException("No value present");
        return value;
    }

    public boolean isPresent() {
        return isPresent;
    }

    public boolean isEmpty() {
        return !isPresent;
    }

    public void ifPresent(IntConsumer action) {
        if (isPresent) {
            Optional.nn(action);
            action.accept(value);
        }
    }

    public void ifPresentOrElse(IntConsumer action, Runnable emptyAction) {
        if (isPresent) {
            Optional.nn(action);
            action.accept(value);
        } else {
            Optional.nn(emptyAction);
            emptyAction.run();
        }
    }

    public IntStream stream() {
        return isPresent ? IntStream.of(value) : IntStream.empty();
    }

    public int orElse(int other) {
        return isPresent ? value : other;
    }

    public int orElseGet(IntSupplier supplier) {
        if (isPresent) return value;
        Optional.nn(supplier);
        return supplier.getAsInt();
    }

    public int orElseThrow() {
        if (!isPresent) throw new NoSuchElementException("No value present");
        return value;
    }

    public <X extends Throwable> int orElseThrow(Supplier<? extends X> exceptionSupplier) throws X {
        if (isPresent) return value;
        Optional.nn(exceptionSupplier);
        X x = exceptionSupplier.get();
        Optional.nn(x);
        throw x;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof OptionalInt)) return false;
        OptionalInt other = (OptionalInt) obj;
        return (isPresent && other.isPresent) ? value == other.value : isPresent == other.isPresent;
    }

    @Override
    public int hashCode() {
        return isPresent ? value : 0;
    }

    @Override
    public String toString() {
        return isPresent ? ("OptionalInt[" + value + "]") : "OptionalInt.empty";
    }
}

/*
 * rocq-jvm model of java.util.OptionalDouble (clean-room, Apache-2.0), from the Javadoc: a
 * container that may hold a double; empty() is one shared instance; getAsDouble/orElseThrow throw
 * NoSuchElementException("No value present"); equals/hashCode/toString as documented.
 * A null functional argument that the JDK dereferences without an explicit check is STUCK
 * (the JDK's NullPointerException has a "helpful" message).
 * toString (Double.toString) and stream() (DoubleStream) are STUCK.
 */
package java.util;

import java.util.function.DoubleConsumer;
import java.util.function.DoubleSupplier;
import java.util.function.Supplier;

public final class OptionalDouble {
    private static final OptionalDouble EMPTY = new OptionalDouble();

    private final boolean isPresent;
    private final double value;

    private OptionalDouble() {
        this.isPresent = false;
        this.value = 0;
    }

    private OptionalDouble(double value) {
        this.isPresent = true;
        this.value = value;
    }

    public static OptionalDouble empty() {
        return EMPTY;
    }

    public static OptionalDouble of(double value) {
        return new OptionalDouble(value);
    }

    public double getAsDouble() {
        if (!isPresent) throw new NoSuchElementException("No value present");
        return value;
    }

    public boolean isPresent() {
        return isPresent;
    }

    public boolean isEmpty() {
        return !isPresent;
    }

    public void ifPresent(DoubleConsumer action) {
        if (isPresent) {
            Optional.nn(action);
            action.accept(value);
        }
    }

    public void ifPresentOrElse(DoubleConsumer action, Runnable emptyAction) {
        if (isPresent) {
            Optional.nn(action);
            action.accept(value);
        } else {
            Optional.nn(emptyAction);
            emptyAction.run();
        }
    }

    public java.util.stream.DoubleStream stream() {
        throw ModelStuck.unsupported("OptionalDouble.stream (DoubleStream)");
    }

    public double orElse(double other) {
        return isPresent ? value : other;
    }

    public double orElseGet(DoubleSupplier supplier) {
        if (isPresent) return value;
        Optional.nn(supplier);
        return supplier.getAsDouble();
    }

    public double orElseThrow() {
        if (!isPresent) throw new NoSuchElementException("No value present");
        return value;
    }

    public <X extends Throwable> double orElseThrow(Supplier<? extends X> exceptionSupplier) throws X {
        if (isPresent) return value;
        Optional.nn(exceptionSupplier);
        X x = exceptionSupplier.get();
        Optional.nn(x);
        throw x;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof OptionalDouble)) return false;
        OptionalDouble other = (OptionalDouble) obj;
        return (isPresent && other.isPresent) ? Double.compare(value, other.value) == 0 : isPresent == other.isPresent;
    }

    @Override
    public int hashCode() {
        return isPresent ? Double.hashCode(value) : 0;
    }

    @Override
    public String toString() {
        if (isPresent) throw ModelStuck.unsupported("OptionalDouble.toString (Double.toString)");
        return "OptionalDouble.empty";
    }
}

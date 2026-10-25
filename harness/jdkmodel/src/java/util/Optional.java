/*
 * rocq-jvm model of java.util.Optional (clean-room, Apache-2.0), from the Javadoc: a container
 * that holds a non-null value or nothing; empty() is one shared instance; get/orElseThrow throw
 * NoSuchElementException("No value present"); equals/hashCode/toString as documented.
 * A null functional argument that the JDK dereferences without an explicit check (the JDK throws a
 * "helpful" NullPointerException whose message names the variable) is STUCK.
 */
package java.util;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.Supplier;
import java.util.stream.Stream;

public final class Optional<T> {
    private static final Optional<?> EMPTY = new Optional<>(null);

    private final T value;

    private Optional(T value) {
        this.value = value;
    }

    @SuppressWarnings("unchecked")
    public static <T> Optional<T> empty() {
        return (Optional<T>) EMPTY;
    }

    public static <T> Optional<T> of(T value) {
        if (value == null) throw new NullPointerException();
        return new Optional<>(value);
    }

    @SuppressWarnings("unchecked")
    public static <T> Optional<T> ofNullable(T value) {
        return value == null ? (Optional<T>) EMPTY : new Optional<>(value);
    }

    public T get() {
        if (value == null) throw new NoSuchElementException("No value present");
        return value;
    }

    public boolean isPresent() {
        return value != null;
    }

    public boolean isEmpty() {
        return value == null;
    }

    static void nn(Object f) {
        if (f == null) throw ModelStuck.unsupported("Optional: helpful NullPointerException message");
    }

    public void ifPresent(Consumer<? super T> action) {
        if (value != null) {
            nn(action);
            action.accept(value);
        }
    }

    public void ifPresentOrElse(Consumer<? super T> action, Runnable emptyAction) {
        if (value != null) {
            nn(action);
            action.accept(value);
        } else {
            nn(emptyAction);
            emptyAction.run();
        }
    }

    public Optional<T> filter(Predicate<? super T> predicate) {
        if (predicate == null) throw new NullPointerException();
        if (value == null) return this;
        return predicate.test(value) ? this : empty();
    }

    public <U> Optional<U> map(Function<? super T, ? extends U> mapper) {
        if (mapper == null) throw new NullPointerException();
        if (value == null) return empty();
        return Optional.ofNullable(mapper.apply(value));
    }

    @SuppressWarnings("unchecked")
    public <U> Optional<U> flatMap(Function<? super T, ? extends Optional<? extends U>> mapper) {
        if (mapper == null) throw new NullPointerException();
        if (value == null) return empty();
        Optional<U> r = (Optional<U>) mapper.apply(value);
        if (r == null) throw new NullPointerException();
        return r;
    }

    @SuppressWarnings("unchecked")
    public Optional<T> or(Supplier<? extends Optional<? extends T>> supplier) {
        if (supplier == null) throw new NullPointerException();
        if (value != null) return this;
        Optional<T> r = (Optional<T>) supplier.get();
        if (r == null) throw new NullPointerException();
        return r;
    }

    public Stream<T> stream() {
        return value == null ? Stream.empty() : Stream.of(value);
    }

    public T orElse(T other) {
        return value != null ? value : other;
    }

    public T orElseGet(Supplier<? extends T> supplier) {
        if (value != null) return value;
        nn(supplier);
        return supplier.get();
    }

    public T orElseThrow() {
        if (value == null) throw new NoSuchElementException("No value present");
        return value;
    }

    public <X extends Throwable> T orElseThrow(Supplier<? extends X> exceptionSupplier) throws X {
        if (value != null) return value;
        nn(exceptionSupplier);
        X x = exceptionSupplier.get();
        nn(x);
        throw x;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Optional)) return false;
        Object o = ((Optional<?>) obj).value;
        return value == o || (value != null && value.equals(o));
    }

    @Override
    public int hashCode() {
        return value == null ? 0 : value.hashCode();
    }

    @Override
    public String toString() {
        return value != null ? ("Optional[" + value + "]") : "Optional.empty";
    }
}

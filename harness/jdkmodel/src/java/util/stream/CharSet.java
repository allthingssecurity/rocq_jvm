/*
 * rocq-jvm model (clean-room, Apache-2.0): an unmodifiable set of Collector.Characteristics that
 * iterates in declaration order, like the JDK's (unmodifiable) EnumSets of characteristics.
 */
package java.util.stream;

import java.util.AbstractSet;
import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.Set;

final class CharSet extends AbstractSet<Collector.Characteristics> {
    static final int CONCURRENT = 1, UNORDERED = 2, ID = 4;

    final int bits;

    CharSet(int bits) {
        this.bits = bits;
    }

    static int bit(Collector.Characteristics c) {
        if (c == null) throw ModelStuckS.unsupported("EnumSet: null characteristic (helpful NullPointerException)");
        if (c == Collector.Characteristics.CONCURRENT) return CONCURRENT;
        if (c == Collector.Characteristics.UNORDERED) return UNORDERED;
        return ID;
    }

    static int bitsOf(Set<Collector.Characteristics> s) {
        if (s instanceof CharSet) return ((CharSet) s).bits;
        int b = 0;
        for (Collector.Characteristics c : s) b |= bit(c);
        return b;
    }

    private static Collector.Characteristics of(int bit) {
        if (bit == CONCURRENT) return Collector.Characteristics.CONCURRENT;
        if (bit == UNORDERED) return Collector.Characteristics.UNORDERED;
        return Collector.Characteristics.IDENTITY_FINISH;
    }

    public int size() {
        return (bits & 1) + ((bits >> 1) & 1) + ((bits >> 2) & 1);
    }

    public boolean contains(Object o) {
        if (!(o instanceof Collector.Characteristics)) return false;
        return (bits & bit((Collector.Characteristics) o)) != 0;
    }

    // unmodifiable (Collections.unmodifiableSet): every mutator throws
    public boolean add(Collector.Characteristics e) {
        throw new UnsupportedOperationException();
    }

    public boolean remove(Object o) {
        throw new UnsupportedOperationException();
    }

    public boolean addAll(java.util.Collection<? extends Collector.Characteristics> c) {
        throw new UnsupportedOperationException();
    }

    public boolean removeAll(java.util.Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    public boolean retainAll(java.util.Collection<?> c) {
        throw new UnsupportedOperationException();
    }

    public void clear() {
        throw new UnsupportedOperationException();
    }

    public boolean removeIf(java.util.function.Predicate<? super Collector.Characteristics> filter) {
        throw new UnsupportedOperationException();
    }

    public Iterator<Collector.Characteristics> iterator() {
        return new Iterator<Collector.Characteristics>() {
            int next = nextBit(1);

            private int nextBit(int from) {
                for (int b = from; b <= ID; b <<= 1) {
                    if ((bits & b) != 0) return b;
                }
                return 0;
            }

            public boolean hasNext() {
                return next != 0;
            }

            public void remove() {
                throw new UnsupportedOperationException();
            }

            public Collector.Characteristics next() {
                if (next == 0) throw new NoSuchElementException();
                int b = next;
                next = nextBit(b << 1);
                return of(b);
            }
        };
    }
}

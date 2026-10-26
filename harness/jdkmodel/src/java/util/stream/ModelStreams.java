/*
 * rocq-jvm helper (not a JDK class; clean-room, Apache-2.0): the entry points through which the
 * java.util model classes (Collection.stream, Arrays.stream) create model pipelines. HotSpot never
 * loads this class.
 */
package java.util.stream;

import java.util.Collection;
import java.util.function.IntSupplier;

public final class ModelStreams {
    private ModelStreams() {
    }

    /** Characteristics for {@link #ofCollection}. */
    public static final int SIZED = Src.SIZED, ORDERED = Src.ORDERED, DISTINCT = Src.DISTINCT, SORTED = Src.SORTED;
    /** Traversal kinds for {@link #ofCollection}: the JDK traverses with the iterator (exact), or
     *  with an internal fail-fast spliterator (a modification during the traversal is STUCK). */
    public static final int ITER = Src.Coll.ITER, GUARD = Src.Coll.GUARD;

    /** Spliterators.checkFromToBounds (arrays). */
    static void checkFromToBounds(int arrayLength, int origin, int fence) {
        if (origin > fence) throw new ArrayIndexOutOfBoundsException("origin(" + origin + ") > fence(" + fence + ")");
        if (origin < 0) throw new ArrayIndexOutOfBoundsException("Array index out of range: " + origin);
        if (fence > arrayLength) throw new ArrayIndexOutOfBoundsException("Array index out of range: " + fence);
    }

    public static <T> Stream<T> ofArray(T[] array, int from, int to) {
        if (array == null) throw new NullPointerException();
        checkFromToBounds(array.length, from, to);
        return new RefPipe<>(new Src.Arr(array, from, to));
    }

    public static IntStream ofIntArray(int[] array, int from, int to) {
        if (array == null) throw new NullPointerException();
        checkFromToBounds(array.length, from, to);
        return new IntPipe(new Src.IntArr(array, from, to));
    }

    public static LongStream ofLongArray(long[] array, int from, int to) {
        if (array == null) throw new NullPointerException();
        checkFromToBounds(array.length, from, to);
        return new LongPipe(new Src.LongArr(array, from, to));
    }

    public static DoubleStream ofDoubleArray(double[] array, int from, int to) {
        if (array == null) throw new NullPointerException();
        checkFromToBounds(array.length, from, to);
        return new DoublePipe(new Src.DoubleArr(array, from, to));
    }

    /** A stream over a collection with the characteristics of its JDK spliterator. mod (may be
     *  null) reads the collection's modification count. */
    public static <T> Stream<T> ofCollection(Collection<T> c, int characteristics, int kind, IntSupplier mod) {
        return new RefPipe<>(new Src.Coll(c, characteristics, kind, mod));
    }
}

/*
 * rocq-jvm model of java.util.Arrays.asList, toString, equals and hashCode (clean-room,
 * Apache-2.0; from the Javadoc: asList is a fixed-size list backed by the array, writes go through
 * to the array; toString is "[a, b]" with String.valueOf of each element, "null" for a null array;
 * equals/hashCode as List.equals/List.hashCode of the elements).
 * The other static methods of Arrays (fill, copyOf, ...) are deliberately NOT declared here: the
 * machine resolves an invokestatic in this loaded class first and, when the method is not
 * declared, falls back to the Rocq model of java/util/Arrays (Jdk.v), so declaring only asList
 * does not shadow those models.  This class has no static initialiser.
 */
package java.util;

import java.util.function.Consumer;
import java.util.function.UnaryOperator;

public class Arrays {
    private Arrays() {
    }

    @SafeVarargs
    @SuppressWarnings("varargs")
    public static <T> List<T> asList(T... a) {
        return new ArrayList<>(a);
    }

    public static String toString(Object[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(String.valueOf(a[i]));
        }
        return b.append(']').toString();
    }

    public static String toString(int[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static String toString(long[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static boolean equals(Object[] a, Object[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null || a.length != a2.length) return false;
        for (int i = 0; i < a.length; i++) {
            Object x = a[i], y = a2[i];
            if (!(x == null ? y == null : x.equals(y))) return false;
        }
        return true;
    }

    public static boolean equals(int[] a, int[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null || a.length != a2.length) return false;
        for (int i = 0; i < a.length; i++) {
            if (a[i] != a2[i]) return false;
        }
        return true;
    }

    public static int hashCode(Object[] a) {
        if (a == null) return 0;
        int h = 1;
        for (Object e : a) h = 31 * h + (e == null ? 0 : e.hashCode());
        return h;
    }

    public static int hashCode(int[] a) {
        if (a == null) return 0;
        int h = 1;
        for (int e : a) h = 31 * h + e;
        return h;
    }

    // ---- sort: a stable merge sort (the JDK's TimSort is stable too, so the result is the same;
    //      only the sequence of compare calls differs) ----

    public static void sort(Object[] a) {
        sortRange(a, 0, a.length, null);
    }

    public static void sort(Object[] a, int fromIndex, int toIndex) {
        rangeCheck(a.length, fromIndex, toIndex);
        sortRange(a, fromIndex, toIndex, null);
    }

    public static <T> void sort(T[] a, Comparator<? super T> c) {
        sortRange(a, 0, a.length, c);
    }

    public static <T> void sort(T[] a, int fromIndex, int toIndex, Comparator<? super T> c) {
        rangeCheck(a.length, fromIndex, toIndex);
        sortRange(a, fromIndex, toIndex, c);
    }

    static void rangeCheck(int arrayLength, int fromIndex, int toIndex) {
        if (fromIndex > toIndex) throw new IllegalArgumentException("fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
        if (fromIndex < 0) throw new ArrayIndexOutOfBoundsException("Array index out of range: " + fromIndex);
        if (toIndex > arrayLength) throw new ArrayIndexOutOfBoundsException("Array index out of range: " + toIndex);
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    private static int cmp(Comparator c, Object x, Object y) {
        if (c == null && y != null && TreeMap.isJdkComparableX(x) && x.getClass() != y.getClass()) {
            // the bridge compareTo(Object) of String and the boxes casts its argument first
            if (!TreeMap.isJdkComparableX(y)) throw ModelStuck.unsupported("Arrays.sort: ClassCastException message for a user class");
            String a = y.getClass().getName(), b = x.getClass().getName();
            throw new ClassCastException("class " + a + " cannot be cast to class " + b + " (" + a + " and " + b
                + " are in module java.base of loader 'bootstrap')");
        }
        return (c == null) ? ((Comparable) x).compareTo(y) : c.compare(x, y);
    }

    @SuppressWarnings("rawtypes")
    static void sortRange(Object[] a, int lo, int hi, Comparator c) {
        int n = hi - lo;
        if (n < 2) return;
        Object[] tmp = new Object[n];
        mergeSort(a, tmp, lo, hi, c);
    }

    @SuppressWarnings("rawtypes")
    private static void mergeSort(Object[] a, Object[] tmp, int lo, int hi, Comparator c) {
        if (hi - lo < 2) return;
        int mid = (lo + hi) >>> 1;
        mergeSort(a, tmp, lo, mid, c);
        mergeSort(a, tmp, mid, hi, c);
        int i = lo, j = mid, k = 0;
        while (i < mid && j < hi) {
            if (cmp(c, a[j], a[i]) < 0) tmp[k++] = a[j++];
            else tmp[k++] = a[i++];
        }
        while (i < mid) tmp[k++] = a[i++];
        while (j < hi) tmp[k++] = a[j++];
        for (int m = 0; m < k; m++) a[lo + m] = tmp[m];
    }

    /** The list view (java.util.Arrays$ArrayList). */
    private static class ArrayList<E> extends AbstractList<E> implements RandomAccess, java.io.Serializable {
        private final E[] a;

        ArrayList(E[] array) {
            if (array == null) throw new NullPointerException();
            a = array;
        }

        public int size() {
            return a.length;
        }

        public Object[] toArray() {
            Object[] r = new Object[a.length];
            System.arraycopy(a, 0, r, 0, a.length);
            return r;
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] r) {
            int size = size();
            if (r.length < size) {
                Object[] n = AbstractCollection.newArrayLike(r, size);
                System.arraycopy(this.a, 0, n, 0, size);
                return (T[]) n;
            }
            System.arraycopy(this.a, 0, r, 0, size);
            if (r.length > size) r[size] = null;
            return r;
        }

        public E get(int index) {
            return a[index];
        }

        public E set(int index, E element) {
            E old = a[index];
            a[index] = element;
            return old;
        }

        public int indexOf(Object o) {
            E[] arr = a;
            if (o == null) {
                for (int i = 0; i < arr.length; i++) {
                    if (arr[i] == null) return i;
                }
            } else {
                for (int i = 0; i < arr.length; i++) {
                    if (o.equals(arr[i])) return i;
                }
            }
            return -1;
        }

        public boolean contains(Object o) {
            return indexOf(o) >= 0;
        }

        public void forEach(Consumer<? super E> action) {
            if (action == null) throw new NullPointerException();
            for (E e : a) action.accept(e);
        }

        public void replaceAll(UnaryOperator<E> operator) {
            if (operator == null) throw new NullPointerException();
            E[] arr = this.a;
            for (int i = 0; i < arr.length; i++) arr[i] = operator.apply(arr[i]);
        }

        /** Javadoc: sorts the backing array in place (stable). */
        public void sort(Comparator<? super E> c) {
            sortRange(a, 0, a.length, c);
        }

        public Iterator<E> iterator() {
            return new ArrayItr<>(a);
        }
    }

    private static class ArrayItr<E> implements Iterator<E> {
        private int cursor;
        private final E[] a;

        ArrayItr(E[] a) {
            this.a = a;
        }

        public boolean hasNext() {
            return cursor < a.length;
        }

        public E next() {
            int i = cursor;
            if (i >= a.length) throw new NoSuchElementException();
            cursor = i + 1;
            return a[i];
        }
    }
}

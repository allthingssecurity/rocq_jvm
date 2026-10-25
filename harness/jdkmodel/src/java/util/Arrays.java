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

        public void sort(Comparator<? super E> c) {
            throw ModelStuck.unsupported("Arrays.asList(..).sort");
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

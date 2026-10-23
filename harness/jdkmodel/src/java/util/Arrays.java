/*
 * rocq-jvm model of java.util.Arrays.asList ONLY (clean-room, Apache-2.0; from the Javadoc:
 * a fixed-size list backed by the array, writes go through to the array).
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

/*
 * rocq-jvm model of java.util.AbstractCollection (clean-room, Apache-2.0; written from the
 * Javadoc's description of each method in terms of iterator() and size()).
 */
package java.util;

public abstract class AbstractCollection<E> implements Collection<E> {
    protected AbstractCollection() {
    }

    public abstract Iterator<E> iterator();

    public abstract int size();

    public boolean isEmpty() {
        return size() == 0;
    }

    public boolean contains(Object o) {
        Iterator<E> it = iterator();
        if (o == null) {
            while (it.hasNext()) {
                if (it.next() == null) return true;
            }
        } else {
            while (it.hasNext()) {
                if (o.equals(it.next())) return true;
            }
        }
        return false;
    }

    /** Javadoc: an array of the elements in iterator order; the array has exactly as many
     *  slots as elements were returned by the iterator (size() is only a hint). */
    public Object[] toArray() {
        Object[] out = new Object[size()];
        Iterator<E> it = iterator();
        int n = 0;
        while (n < out.length) {
            if (!it.hasNext()) return copyObjects(out, n);
            out[n++] = it.next();
        }
        while (it.hasNext()) {
            if (n == out.length) out = copyObjects(out, n + (n >> 1) + 1);
            out[n++] = it.next();
        }
        return n == out.length ? out : copyObjects(out, n);
    }

    /** Only the case where the argument array is large enough is modelled; a larger result
     *  array of the argument's runtime type needs reflection (STUCK in the machine). */
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(T[] a) {
        int sz = size();
        if (a.length < sz) {
            T[] r = (T[]) newArrayLike(a, sz);
            Iterator<E> it = iterator();
            for (int i = 0; i < r.length; i++) {
                if (!it.hasNext()) throw ModelStuck.unsupported("toArray: collection shrank during iteration");
                r[i] = (T) it.next();
            }
            if (it.hasNext()) throw ModelStuck.unsupported("toArray: collection grew during iteration");
            return r;
        }
        Iterator<E> it = iterator();
        for (int i = 0; i < a.length; i++) {
            if (!it.hasNext()) {
                a[i] = null;
                return a;
            }
            a[i] = (T) it.next();
        }
        if (it.hasNext()) throw ModelStuck.unsupported("toArray: collection grew during iteration");
        return a;
    }

    public boolean add(E e) {
        throw new UnsupportedOperationException();
    }

    /** A new Object[n] holding the first min(n, src.length) elements of src. */
    static Object[] copyObjects(Object[] src, int n) {
        Object[] r = new Object[n];
        System.arraycopy(src, 0, r, 0, Math.min(n, src.length));
        return r;
    }

    /** A new array of a's runtime type and length n.  Object[], String[], Integer[] and Long[]
     *  are made directly; any other component type needs reflection (STUCK in the machine). */
    static Object[] newArrayLike(Object[] a, int n) {
        Class<?> c = a.getClass();
        if (c == Object[].class) return new Object[n];
        if (c == String[].class) return new String[n];
        if (c == Integer[].class) return new Integer[n];
        if (c == Long[].class) return new Long[n];
        return (Object[]) java.lang.reflect.Array.newInstance(c.getComponentType(), n);
    }

    public boolean remove(Object o) {
        Iterator<E> it = iterator();
        if (o == null) {
            while (it.hasNext()) {
                if (it.next() == null) {
                    it.remove();
                    return true;
                }
            }
        } else {
            while (it.hasNext()) {
                if (o.equals(it.next())) {
                    it.remove();
                    return true;
                }
            }
        }
        return false;
    }

    public boolean containsAll(Collection<?> c) {
        for (Object e : c) {
            if (!contains(e)) return false;
        }
        return true;
    }

    public boolean addAll(Collection<? extends E> c) {
        boolean changed = false;
        for (E e : c) {
            if (add(e)) changed = true;
        }
        return changed;
    }

    public boolean removeAll(Collection<?> c) {
        if (c == null) throw new NullPointerException();
        boolean changed = false;
        Iterator<?> it = iterator();
        while (it.hasNext()) {
            if (c.contains(it.next())) {
                it.remove();
                changed = true;
            }
        }
        return changed;
    }

    public boolean retainAll(Collection<?> c) {
        if (c == null) throw new NullPointerException();
        boolean changed = false;
        Iterator<E> it = iterator();
        while (it.hasNext()) {
            if (!c.contains(it.next())) {
                it.remove();
                changed = true;
            }
        }
        return changed;
    }

    public void clear() {
        Iterator<E> it = iterator();
        while (it.hasNext()) {
            it.next();
            it.remove();
        }
    }

    /** Javadoc: "[e1, e2]" with String.valueOf of each element, "(this Collection)" for a
     *  self-reference.  Element toString() is called directly (String.valueOf(Object) would
     *  need a callback the Rocq String model does not make). */
    public String toString() {
        Iterator<E> it = iterator();
        if (!it.hasNext()) return "[]";
        StringBuilder sb = new StringBuilder();
        sb.append('[');
        for (;;) {
            E e = it.next();
            sb.append(e == this ? "(this Collection)" : (e == null ? "null" : e.toString()));
            if (!it.hasNext()) return sb.append(']').toString();
            sb.append(',').append(' ');
        }
    }
}

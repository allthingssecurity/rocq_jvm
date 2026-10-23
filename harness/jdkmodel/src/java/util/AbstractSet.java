/* rocq-jvm model of java.util.AbstractSet (clean-room, Apache-2.0; from the Javadoc). */
package java.util;

public abstract class AbstractSet<E> extends AbstractCollection<E> implements Set<E> {
    protected AbstractSet() {
    }

    /** Javadoc: same size and containsAll; ClassCastException/NullPointerException -> false. */
    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Set)) return false;
        Collection<?> c = (Collection<?>) o;
        if (c.size() != size()) return false;
        try {
            return containsAll(c);
        } catch (ClassCastException | NullPointerException unused) {
            return false;
        }
    }

    /** Javadoc: sum of the element hash codes (null counts 0). */
    public int hashCode() {
        int h = 0;
        Iterator<E> it = iterator();
        while (it.hasNext()) {
            E e = it.next();
            if (e != null) h += e.hashCode();
        }
        return h;
    }

    /** Javadoc: iterates over the smaller of the two (this set if sizes are equal...):
     *  if this set has more elements than c, removes each element of c with remove(Object);
     *  otherwise iterates over this set and removes the elements c contains. */
    public boolean removeAll(Collection<?> c) {
        if (c == null) throw new NullPointerException();
        boolean changed = false;
        if (size() > c.size()) {
            for (Object e : c) {
                if (remove(e)) changed = true;
            }
        } else {
            Iterator<?> it = iterator();
            while (it.hasNext()) {
                if (c.contains(it.next())) {
                    it.remove();
                    changed = true;
                }
            }
        }
        return changed;
    }
}

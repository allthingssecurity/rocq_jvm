/*
 * rocq-jvm model of java.util.concurrent.ConcurrentSkipListSet (clean-room, Apache-2.0): a
 * navigable set over a ConcurrentNavigableMap (a ConcurrentSkipListMap or one of its sub maps)
 * from elements to Boolean.TRUE, as the JDK; its iterators and views are the map's key set's.
 * Not modelled: spliterator (and so stream: STUCK), serialization.
 */
package java.util.concurrent;

import java.util.AbstractSet;
import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Map;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;

public class ConcurrentSkipListSet<E> extends AbstractSet<E> implements NavigableSet<E>, Cloneable, java.io.Serializable {
    private static final long serialVersionUID = -2479143111061671589L;

    @SuppressWarnings("serial")
    private ConcurrentNavigableMap<E, Object> m;

    public ConcurrentSkipListSet() {
        m = new ConcurrentSkipListMap<E, Object>();
    }

    public ConcurrentSkipListSet(Comparator<? super E> comparator) {
        m = new ConcurrentSkipListMap<E, Object>(comparator);
    }

    public ConcurrentSkipListSet(Collection<? extends E> c) {
        m = new ConcurrentSkipListMap<E, Object>();
        if (c == null) throw new NullPointerException("Cannot invoke \"java.util.Collection.iterator()\" because \"c\" is null");
        addAll(c);
    }

    public ConcurrentSkipListSet(SortedSet<E> s) {
        if (s == null) throw new NullPointerException("Cannot invoke \"java.util.SortedSet.comparator()\" because \"s\" is null");
        m = new ConcurrentSkipListMap<E, Object>(s.comparator());
        addAll(s);
    }

    ConcurrentSkipListSet(ConcurrentNavigableMap<E, Object> m) {
        this.m = m;
    }

    @SuppressWarnings("unchecked")
    public ConcurrentSkipListSet<E> clone() {
        try {
            ConcurrentSkipListSet<E> clone = (ConcurrentSkipListSet<E>) super.clone();
            clone.m = new ConcurrentSkipListMap<E, Object>(m);
            return clone;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }

    public int size() { return m.size(); }

    public boolean isEmpty() { return m.isEmpty(); }

    public boolean contains(Object o) { return m.containsKey(o); }

    public boolean add(E e) { return m.putIfAbsent(e, Boolean.TRUE) == null; }

    public boolean remove(Object o) { return m.remove(o, Boolean.TRUE); }

    public void clear() { m.clear(); }

    public Iterator<E> iterator() { return m.navigableKeySet().iterator(); }

    public Iterator<E> descendingIterator() { return m.descendingKeySet().iterator(); }

    public boolean equals(Object o) {
        if (o == this) return true;
        if (!(o instanceof Set)) return false;
        Collection<?> c = (Collection<?>) o;
        try {
            return containsAll(c) && c.containsAll(this);
        } catch (ClassCastException | NullPointerException unused) {
            return false;
        }
    }

    public boolean removeAll(Collection<?> c) {
        if (c == null) throw new NullPointerException("Cannot invoke \"java.util.Collection.iterator()\" because \"c\" is null");
        boolean modified = false;
        for (Object e : c)
            if (remove(e)) modified = true;
        return modified;
    }

    public E lower(E e) { return m.lowerKey(e); }

    public E floor(E e) { return m.floorKey(e); }

    public E ceiling(E e) { return m.ceilingKey(e); }

    public E higher(E e) { return m.higherKey(e); }

    public E pollFirst() {
        Map.Entry<E, Object> e = m.pollFirstEntry();
        return (e == null) ? null : e.getKey();
    }

    public E pollLast() {
        Map.Entry<E, Object> e = m.pollLastEntry();
        return (e == null) ? null : e.getKey();
    }

    public Comparator<? super E> comparator() { return m.comparator(); }

    public E first() { return m.firstKey(); }

    public E last() { return m.lastKey(); }

    public NavigableSet<E> subSet(E fromElement, boolean fromInclusive, E toElement, boolean toInclusive) {
        return new ConcurrentSkipListSet<E>(m.subMap(fromElement, fromInclusive, toElement, toInclusive));
    }

    public NavigableSet<E> headSet(E toElement, boolean inclusive) {
        return new ConcurrentSkipListSet<E>(m.headMap(toElement, inclusive));
    }

    public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
        return new ConcurrentSkipListSet<E>(m.tailMap(fromElement, inclusive));
    }

    public NavigableSet<E> subSet(E fromElement, E toElement) { return subSet(fromElement, true, toElement, false); }

    public NavigableSet<E> headSet(E toElement) { return headSet(toElement, false); }

    public NavigableSet<E> tailSet(E fromElement) { return tailSet(fromElement, true); }

    public NavigableSet<E> descendingSet() {
        return new ConcurrentSkipListSet<E>(m.descendingMap());
    }
}

/*
 * rocq-jvm model of java.util.ImmutableCollections (clean-room, Apache-2.0): the classes behind
 * List.of/copyOf, Set.of/copyOf, Map.of/ofEntries/copyOf. Class names, null checks, exceptions and
 * their messages follow JDK 21.
 *
 * Iteration order of Set.of/Map.of with two or more elements depends on a per-JVM-run salt
 * (the JDK seeds it from System.nanoTime() at startup). The model takes the salt from the
 * environment (ModelEnv.seed(0) = the JDK's SALT32L, in [0, 2^32)), so a theorem holds for the
 * salt it names, and "for every salt" is a quantifier the theorem can state. HotSpot picks one
 * per run: differential tests compare only salt-independent results.
 */
package java.util;

import java.util.function.Predicate;
import java.util.function.UnaryOperator;

class ImmutableCollections {
    private ImmutableCollections() {
    }

    static final int EXPAND_FACTOR = 2;

    private static long saltCache = -1;

    /** The JDK's SALT32L (fixed for the run). */
    static long salt() {
        if (saltCache < 0) {
            saltCache = ModelEnv.seed(0) & 0xFFFFFFFFL;
        }
        return saltCache;
    }

    /** The JDK's REVERSE: the lowest salt bit decides the iteration direction. */
    static boolean reverse() {
        return (salt() & 1) == 0;
    }

    static final Object EMPTY = new Object();
    static final ListN<?> EMPTY_LIST = new ListN<>(new Object[0], false);
    static final ListN<?> EMPTY_LIST_NULLS = new ListN<>(new Object[0], true);
    static final SetN<?> EMPTY_SET = new SetN<>();
    static final MapN<?, ?> EMPTY_MAP = new MapN<>();

    static UnsupportedOperationException uoe() {
        return new UnsupportedOperationException();
    }

    static Object nonNull(Object o) {
        if (o == null) throw new NullPointerException();
        return o;
    }

    /** The NullPointerException of an implicit null check in the JDK code, with HotSpot's helpful
     *  message (JEP 358) for that bytecode, e.g. invoke("Object.equals(Object)", "o"). */
    static NullPointerException invokeOnNull(String method, String what) {
        return new NullPointerException("Cannot invoke \"" + method + "\" because \"" + what + "\" is null");
    }

    static NullPointerException lengthOfNull(String what) {
        return new NullPointerException("Cannot read the array length because \"" + what + "\" is null");
    }

    static IndexOutOfBoundsException checkIndexFail(int index, int length) {
        return new IndexOutOfBoundsException("Index " + index + " out of bounds for length " + length);
    }

    abstract static class AbstractImmutableCollection<E> extends AbstractCollection<E> {
        public boolean add(E e) { throw uoe(); }
        public boolean addAll(Collection<? extends E> c) { throw uoe(); }
        public void clear() { throw uoe(); }
        public boolean remove(Object o) { throw uoe(); }
        public boolean removeAll(Collection<?> c) { throw uoe(); }
        public boolean removeIf(Predicate<? super E> filter) { throw uoe(); }
        public boolean retainAll(Collection<?> c) { throw uoe(); }
    }

    @SuppressWarnings("unchecked")
    static <E> List<E> listCopy(Collection<? extends E> coll) {
        if (coll instanceof List12 || (coll instanceof ListN && !((ListN<?>) coll).allowNulls)) {
            return (List<E>) coll;
        } else if (coll == null) {
            throw invokeOnNull("java.util.Collection.isEmpty()", "coll");
        } else if (coll.isEmpty()) {
            return (List<E>) EMPTY_LIST;
        } else {
            return (List<E>) List.of(coll.toArray());
        }
    }

    @SuppressWarnings("unchecked")
    static <E> List<E> listFromArray(E... input) {
        Object[] tmp = new Object[input.length];
        for (int i = 0; i < input.length; i++) {
            tmp[i] = nonNull(input[i]);
        }
        return new ListN<>((E[]) tmp, false);
    }

    @SuppressWarnings("unchecked")
    static <E> List<E> listFromTrustedArray(Object... input) {
        for (Object o : input) nonNull(o);
        switch (input.length) {
            case 0: return (List<E>) EMPTY_LIST;
            case 1: return (List<E>) new List12<>(input[0]);
            case 2: return (List<E>) new List12<>(input[0], input[1]);
            default: return (List<E>) new ListN<>(input, false);
        }
    }

    @SuppressWarnings("unchecked")
    static <E> List<E> listFromTrustedArrayNullsAllowed(Object... input) {
        if (input.length == 0) return (List<E>) EMPTY_LIST_NULLS;
        return new ListN<>((E[]) input, true);
    }

    // ---------- lists ----------

    abstract static class AbstractImmutableList<E> extends AbstractImmutableCollection<E>
            implements List<E>, RandomAccess {
        public void add(int index, E element) { throw uoe(); }
        public boolean addAll(int index, Collection<? extends E> c) { throw uoe(); }
        public E remove(int index) { throw uoe(); }
        public void replaceAll(UnaryOperator<E> operator) { throw uoe(); }
        public E set(int index, E element) { throw uoe(); }
        public void sort(Comparator<? super E> c) { throw uoe(); }

        public List<E> subList(int fromIndex, int toIndex) {
            subListRangeCheck(fromIndex, toIndex, size());
            return SubList.fromList(this, fromIndex, toIndex);
        }

        static void subListRangeCheck(int fromIndex, int toIndex, int size) {
            if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex = " + fromIndex);
            if (toIndex > size) throw new IndexOutOfBoundsException("toIndex = " + toIndex);
            if (fromIndex > toIndex)
                throw new IllegalArgumentException("fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
        }

        public Iterator<E> iterator() {
            return new ListItr<E>(this, size());
        }

        public ListIterator<E> listIterator() {
            return listIterator(0);
        }

        public ListIterator<E> listIterator(int index) {
            int size = size();
            if (index < 0 || index > size) throw outOfBounds(index);
            return new ListItr<E>(this, size, index);
        }

        public boolean equals(Object o) {
            if (o == this) return true;
            if (!(o instanceof List)) return false;
            Iterator<?> oit = ((List<?>) o).iterator();
            for (int i = 0, s = size(); i < s; i++) {
                if (!oit.hasNext() || !Objects.equals(get(i), oit.next())) return false;
            }
            return !oit.hasNext();
        }

        public int hashCode() {
            int hash = 1;
            for (int i = 0, s = size(); i < s; i++) {
                hash = 31 * hash + Objects.hashCode(get(i));
            }
            return hash;
        }

        public boolean contains(Object o) {
            return indexOf(o) >= 0;
        }

        IndexOutOfBoundsException outOfBounds(int index) {
            return new IndexOutOfBoundsException("Index: " + index + " Size: " + size());
        }
    }

    static final class ListItr<E> implements ListIterator<E> {
        private final List<E> list;
        private final int size;
        private final boolean isListIterator;
        private int cursor;

        ListItr(List<E> list, int size) {
            this.list = list;
            this.size = size;
            this.cursor = 0;
            this.isListIterator = false;
        }

        ListItr(List<E> list, int size, int index) {
            this.list = list;
            this.size = size;
            this.cursor = index;
            this.isListIterator = true;
        }

        public boolean hasNext() {
            return cursor != size;
        }

        public E next() {
            int i = cursor;
            E next;
            try {
                next = list.get(i);
            } catch (IndexOutOfBoundsException e) {
                throw new NoSuchElementException();
            }
            cursor = i + 1;
            return next;
        }

        public void remove() { throw uoe(); }

        public boolean hasPrevious() {
            if (!isListIterator) throw uoe();
            return cursor != 0;
        }

        public E previous() {
            if (!isListIterator) throw uoe();
            int i = cursor - 1;
            E previous;
            try {
                previous = list.get(i);
            } catch (IndexOutOfBoundsException e) {
                throw new NoSuchElementException();
            }
            cursor = i;
            return previous;
        }

        public int nextIndex() {
            if (!isListIterator) throw uoe();
            return cursor;
        }

        public int previousIndex() {
            if (!isListIterator) throw uoe();
            return cursor - 1;
        }

        public void set(E e) { throw uoe(); }

        public void add(E e) { throw uoe(); }
    }

    static final class SubList<E> extends AbstractImmutableList<E> implements RandomAccess {
        private final AbstractImmutableList<E> root;
        private final int offset;
        private final int size;

        private SubList(AbstractImmutableList<E> root, int offset, int size) {
            this.root = root;
            this.offset = offset;
            this.size = size;
        }

        static <E> SubList<E> fromSubList(SubList<E> parent, int fromIndex, int toIndex) {
            return new SubList<>(parent.root, parent.offset + fromIndex, toIndex - fromIndex);
        }

        static <E> SubList<E> fromList(AbstractImmutableList<E> list, int fromIndex, int toIndex) {
            return new SubList<>(list, fromIndex, toIndex - fromIndex);
        }

        public E get(int index) {
            if (index < 0 || index >= size) throw checkIndexFail(index, size);
            return root.get(offset + index);
        }

        public int size() {
            return size;
        }

        public Iterator<E> iterator() {
            return new ListItr<>(this, size());
        }

        public ListIterator<E> listIterator(int index) {
            if (index < 0 || index > size) throw outOfBounds(index);
            return new ListItr<>(this, size(), index);
        }

        public List<E> subList(int fromIndex, int toIndex) {
            subListRangeCheck(fromIndex, toIndex, size);
            return SubList.fromSubList(this, fromIndex, toIndex);
        }

        private boolean allowNulls() {
            return root instanceof ListN && ((ListN<?>) root).allowNulls;
        }

        public int indexOf(Object o) {
            if (!allowNulls() && o == null) throw new NullPointerException();
            for (int i = 0, s = size(); i < s; i++) {
                if (Objects.equals(o, get(i))) return i;
            }
            return -1;
        }

        public int lastIndexOf(Object o) {
            if (!allowNulls() && o == null) throw new NullPointerException();
            for (int i = size() - 1; i >= 0; i--) {
                if (Objects.equals(o, get(i))) return i;
            }
            return -1;
        }

        public Object[] toArray() {
            Object[] array = new Object[size];
            for (int i = 0; i < size; i++) array[i] = get(i);
            return array;
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            T[] array = a.length >= size ? a
                : (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
            for (int i = 0; i < size; i++) array[i] = (T) get(i);
            if (array.length > size) array[size] = null;
            return array;
        }
    }

    static final class List12<E> extends AbstractImmutableList<E> {
        private final E e0;
        private final Object e1;

        List12(E e0) {
            this.e0 = (E) nonNull(e0);
            this.e1 = EMPTY;
        }

        List12(E e0, E e1) {
            this.e0 = (E) nonNull(e0);
            this.e1 = nonNull(e1);
        }

        public int size() {
            return e1 != EMPTY ? 2 : 1;
        }

        public boolean isEmpty() {
            return false;
        }

        @SuppressWarnings("unchecked")
        public E get(int index) {
            if (index == 0) return e0;
            if (index == 1 && e1 != EMPTY) return (E) e1;
            throw outOfBounds(index);
        }

        public int indexOf(Object o) {
            nonNull(o);
            if (o.equals(e0)) return 0;
            if (e1 != EMPTY && o.equals(e1)) return 1;
            return -1;
        }

        public int lastIndexOf(Object o) {
            nonNull(o);
            if (e1 != EMPTY && o.equals(e1)) return 1;
            if (o.equals(e0)) return 0;
            return -1;
        }

        public Object[] toArray() {
            if (e1 == EMPTY) return new Object[] {e0};
            return new Object[] {e0, e1};
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            int size = size();
            T[] array = a.length >= size ? a
                : (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
            array[0] = (T) e0;
            if (size == 2) array[1] = (T) e1;
            if (array.length > size) array[size] = null;
            return array;
        }
    }

    static final class ListN<E> extends AbstractImmutableList<E> {
        private final E[] elements;
        final boolean allowNulls;

        ListN(E[] elements, boolean allowNulls) {
            this.elements = elements;
            this.allowNulls = allowNulls;
        }

        public boolean isEmpty() {
            return elements.length == 0;
        }

        public int size() {
            return elements.length;
        }

        public E get(int index) {
            return elements[index];
        }

        public Object[] toArray() {
            Object[] r = new Object[elements.length];
            System.arraycopy(elements, 0, r, 0, elements.length);
            return r;
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            int size = elements.length;
            if (a.length < size) {
                T[] r = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
                System.arraycopy(elements, 0, r, 0, size);
                return r;
            }
            System.arraycopy(elements, 0, a, 0, size);
            if (a.length > size) a[size] = null;
            return a;
        }

        public int indexOf(Object o) {
            if (!allowNulls && o == null) throw new NullPointerException();
            Object[] es = elements;
            for (int i = 0; i < es.length; i++) {
                if (Objects.equals(o, es[i])) return i;
            }
            return -1;
        }

        public int lastIndexOf(Object o) {
            if (!allowNulls && o == null) throw new NullPointerException();
            Object[] es = elements;
            for (int i = es.length - 1; i >= 0; i--) {
                if (Objects.equals(o, es[i])) return i;
            }
            return -1;
        }
    }

    // ---------- sets ----------

    abstract static class AbstractImmutableSet<E> extends AbstractImmutableCollection<E> implements Set<E> {
        public boolean equals(Object o) {
            if (o == this) return true;
            if (!(o instanceof Set)) return false;
            Collection<?> c = (Collection<?>) o;
            if (c.size() != size()) return false;
            for (Object e : c) {
                if (e == null || !contains(e)) return false;
            }
            return true;
        }

        public abstract int hashCode();
    }

    static final class Set12<E> extends AbstractImmutableSet<E> {
        private final E e0;
        private final Object e1;

        Set12(E e0) {
            this.e0 = (E) nonNull(e0);
            this.e1 = EMPTY;
        }

        Set12(E e0, E e1) {
            Object x = nonNull(e1);
            if (e0 == null) throw invokeOnNull("Object.equals(Object)", "e0");
            if (e0.equals(x)) {
                throw new IllegalArgumentException("duplicate element: " + e0);
            }
            this.e0 = e0;
            this.e1 = e1;
        }

        public int size() {
            return (e1 == EMPTY) ? 1 : 2;
        }

        public boolean isEmpty() {
            return false;
        }

        public boolean contains(Object o) {
            if (o == null) throw invokeOnNull("Object.equals(Object)", "o");
            return o.equals(e0) || e1.equals(o);
        }

        public int hashCode() {
            return e0.hashCode() + (e1 == EMPTY ? 0 : e1.hashCode());
        }

        public Iterator<E> iterator() {
            return new Set12Itr();
        }

        private final class Set12Itr implements Iterator<E> {
            private int idx = (e1 == EMPTY) ? 1 : 2;

            public boolean hasNext() {
                return idx > 0;
            }

            @SuppressWarnings("unchecked")
            public E next() {
                if (idx == 1) {
                    idx = 0;
                    return (e1 == EMPTY || reverse()) ? e0 : (E) e1;
                } else if (idx == 2) {
                    idx = 1;
                    return reverse() ? (E) e1 : e0;
                } else {
                    throw new NoSuchElementException();
                }
            }
        }

        public Object[] toArray() {
            if (e1 == EMPTY) return new Object[] {e0};
            if (reverse()) return new Object[] {e1, e0};
            return new Object[] {e0, e1};
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            int size = size();
            T[] array = a.length >= size ? a
                : (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
            if (size == 1) {
                array[0] = (T) e0;
            } else if (reverse()) {
                array[0] = (T) e1;
                array[1] = (T) e0;
            } else {
                array[0] = (T) e0;
                array[1] = (T) e1;
            }
            if (array.length > size) array[size] = null;
            return array;
        }
    }

    static final class SetN<E> extends AbstractImmutableSet<E> {
        final E[] elements;
        final int size;

        @SuppressWarnings("unchecked")
        SetN(E... input) {
            size = input.length;
            elements = (E[]) new Object[EXPAND_FACTOR * input.length];
            for (int i = 0; i < input.length; i++) {
                E e = input[i];
                if (e == null) throw invokeOnNull("Object.hashCode()", "pe");
                int idx = probe(e);
                if (idx >= 0) {
                    throw new IllegalArgumentException("duplicate element: " + e);
                }
                elements[-(idx + 1)] = e;
            }
        }

        public int size() {
            return size;
        }

        public boolean isEmpty() {
            return size == 0;
        }

        public boolean contains(Object o) {
            nonNull(o);
            return size > 0 && probe(o) >= 0;
        }

        private final class SetNItr implements Iterator<E> {
            private int remaining;
            private int idx;

            SetNItr() {
                remaining = size;
                idx = (int) ((salt() * elements.length) >>> 32);
            }

            public boolean hasNext() {
                return remaining > 0;
            }

            public E next() {
                if (remaining <= 0) throw new NoSuchElementException();
                E element;
                int i = idx;
                int len = elements.length;
                boolean rev = reverse();
                do {
                    if (rev) {
                        if (++i >= len) i = 0;
                    } else {
                        if (--i < 0) i = len - 1;
                    }
                } while ((element = elements[i]) == null);
                idx = i;
                remaining--;
                return element;
            }
        }

        public Iterator<E> iterator() {
            return new SetNItr();
        }

        public int hashCode() {
            int h = 0;
            for (E e : elements) {
                if (e != null) h += e.hashCode();
            }
            return h;
        }

        private int probe(Object pe) {
            int idx = Math.floorMod(pe.hashCode(), elements.length);
            while (true) {
                E ee = elements[idx];
                if (ee == null) return -idx - 1;
                if (pe.equals(ee)) return idx;
                if (++idx == elements.length) idx = 0;
            }
        }

        public Object[] toArray() {
            Object[] array = new Object[size];
            Iterator<E> it = iterator();
            for (int i = 0; i < size; i++) array[i] = it.next();
            return array;
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            T[] array = a.length >= size ? a
                : (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
            Iterator<E> it = iterator();
            for (int i = 0; i < size; i++) array[i] = (T) it.next();
            if (array.length > size) array[size] = null;
            return array;
        }
    }

    // ---------- maps ----------

    abstract static class AbstractImmutableMap<K, V> extends AbstractMap<K, V> {
        public void clear() { throw uoe(); }
        public V compute(K key, java.util.function.BiFunction<? super K, ? super V, ? extends V> rf) { throw uoe(); }
        public V computeIfAbsent(K key, java.util.function.Function<? super K, ? extends V> mf) { throw uoe(); }
        public V computeIfPresent(K key, java.util.function.BiFunction<? super K, ? super V, ? extends V> rf) { throw uoe(); }
        public V merge(K key, V value, java.util.function.BiFunction<? super V, ? super V, ? extends V> rf) { throw uoe(); }
        public V put(K key, V value) { throw uoe(); }
        public void putAll(Map<? extends K, ? extends V> m) { throw uoe(); }
        public V putIfAbsent(K key, V value) { throw uoe(); }
        public V remove(Object key) { throw uoe(); }
        public boolean remove(Object key, Object value) { throw uoe(); }
        public V replace(K key, V value) { throw uoe(); }
        public boolean replace(K key, V oldValue, V newValue) { throw uoe(); }
        public void replaceAll(java.util.function.BiFunction<? super K, ? super V, ? extends V> f) { throw uoe(); }

        public V getOrDefault(Object key, V defaultValue) {
            V v;
            return ((v = get(key)) != null) ? v : defaultValue;
        }
    }

    static final class Map1<K, V> extends AbstractImmutableMap<K, V> {
        private final K k0;
        private final V v0;

        Map1(K k0, V v0) {
            this.k0 = (K) nonNull(k0);
            this.v0 = (V) nonNull(v0);
        }

        public Set<Map.Entry<K, V>> entrySet() {
            return Set.of(new KeyValueHolder<>(k0, v0));
        }

        public V get(Object o) {
            if (o == null) throw invokeOnNull("Object.equals(Object)", "o");
            return o.equals(k0) ? v0 : null;
        }

        public boolean containsKey(Object o) {
            if (o == null) throw invokeOnNull("Object.equals(Object)", "o");
            return o.equals(k0);
        }

        public boolean containsValue(Object o) {
            if (o == null) throw invokeOnNull("Object.equals(Object)", "o");
            return o.equals(v0);
        }

        public int size() {
            return 1;
        }

        public boolean isEmpty() {
            return false;
        }

        public int hashCode() {
            return k0.hashCode() ^ v0.hashCode();
        }
    }

    static final class MapN<K, V> extends AbstractImmutableMap<K, V> {
        final Object[] table; // key, value pairs
        final int size;

        MapN(Object... input) {
            if ((input.length & 1) != 0) throw new InternalError("length is odd");
            size = input.length >> 1;
            int len = EXPAND_FACTOR * input.length;
            len = (len + 1) & ~1;
            table = new Object[len];
            for (int i = 0; i < input.length; i += 2) {
                Object k = nonNull(input[i]);
                Object v = nonNull(input[i + 1]);
                int idx = probe(k);
                if (idx >= 0) {
                    throw new IllegalArgumentException("duplicate key: " + k);
                }
                int dest = -(idx + 1);
                table[dest] = k;
                table[dest + 1] = v;
            }
        }

        public boolean containsKey(Object o) {
            nonNull(o);
            return size > 0 && probe(o) >= 0;
        }

        public boolean containsValue(Object o) {
            nonNull(o);
            for (int i = 1; i < table.length; i += 2) {
                Object v = table[i];
                if (v != null && o.equals(v)) return true;
            }
            return false;
        }

        public int hashCode() {
            int hash = 0;
            for (int i = 0; i < table.length; i += 2) {
                Object k = table[i];
                if (k != null) hash += k.hashCode() ^ table[i + 1].hashCode();
            }
            return hash;
        }

        @SuppressWarnings("unchecked")
        public V get(Object o) {
            if (size == 0) {
                nonNull(o);
                return null;
            }
            if (o == null) throw invokeOnNull("Object.hashCode()", "pk");
            int i = probe(o);
            return i >= 0 ? (V) table[i + 1] : null;
        }

        public int size() {
            return size;
        }

        public boolean isEmpty() {
            return size == 0;
        }

        final class MapNItr implements Iterator<Map.Entry<K, V>> {
            private int remaining;
            private int idx;

            MapNItr() {
                remaining = size;
                idx = (int) ((salt() * (table.length >> 1)) >>> 32) << 1;
            }

            public boolean hasNext() {
                return remaining > 0;
            }

            private int nextIndex() {
                int i = idx;
                if (reverse()) {
                    if ((i += 2) >= table.length) i = 0;
                } else {
                    if ((i -= 2) < 0) i = table.length - 2;
                }
                return idx = i;
            }

            @SuppressWarnings("unchecked")
            public Map.Entry<K, V> next() {
                if (remaining <= 0) throw new NoSuchElementException();
                int i;
                while (table[i = nextIndex()] == null) {
                }
                Map.Entry<K, V> e = new KeyValueHolder<>((K) table[i], (V) table[i + 1]);
                remaining--;
                return e;
            }
        }

        public Set<Map.Entry<K, V>> entrySet() {
            return new AbstractSet<Map.Entry<K, V>>() {
                public int size() {
                    return MapN.this.size;
                }

                public Iterator<Map.Entry<K, V>> iterator() {
                    return new MapNItr();
                }
            };
        }

        private int probe(Object pk) {
            int idx = Math.floorMod(pk.hashCode(), table.length >> 1) << 1;
            while (true) {
                Object ek = table[idx];
                if (ek == null) return -idx - 1;
                if (pk.equals(ek)) return idx;
                if ((idx += 2) == table.length) idx = 0;
            }
        }
    }
}

/** java.util.KeyValueHolder: the entries of Map.entry and of the immutable maps. */
final class KeyValueHolder<K, V> implements Map.Entry<K, V> {
    final K key;
    final V value;

    KeyValueHolder(K k, V v) {
        key = (K) ImmutableCollections.nonNull(k);
        value = (V) ImmutableCollections.nonNull(v);
    }

    public K getKey() {
        return key;
    }

    public V getValue() {
        return value;
    }

    public V setValue(V value) {
        throw new UnsupportedOperationException("not supported");
    }

    public boolean equals(Object o) {
        return o instanceof Map.Entry<?, ?> e && key.equals(e.getKey()) && value.equals(e.getValue());
    }

    public int hashCode() {
        return key.hashCode() ^ value.hashCode();
    }

    public String toString() {
        return key + "=" + value;
    }
}

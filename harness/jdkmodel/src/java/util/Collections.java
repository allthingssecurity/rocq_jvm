/*
 * rocq-jvm model of part of java.util.Collections (clean-room, Apache-2.0; from the Javadoc).
 * Modelled: emptyIterator, emptyList, emptySet, emptyMap, singletonList, singleton,
 * unmodifiableCollection/List/Set/Map.  Everything else in Collections is not modelled
 * (calls are STUCK: the class is loaded but has no such method, and there is no Rocq model).
 * The EMPTY_* constants are created on first use (as the JDK's static fields are).
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

public class Collections {
    private Collections() {
    }

    @SuppressWarnings("rawtypes")
    public static final List EMPTY_LIST = new EmptyList<>();
    @SuppressWarnings("rawtypes")
    public static final Set EMPTY_SET = new EmptySet<>();
    @SuppressWarnings("rawtypes")
    public static final Map EMPTY_MAP = new EmptyMap<>();

    static boolean eq(Object a, Object b) {
        return a == null ? b == null : a.equals(b);
    }

    // ---- empty ----

    @SuppressWarnings("unchecked")
    public static <T> Iterator<T> emptyIterator() {
        return (Iterator<T>) EmptyIterator.EMPTY_ITERATOR;
    }

    private static class EmptyIterator<E> implements Iterator<E> {
        static final EmptyIterator<Object> EMPTY_ITERATOR = new EmptyIterator<>();

        public boolean hasNext() {
            return false;
        }

        public E next() {
            throw new NoSuchElementException();
        }

        public void remove() {
            throw new IllegalStateException();
        }

        public void forEachRemaining(Consumer<? super E> action) {
            if (action == null) throw new NullPointerException();
        }
    }

    @SuppressWarnings("unchecked")
    public static final <T> List<T> emptyList() {
        return (List<T>) EMPTY_LIST;
    }

    @SuppressWarnings("unchecked")
    public static final <T> Set<T> emptySet() {
        return (Set<T>) EMPTY_SET;
    }

    @SuppressWarnings("unchecked")
    public static final <K, V> Map<K, V> emptyMap() {
        return (Map<K, V>) EMPTY_MAP;
    }

    private static class EmptyList<E> extends AbstractList<E> implements RandomAccess, java.io.Serializable {
        public Iterator<E> iterator() {
            return emptyIterator();
        }

        public ListIterator<E> listIterator() {
            return EmptyListIterator.instance();
        }

        public int size() {
            return 0;
        }

        public boolean isEmpty() {
            return true;
        }

        public void clear() {
        }

        public boolean contains(Object obj) {
            return false;
        }

        public boolean containsAll(Collection<?> c) {
            return c.isEmpty();
        }

        public Object[] toArray() {
            return new Object[0];
        }

        public <T> T[] toArray(T[] a) {
            if (a.length > 0) a[0] = null;
            return a;
        }

        public E get(int index) {
            throw new IndexOutOfBoundsException();
        }

        public boolean equals(Object o) {
            return (o instanceof List) && ((List<?>) o).isEmpty();
        }

        public int hashCode() {
            return 1;
        }

        public boolean removeIf(Predicate<? super E> filter) {
            if (filter == null) throw new NullPointerException();
            return false;
        }

        public void replaceAll(UnaryOperator<E> operator) {
            if (operator == null) throw new NullPointerException();
        }

        public void sort(Comparator<? super E> c) {
        }

        public void forEach(Consumer<? super E> action) {
            if (action == null) throw new NullPointerException();
        }
    }

    private static final class EmptyListIterator<E> extends EmptyIterator<E> implements ListIterator<E> {
        static final EmptyListIterator<Object> EMPTY = new EmptyListIterator<>();

        @SuppressWarnings("unchecked")
        static <T> ListIterator<T> instance() {
            return (ListIterator<T>) EMPTY;
        }

        public boolean hasPrevious() {
            return false;
        }

        public E previous() {
            throw new NoSuchElementException();
        }

        public int nextIndex() {
            return 0;
        }

        public int previousIndex() {
            return -1;
        }

        public void set(E e) {
            throw new IllegalStateException();
        }

        public void add(E e) {
            throw new UnsupportedOperationException();
        }
    }

    private static class EmptySet<E> extends AbstractSet<E> implements java.io.Serializable {
        public Iterator<E> iterator() {
            return emptyIterator();
        }

        public int size() {
            return 0;
        }

        public boolean isEmpty() {
            return true;
        }

        public void clear() {
        }

        public boolean contains(Object obj) {
            return false;
        }

        public boolean containsAll(Collection<?> c) {
            return c.isEmpty();
        }

        public Object[] toArray() {
            return new Object[0];
        }

        public <T> T[] toArray(T[] a) {
            if (a.length > 0) a[0] = null;
            return a;
        }

        public boolean removeIf(Predicate<? super E> filter) {
            if (filter == null) throw new NullPointerException();
            return false;
        }

        public void forEach(Consumer<? super E> action) {
            if (action == null) throw new NullPointerException();
        }

        public int hashCode() {
            return 0;
        }
    }

    private static class EmptyMap<K, V> extends AbstractMap<K, V> implements java.io.Serializable {
        public int size() {
            return 0;
        }

        public boolean isEmpty() {
            return true;
        }

        public void clear() {
        }

        public boolean containsKey(Object key) {
            return false;
        }

        public boolean containsValue(Object value) {
            return false;
        }

        public V get(Object key) {
            return null;
        }

        public Set<K> keySet() {
            return emptySet();
        }

        public Collection<V> values() {
            return emptySet();
        }

        public Set<Map.Entry<K, V>> entrySet() {
            return emptySet();
        }

        public boolean equals(Object o) {
            return (o instanceof Map) && ((Map<?, ?>) o).isEmpty();
        }

        public int hashCode() {
            return 0;
        }

        public V getOrDefault(Object k, V defaultValue) {
            return defaultValue;
        }

        public void forEach(BiConsumer<? super K, ? super V> action) {
            if (action == null) throw new NullPointerException();
        }

        public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
            if (function == null) throw new NullPointerException();
        }

        public V putIfAbsent(K key, V value) {
            throw new UnsupportedOperationException();
        }

        public boolean remove(Object key, Object value) {
            throw new UnsupportedOperationException();
        }

        public boolean replace(K key, V oldValue, V newValue) {
            throw new UnsupportedOperationException();
        }

        public V replace(K key, V value) {
            throw new UnsupportedOperationException();
        }

        public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
            throw new UnsupportedOperationException();
        }

        public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
            throw new UnsupportedOperationException();
        }

        public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
            throw new UnsupportedOperationException();
        }

        public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
            throw new UnsupportedOperationException();
        }
    }

    // ---- singletons ----

    static <E> Iterator<E> singletonIterator(final E e) {
        return new Iterator<E>() {
            private boolean more = true;

            public boolean hasNext() {
                return more;
            }

            public E next() {
                if (more) {
                    more = false;
                    return e;
                }
                throw new NoSuchElementException();
            }

            public void remove() {
                throw new UnsupportedOperationException();
            }

            public void forEachRemaining(Consumer<? super E> action) {
                if (action == null) throw new NullPointerException();
                if (more) {
                    more = false;
                    action.accept(e);
                }
            }
        };
    }

    public static <T> Set<T> singleton(T o) {
        return new SingletonSet<>(o);
    }

    private static class SingletonSet<E> extends AbstractSet<E> implements java.io.Serializable {
        private final E element;

        SingletonSet(E e) {
            element = e;
        }

        public Iterator<E> iterator() {
            return singletonIterator(element);
        }

        public int size() {
            return 1;
        }

        public boolean contains(Object o) {
            return eq(o, element);
        }

        public void forEach(Consumer<? super E> action) {
            action.accept(element);
        }

        public boolean removeIf(Predicate<? super E> filter) {
            throw new UnsupportedOperationException();
        }

        public int hashCode() {
            return AbstractMap.hashOf(element);
        }
    }

    public static <T> List<T> singletonList(T o) {
        return new SingletonList<>(o);
    }

    private static class SingletonList<E> extends AbstractList<E> implements RandomAccess, java.io.Serializable {
        private final E element;

        SingletonList(E obj) {
            element = obj;
        }

        public Iterator<E> iterator() {
            return singletonIterator(element);
        }

        public int size() {
            return 1;
        }

        public boolean contains(Object obj) {
            return eq(obj, element);
        }

        public E get(int index) {
            if (index != 0) throw new IndexOutOfBoundsException();
            return element;
        }

        public void forEach(Consumer<? super E> action) {
            action.accept(element);
        }

        public boolean removeIf(Predicate<? super E> filter) {
            throw new UnsupportedOperationException();
        }

        public void replaceAll(UnaryOperator<E> operator) {
            throw new UnsupportedOperationException();
        }

        public void sort(Comparator<? super E> c) {
        }

        public int hashCode() {
            return 31 + AbstractMap.hashOf(element);
        }
    }

    // ---- unmodifiable views ----

    @SuppressWarnings("unchecked")
    public static <T> Collection<T> unmodifiableCollection(Collection<? extends T> c) {
        if (c.getClass() == UnmodifiableCollection.class) return (Collection<T>) c;
        return new UnmodifiableCollection<>(c);
    }

    static class UnmodifiableCollection<E> implements Collection<E>, java.io.Serializable {
        final Collection<? extends E> c;

        UnmodifiableCollection(Collection<? extends E> c) {
            if (c == null) throw new NullPointerException();
            this.c = c;
        }

        public int size() {
            return c.size();
        }

        public boolean isEmpty() {
            return c.isEmpty();
        }

        public boolean contains(Object o) {
            return c.contains(o);
        }

        public Object[] toArray() {
            return c.toArray();
        }

        public <T> T[] toArray(T[] a) {
            return c.toArray(a);
        }

        public String toString() {
            return c.toString();
        }

        public Iterator<E> iterator() {
            return new Iterator<E>() {
                private final Iterator<? extends E> i = c.iterator();

                public boolean hasNext() {
                    return i.hasNext();
                }

                public E next() {
                    return i.next();
                }

                public void remove() {
                    throw new UnsupportedOperationException();
                }

                public void forEachRemaining(Consumer<? super E> action) {
                    i.forEachRemaining(action);
                }
            };
        }

        public boolean add(E e) {
            throw new UnsupportedOperationException();
        }

        public boolean remove(Object o) {
            throw new UnsupportedOperationException();
        }

        public boolean containsAll(Collection<?> coll) {
            return c.containsAll(coll);
        }

        public boolean addAll(Collection<? extends E> coll) {
            throw new UnsupportedOperationException();
        }

        public boolean removeAll(Collection<?> coll) {
            throw new UnsupportedOperationException();
        }

        public boolean retainAll(Collection<?> coll) {
            throw new UnsupportedOperationException();
        }

        public void clear() {
            throw new UnsupportedOperationException();
        }

        @SuppressWarnings("unchecked")
        public void forEach(Consumer<? super E> action) {
            ((Collection<E>) c).forEach(action);
        }

        public boolean removeIf(Predicate<? super E> filter) {
            throw new UnsupportedOperationException();
        }
    }

    @SuppressWarnings("unchecked")
    public static <T> Set<T> unmodifiableSet(Set<? extends T> s) {
        if (s.getClass() == UnmodifiableSet.class) return (Set<T>) s;
        return new UnmodifiableSet<>(s);
    }

    static class UnmodifiableSet<E> extends UnmodifiableCollection<E> implements Set<E>, java.io.Serializable {
        UnmodifiableSet(Set<? extends E> s) {
            super(s);
        }

        public boolean equals(Object o) {
            return o == this || c.equals(o);
        }

        public int hashCode() {
            return c.hashCode();
        }
    }

    @SuppressWarnings("unchecked")
    public static <T> List<T> unmodifiableList(List<? extends T> list) {
        if (list.getClass() == UnmodifiableList.class || list.getClass() == UnmodifiableRandomAccessList.class) {
            return (List<T>) list;
        }
        return (list instanceof RandomAccess) ? new UnmodifiableRandomAccessList<>(list) : new UnmodifiableList<>(list);
    }

    static class UnmodifiableList<E> extends UnmodifiableCollection<E> implements List<E> {
        final List<? extends E> list;

        UnmodifiableList(List<? extends E> list) {
            super(list);
            this.list = list;
        }

        public boolean equals(Object o) {
            return o == this || list.equals(o);
        }

        public int hashCode() {
            return list.hashCode();
        }

        public E get(int index) {
            return list.get(index);
        }

        public E set(int index, E element) {
            throw new UnsupportedOperationException();
        }

        public void add(int index, E element) {
            throw new UnsupportedOperationException();
        }

        public E remove(int index) {
            throw new UnsupportedOperationException();
        }

        public int indexOf(Object o) {
            return list.indexOf(o);
        }

        public int lastIndexOf(Object o) {
            return list.lastIndexOf(o);
        }

        public boolean addAll(int index, Collection<? extends E> c) {
            throw new UnsupportedOperationException();
        }

        public void replaceAll(UnaryOperator<E> operator) {
            throw new UnsupportedOperationException();
        }

        public void sort(Comparator<? super E> c) {
            throw new UnsupportedOperationException();
        }

        public ListIterator<E> listIterator() {
            return listIterator(0);
        }

        public ListIterator<E> listIterator(final int index) {
            return new ListIterator<E>() {
                private final ListIterator<? extends E> i = list.listIterator(index);

                public boolean hasNext() {
                    return i.hasNext();
                }

                public E next() {
                    return i.next();
                }

                public boolean hasPrevious() {
                    return i.hasPrevious();
                }

                public E previous() {
                    return i.previous();
                }

                public int nextIndex() {
                    return i.nextIndex();
                }

                public int previousIndex() {
                    return i.previousIndex();
                }

                public void remove() {
                    throw new UnsupportedOperationException();
                }

                public void set(E e) {
                    throw new UnsupportedOperationException();
                }

                public void add(E e) {
                    throw new UnsupportedOperationException();
                }

                public void forEachRemaining(Consumer<? super E> action) {
                    i.forEachRemaining(action);
                }
            };
        }

        public List<E> subList(int fromIndex, int toIndex) {
            return new UnmodifiableList<>(list.subList(fromIndex, toIndex));
        }
    }

    static class UnmodifiableRandomAccessList<E> extends UnmodifiableList<E> implements RandomAccess {
        UnmodifiableRandomAccessList(List<? extends E> list) {
            super(list);
        }

        public List<E> subList(int fromIndex, int toIndex) {
            return new UnmodifiableRandomAccessList<>(list.subList(fromIndex, toIndex));
        }
    }

    @SuppressWarnings("unchecked")
    public static <K, V> Map<K, V> unmodifiableMap(Map<? extends K, ? extends V> m) {
        if (m.getClass() == UnmodifiableMap.class) return (Map<K, V>) m;
        return new UnmodifiableMap<>(m);
    }

    private static class UnmodifiableMap<K, V> implements Map<K, V>, java.io.Serializable {
        private final Map<? extends K, ? extends V> m;
        private transient Set<K> keySet;
        private transient Set<Map.Entry<K, V>> entrySet;
        private transient Collection<V> values;

        UnmodifiableMap(Map<? extends K, ? extends V> m) {
            if (m == null) throw new NullPointerException();
            this.m = m;
        }

        public int size() {
            return m.size();
        }

        public boolean isEmpty() {
            return m.isEmpty();
        }

        public boolean containsKey(Object key) {
            return m.containsKey(key);
        }

        public boolean containsValue(Object val) {
            return m.containsValue(val);
        }

        public V get(Object key) {
            return m.get(key);
        }

        public V put(K key, V value) {
            throw new UnsupportedOperationException();
        }

        public V remove(Object key) {
            throw new UnsupportedOperationException();
        }

        public void putAll(Map<? extends K, ? extends V> map) {
            throw new UnsupportedOperationException();
        }

        public void clear() {
            throw new UnsupportedOperationException();
        }

        public Set<K> keySet() {
            if (keySet == null) keySet = unmodifiableSet(m.keySet());
            return keySet;
        }

        @SuppressWarnings({"unchecked", "rawtypes"})
        public Set<Map.Entry<K, V>> entrySet() {
            if (entrySet == null) entrySet = new UnmodifiableEntrySet<>((Set) m.entrySet());
            return entrySet;
        }

        public Collection<V> values() {
            if (values == null) values = unmodifiableCollection(m.values());
            return values;
        }

        public boolean equals(Object o) {
            return o == this || m.equals(o);
        }

        public int hashCode() {
            return m.hashCode();
        }

        public String toString() {
            return m.toString();
        }

        @SuppressWarnings("unchecked")
        public V getOrDefault(Object k, V defaultValue) {
            return ((Map<K, V>) m).getOrDefault(k, defaultValue);
        }

        @SuppressWarnings("unchecked")
        public void forEach(BiConsumer<? super K, ? super V> action) {
            ((Map<K, V>) m).forEach(action);
        }

        public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
            throw new UnsupportedOperationException();
        }

        public V putIfAbsent(K key, V value) {
            throw new UnsupportedOperationException();
        }

        public boolean remove(Object key, Object value) {
            throw new UnsupportedOperationException();
        }

        public boolean replace(K key, V oldValue, V newValue) {
            throw new UnsupportedOperationException();
        }

        public V replace(K key, V value) {
            throw new UnsupportedOperationException();
        }

        public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
            throw new UnsupportedOperationException();
        }

        public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
            throw new UnsupportedOperationException();
        }

        public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
            throw new UnsupportedOperationException();
        }

        public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
            throw new UnsupportedOperationException();
        }

        /** Entries are wrapped so that setValue throws UnsupportedOperationException. */
        static class UnmodifiableEntrySet<K, V> extends UnmodifiableSet<Map.Entry<K, V>> {
            UnmodifiableEntrySet(Set<? extends Map.Entry<? extends K, ? extends V>> s) {
                super((Set) s);
            }

            public Iterator<Map.Entry<K, V>> iterator() {
                return new Iterator<Map.Entry<K, V>>() {
                    private final Iterator<? extends Map.Entry<? extends K, ? extends V>> i =
                        ((Set<? extends Map.Entry<? extends K, ? extends V>>) (Set) c).iterator();

                    public boolean hasNext() {
                        return i.hasNext();
                    }

                    public Map.Entry<K, V> next() {
                        return new UnmodifiableEntry<>(i.next());
                    }

                    public void remove() {
                        throw new UnsupportedOperationException();
                    }
                };
            }

            public void forEach(Consumer<? super Map.Entry<K, V>> action) {
                if (action == null) throw new NullPointerException();
                Iterator<Map.Entry<K, V>> it = iterator();
                while (it.hasNext()) action.accept(it.next());
            }

            public Object[] toArray() {
                throw ModelStuck.unsupported("unmodifiable entrySet toArray");
            }

            public <T> T[] toArray(T[] a) {
                throw ModelStuck.unsupported("unmodifiable entrySet toArray");
            }

            public boolean contains(Object o) {
                if (!(o instanceof Map.Entry)) return false;
                return c.contains(new UnmodifiableEntry<>((Map.Entry<?, ?>) o));
            }

            public boolean containsAll(Collection<?> coll) {
                for (Object e : coll) {
                    if (!contains(e)) return false;
                }
                return true;
            }

            public boolean equals(Object o) {
                if (o == this) return true;
                if (!(o instanceof Set)) return false;
                Set<?> s = (Set<?>) o;
                if (s.size() != c.size()) return false;
                return containsAll(s);
            }

            private static class UnmodifiableEntry<K, V> implements Map.Entry<K, V> {
                private final Map.Entry<? extends K, ? extends V> e;

                UnmodifiableEntry(Map.Entry<? extends K, ? extends V> e) {
                    if (e == null) throw new NullPointerException();
                    this.e = e;
                }

                public K getKey() {
                    return e.getKey();
                }

                public V getValue() {
                    return e.getValue();
                }

                public V setValue(V value) {
                    throw new UnsupportedOperationException();
                }

                public int hashCode() {
                    return e.hashCode();
                }

                public boolean equals(Object o) {
                    if (this == o) return true;
                    if (!(o instanceof Map.Entry)) return false;
                    Map.Entry<?, ?> t = (Map.Entry<?, ?>) o;
                    return eq(e.getKey(), t.getKey()) && eq(e.getValue(), t.getValue());
                }

                public String toString() {
                    return e.toString();
                }
            }
        }
    }

    // ---- synchronized wrappers (Javadoc: every method synchronizes on the wrapper; iteration
    //      is left to the caller to synchronize) ----

    public static <T> Collection<T> synchronizedCollection(Collection<T> c) {
        return new SynchronizedCollection<>(c);
    }

    public static <T> List<T> synchronizedList(List<T> list) {
        return new SynchronizedList<>(list);
    }

    public static <T> Set<T> synchronizedSet(Set<T> s) {
        return new SynchronizedSet<>(s);
    }

    public static <K, V> Map<K, V> synchronizedMap(Map<K, V> m) {
        return new SynchronizedMap<>(m);
    }

    static class SynchronizedCollection<E> implements Collection<E>, java.io.Serializable {
        final Collection<E> c;
        final Object mutex;

        SynchronizedCollection(Collection<E> c) {
            if (c == null) throw new NullPointerException();
            this.c = c;
            this.mutex = this;
        }

        public int size() { synchronized (mutex) { return c.size(); } }
        public boolean isEmpty() { synchronized (mutex) { return c.isEmpty(); } }
        public boolean contains(Object o) { synchronized (mutex) { return c.contains(o); } }
        public Object[] toArray() { synchronized (mutex) { return c.toArray(); } }
        public <T> T[] toArray(T[] a) { synchronized (mutex) { return c.toArray(a); } }
        public Iterator<E> iterator() { return c.iterator(); }
        public boolean add(E e) { synchronized (mutex) { return c.add(e); } }
        public boolean remove(Object o) { synchronized (mutex) { return c.remove(o); } }
        public boolean containsAll(Collection<?> coll) { synchronized (mutex) { return c.containsAll(coll); } }
        public boolean addAll(Collection<? extends E> coll) { synchronized (mutex) { return c.addAll(coll); } }
        public boolean removeAll(Collection<?> coll) { synchronized (mutex) { return c.removeAll(coll); } }
        public boolean retainAll(Collection<?> coll) { synchronized (mutex) { return c.retainAll(coll); } }
        public void clear() { synchronized (mutex) { c.clear(); } }
        public String toString() { synchronized (mutex) { return c.toString(); } }
        public void forEach(java.util.function.Consumer<? super E> consumer) { synchronized (mutex) { c.forEach(consumer); } }
        public boolean removeIf(java.util.function.Predicate<? super E> filter) { synchronized (mutex) { return c.removeIf(filter); } }
    }

    static class SynchronizedSet<E> extends SynchronizedCollection<E> implements Set<E> {
        SynchronizedSet(Set<E> s) { super(s); }
        public boolean equals(Object o) { if (this == o) return true; synchronized (mutex) { return c.equals(o); } }
        public int hashCode() { synchronized (mutex) { return c.hashCode(); } }
    }

    static class SynchronizedList<E> extends SynchronizedCollection<E> implements List<E> {
        final List<E> list;
        SynchronizedList(List<E> list) { super(list); this.list = list; }
        public boolean equals(Object o) { if (this == o) return true; synchronized (mutex) { return list.equals(o); } }
        public int hashCode() { synchronized (mutex) { return list.hashCode(); } }
        public E get(int index) { synchronized (mutex) { return list.get(index); } }
        public E set(int index, E element) { synchronized (mutex) { return list.set(index, element); } }
        public void add(int index, E element) { synchronized (mutex) { list.add(index, element); } }
        public E remove(int index) { synchronized (mutex) { return list.remove(index); } }
        public int indexOf(Object o) { synchronized (mutex) { return list.indexOf(o); } }
        public int lastIndexOf(Object o) { synchronized (mutex) { return list.lastIndexOf(o); } }
        public boolean addAll(int index, Collection<? extends E> c) { synchronized (mutex) { return list.addAll(index, c); } }
        public ListIterator<E> listIterator() { return list.listIterator(); }
        public ListIterator<E> listIterator(int index) { return list.listIterator(index); }
        public List<E> subList(int fromIndex, int toIndex) { throw ModelStuck.unsupported("synchronizedList.subList"); }
        public void replaceAll(java.util.function.UnaryOperator<E> operator) { synchronized (mutex) { list.replaceAll(operator); } }
    }

    static class SynchronizedMap<K, V> implements Map<K, V>, java.io.Serializable {
        private final Map<K, V> m;
        final Object mutex;
        SynchronizedMap(Map<K, V> m) { if (m == null) throw new NullPointerException(); this.m = m; mutex = this; }
        public int size() { synchronized (mutex) { return m.size(); } }
        public boolean isEmpty() { synchronized (mutex) { return m.isEmpty(); } }
        public boolean containsKey(Object key) { synchronized (mutex) { return m.containsKey(key); } }
        public boolean containsValue(Object value) { synchronized (mutex) { return m.containsValue(value); } }
        public V get(Object key) { synchronized (mutex) { return m.get(key); } }
        public V put(K key, V value) { synchronized (mutex) { return m.put(key, value); } }
        public V remove(Object key) { synchronized (mutex) { return m.remove(key); } }
        public void putAll(Map<? extends K, ? extends V> map) { synchronized (mutex) { m.putAll(map); } }
        public void clear() { synchronized (mutex) { m.clear(); } }
        public Set<K> keySet() { throw ModelStuck.unsupported("synchronizedMap.keySet"); }
        public Set<Map.Entry<K, V>> entrySet() { throw ModelStuck.unsupported("synchronizedMap.entrySet"); }
        public Collection<V> values() { throw ModelStuck.unsupported("synchronizedMap.values"); }
        public boolean equals(Object o) { if (this == o) return true; synchronized (mutex) { return m.equals(o); } }
        public int hashCode() { synchronized (mutex) { return m.hashCode(); } }
        public String toString() { synchronized (mutex) { return m.toString(); } }
        public V getOrDefault(Object k, V defaultValue) { synchronized (mutex) { return m.getOrDefault(k, defaultValue); } }
        public V putIfAbsent(K key, V value) { synchronized (mutex) { return m.putIfAbsent(key, value); } }
        public boolean remove(Object key, Object value) { synchronized (mutex) { return m.remove(key, value); } }
        public V computeIfAbsent(K key, java.util.function.Function<? super K, ? extends V> f) { synchronized (mutex) { return m.computeIfAbsent(key, f); } }
        public V merge(K key, V value, java.util.function.BiFunction<? super V, ? super V, ? extends V> f) { synchronized (mutex) { return m.merge(key, value, f); } }
    }
}

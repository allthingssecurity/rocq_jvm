/*
 * rocq-jvm model of java.util.Collections (clean-room, Apache-2.0; written from the Javadoc and
 * the algorithms JDK 21 documents and uses, so that every observable effect is HotSpot's).
 *
 * Modelled: every public static method of JDK 21's Collections except the Sequenced* ones:
 *  - algorithms with the JDK's thresholds and call sequences: sort (List.sort), binarySearch
 *    (indexed below 5000 elements or for RandomAccess lists, else through a ListIterator, with
 *    the JDK's probe sequence), reverse (18), shuffle(List, Random/RandomGenerator) (5), swap,
 *    fill (25), copy (10), min/max (in iteration order, with and without a Comparator), rotate
 *    (cycle algorithm for RandomAccess lists or below 100 elements, else three reverses of
 *    subLists), replaceAll (11), indexOfSubList/lastIndexOfSubList (35), frequency, disjoint
 *    (the JDK's choice of the collection to iterate), addAll, list(Enumeration), enumeration.
 *  - views and wrappers with the JDK's classes and delegation: unmodifiable{Collection, Set,
 *    SortedSet, NavigableSet, List, Map, SortedMap, NavigableMap} (entries wrapped, identity of
 *    an already wrapped argument), synchronized{...} (the same nine; RandomAccess lists get the
 *    RandomAccess wrapper; views share the mutex), checked{Collection, Queue, Set, SortedSet,
 *    NavigableSet, List, Map, SortedMap, NavigableMap} (the type checks and their
 *    ClassCastException texts, checkedCopyOf for addAll, checked entries), newSetFromMap,
 *    asLifoQueue, nCopies (CopiesList: its hashCode, equals, toArray, subList checks),
 *    singleton/singletonList/singletonMap, the empty iterators/enumeration/collections/maps
 *    (shared instances; emptySortedSet/NavigableSet and emptySortedMap/NavigableMap are the
 *    JDK's unmodifiable wrappers of an empty TreeSet/TreeMap), reverseOrder (both).
 *  - Exception classes and messages as HotSpot 21, including the helpful NullPointerException
 *    texts of the JDK's implicit null checks (`Cannot invoke "java.util.List.size()" because
 *    "list" is null`, `... "java.lang.Comparable.compareTo(Object)" because "midVal"/"next" is
 *    null`, the anonymous Enumeration's "this.val$c", addAll's "<local3>" ...), thrown here
 *    explicitly; Objects.requireNonNull's null message.
 * STUCK / not modelled: unmodifiableSequenced{Collection, Set, Map} and newSequencedSetFromMap
 * (JDK 21 Sequenced* interfaces are not in the model; not declared, so a call is STUCK),
 * shuffle(List) (it draws from a hidden new Random()), spliterator() and parallelStream() of
 * the views (no Spliterator model; the Collection defaults are STUCK), stream() of a view
 * returns the wrapped collection's stream as the JDK does (CopiesList: IntStream.range().mapToObj).
 * The EMPTY_* constants are created by the class initialiser (as the JDK's static fields are).
 */
package java.util;

import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.IntStream;
import java.util.stream.Stream;

public class Collections {
    private Collections() {
    }

    private static final int BINARYSEARCH_THRESHOLD = 5000;
    private static final int REVERSE_THRESHOLD = 18;
    private static final int SHUFFLE_THRESHOLD = 5;
    private static final int FILL_THRESHOLD = 25;
    private static final int ROTATE_THRESHOLD = 100;
    private static final int COPY_THRESHOLD = 10;
    private static final int REPLACEALL_THRESHOLD = 11;
    private static final int INDEXOFSUBLIST_THRESHOLD = 35;

    @SuppressWarnings("rawtypes")
    public static final Set EMPTY_SET = new EmptySet<>();
    @SuppressWarnings("rawtypes")
    public static final List EMPTY_LIST = new EmptyList<>();
    @SuppressWarnings("rawtypes")
    public static final Map EMPTY_MAP = new EmptyMap<>();

    static boolean eq(Object a, Object b) {
        return a == null ? b == null : a.equals(b);
    }

    /** HotSpot's helpful message of an invoke on a null receiver. */
    static NullPointerException npe(String method, String what) {
        return new NullPointerException("Cannot invoke \"" + method + "\" because \"" + what + "\" is null");
    }

    private static <T> T requireNonNull(T o) {
        if (o == null) throw new NullPointerException();
        return o;
    }

    private static <T> T requireNonNull(T o, String message) {
        if (o == null) throw new NullPointerException(message);
        return o;
    }

    private static int sizeOf(List<?> list, String what) {
        if (list == null) throw npe("java.util.List.size()", what);
        return list.size();
    }

    // ---- sort / binarySearch ----

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static <T extends Comparable<? super T>> void sort(List<T> list) {
        if (list == null) throw npe("java.util.List.sort(java.util.Comparator)", "list");
        list.sort(null);
    }

    public static <T> void sort(List<T> list, Comparator<? super T> c) {
        if (list == null) throw npe("java.util.List.sort(java.util.Comparator)", "list");
        list.sort(c);
    }

    public static <T> int binarySearch(List<? extends Comparable<? super T>> list, T key) {
        if (list instanceof RandomAccess || sizeOf(list, "list") < BINARYSEARCH_THRESHOLD) return indexedBinarySearch(list, key);
        else return iteratorBinarySearch(list, key);
    }

    private static <T> int indexedBinarySearch(List<? extends Comparable<? super T>> list, T key) {
        int low = 0;
        int high = list.size() - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            Object midVal = list.get(mid);
            Arrays.checkComparable(midVal);
            int cmp = Arrays.natCmp(midVal, key, "midVal");
            if (cmp < 0) low = mid + 1;
            else if (cmp > 0) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    private static <T> int iteratorBinarySearch(List<? extends Comparable<? super T>> list, T key) {
        int low = 0;
        int high = list.size() - 1;
        ListIterator<? extends Comparable<? super T>> i = list.listIterator();
        while (low <= high) {
            int mid = (low + high) >>> 1;
            Object midVal = get(i, mid);
            Arrays.checkComparable(midVal);
            int cmp = Arrays.natCmp(midVal, key, "midVal");
            if (cmp < 0) low = mid + 1;
            else if (cmp > 0) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    /** Moves the list iterator i to the element at index and returns it. */
    private static <T> T get(ListIterator<? extends T> i, int index) {
        T obj;
        int pos = i.nextIndex();
        if (pos <= index) {
            do {
                obj = i.next();
            } while (pos++ < index);
        } else {
            do {
                obj = i.previous();
            } while (--pos > index);
        }
        return obj;
    }

    @SuppressWarnings("unchecked")
    public static <T> int binarySearch(List<? extends T> list, T key, Comparator<? super T> c) {
        if (c == null) return binarySearch((List<? extends Comparable<? super T>>) list, key);
        if (list instanceof RandomAccess || sizeOf(list, "list") < BINARYSEARCH_THRESHOLD) return indexedBinarySearch(list, key, c);
        else return iteratorBinarySearch(list, key, c);
    }

    private static <T> int indexedBinarySearch(List<? extends T> l, T key, Comparator<? super T> c) {
        int low = 0;
        int high = l.size() - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            T midVal = l.get(mid);
            int cmp = c.compare(midVal, key);
            if (cmp < 0) low = mid + 1;
            else if (cmp > 0) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    private static <T> int iteratorBinarySearch(List<? extends T> l, T key, Comparator<? super T> c) {
        int low = 0;
        int high = l.size() - 1;
        ListIterator<? extends T> i = l.listIterator();
        while (low <= high) {
            int mid = (low + high) >>> 1;
            T midVal = get(i, mid);
            int cmp = c.compare(midVal, key);
            if (cmp < 0) low = mid + 1;
            else if (cmp > 0) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    // ---- reverse / shuffle / swap / fill / copy ----

    @SuppressWarnings({"rawtypes", "unchecked"})
    public static void reverse(List<?> list) {
        int size = sizeOf(list, "list");
        if (size < REVERSE_THRESHOLD || list instanceof RandomAccess) {
            for (int i = 0, mid = size >> 1, j = size - 1; i < mid; i++, j--) swap(list, i, j);
        } else {
            ListIterator fwd = list.listIterator();
            ListIterator rev = list.listIterator(size);
            for (int i = 0, mid = list.size() >> 1; i < mid; i++) {
                Object tmp = fwd.next();
                fwd.set(rev.previous());
                rev.set(tmp);
            }
        }
    }

    // shuffle(List, Random/RandomGenerator): swaps from the end with rnd.nextInt(i); a list of at
    // least 5 elements that is not RandomAccess is shuffled in an array and written back through
    // a list iterator. shuffle(List) draws from a hidden new Random() (host time): STUCK.

    public static void shuffle(List<?> list) {
        throw ModelStuck.unsupported("Collections.shuffle(List) (unseeded Random)");
    }

    public static void shuffle(List<?> list, Random rnd) {
        shuffle(list, (java.util.random.RandomGenerator) rnd);
    }

    @SuppressWarnings({"rawtypes", "unchecked"})
    public static void shuffle(List<?> list, java.util.random.RandomGenerator rnd) {
        if (list == null) throw new NullPointerException("Cannot invoke \"java.util.List.size()\" because \"list\" is null");
        int size = list.size();
        if (size > 1 && rnd == null)
            throw new NullPointerException("Cannot invoke \"java.util.random.RandomGenerator.nextInt(int)\" because \"rnd\" is null");
        if (size < SHUFFLE_THRESHOLD || list instanceof RandomAccess) {
            for (int i = size; i > 1; i--) swap(list, i - 1, rnd.nextInt(i));
        } else {
            Object[] arr = list.toArray();
            for (int i = size; i > 1; i--) {
                int j = rnd.nextInt(i);
                Object t = arr[i - 1];
                arr[i - 1] = arr[j];
                arr[j] = t;
            }
            ListIterator it = list.listIterator();
            for (Object e : arr) {
                it.next();
                it.set(e);
            }
        }
    }

    @SuppressWarnings({"rawtypes", "unchecked"})
    public static void swap(List<?> list, int i, int j) {
        if (list == null) throw new NullPointerException("Cannot invoke \"java.util.List.get(int)\" because \"l\" is null");
        final List l = list;
        l.set(i, l.set(j, l.get(i)));
    }

    public static <T> void fill(List<? super T> list, T obj) {
        int size = sizeOf(list, "list");
        if (size < FILL_THRESHOLD || list instanceof RandomAccess) {
            for (int i = 0; i < size; i++) list.set(i, obj);
        } else {
            ListIterator<? super T> itr = list.listIterator();
            for (int i = 0; i < size; i++) {
                itr.next();
                itr.set(obj);
            }
        }
    }

    public static <T> void copy(List<? super T> dest, List<? extends T> src) {
        int srcSize = sizeOf(src, "src");
        if (srcSize > sizeOf(dest, "dest")) throw new IndexOutOfBoundsException("Source does not fit in dest");
        if (srcSize < COPY_THRESHOLD || (src instanceof RandomAccess && dest instanceof RandomAccess)) {
            for (int i = 0; i < srcSize; i++) dest.set(i, src.get(i));
        } else {
            ListIterator<? super T> di = dest.listIterator();
            ListIterator<? extends T> si = src.listIterator();
            for (int i = 0; i < srcSize; i++) {
                di.next();
                di.set(si.next());
            }
        }
    }

    // ---- min / max ----

    private static <T> Iterator<T> iteratorOf(Collection<T> coll) {
        if (coll == null) throw npe("java.util.Collection.iterator()", "coll");
        return coll.iterator();
    }

    @SuppressWarnings("unchecked")
    private static <T> T minMax(Collection<? extends T> coll, Comparator<? super T> comp, int sign) {
        Iterator<? extends T> i = iteratorOf(coll);
        T candidate = i.next();
        while (i.hasNext()) {
            T next = i.next();
            int c;
            if (comp == null) {
                Arrays.checkComparable(next);
                c = Arrays.natCmp(next, candidate, "next");
            } else {
                c = comp.compare(next, candidate);
            }
            if (sign < 0 ? c < 0 : c > 0) candidate = next;
        }
        return candidate;
    }

    public static <T extends Object & Comparable<? super T>> T min(Collection<? extends T> coll) {
        return minMax(coll, null, -1);
    }

    public static <T> T min(Collection<? extends T> coll, Comparator<? super T> comp) {
        return minMax(coll, comp, -1);
    }

    public static <T extends Object & Comparable<? super T>> T max(Collection<? extends T> coll) {
        return minMax(coll, null, 1);
    }

    public static <T> T max(Collection<? extends T> coll, Comparator<? super T> comp) {
        return minMax(coll, comp, 1);
    }

    // ---- rotate / replaceAll / indexOfSubList / lastIndexOfSubList ----

    public static void rotate(List<?> list, int distance) {
        if (list instanceof RandomAccess || sizeOf(list, "list") < ROTATE_THRESHOLD) rotate1(list, distance);
        else rotate2(list, distance);
    }

    private static <T> void rotate1(List<T> list, int distance) {
        int size = list.size();
        if (size == 0) return;
        distance = distance % size;
        if (distance < 0) distance += size;
        if (distance == 0) return;
        int bound = size - distance;
        for (int cycleStart = 0, nMoved = 0; nMoved < size; cycleStart++) {
            T displaced = list.get(cycleStart);
            int i = cycleStart;
            do {
                if (i >= bound) i -= size;
                i += distance;
                displaced = list.set(i, displaced);
                nMoved++;
            } while (i != cycleStart);
        }
    }

    private static void rotate2(List<?> list, int distance) {
        int size = list.size();
        if (size == 0) return;
        int mid = -distance % size;
        if (mid < 0) mid += size;
        if (mid == 0) return;
        reverse(list.subList(0, mid));
        reverse(list.subList(mid, size));
        reverse(list);
    }

    public static <T> boolean replaceAll(List<T> list, T oldVal, T newVal) {
        boolean result = false;
        int size = sizeOf(list, "list");
        if (size < REPLACEALL_THRESHOLD || list instanceof RandomAccess) {
            if (oldVal == null) {
                for (int i = 0; i < size; i++) {
                    if (list.get(i) == null) {
                        list.set(i, newVal);
                        result = true;
                    }
                }
            } else {
                for (int i = 0; i < size; i++) {
                    if (oldVal.equals(list.get(i))) {
                        list.set(i, newVal);
                        result = true;
                    }
                }
            }
        } else {
            ListIterator<T> itr = list.listIterator();
            if (oldVal == null) {
                for (int i = 0; i < size; i++) {
                    if (itr.next() == null) {
                        itr.set(newVal);
                        result = true;
                    }
                }
            } else {
                for (int i = 0; i < size; i++) {
                    if (oldVal.equals(itr.next())) {
                        itr.set(newVal);
                        result = true;
                    }
                }
            }
        }
        return result;
    }

    public static int indexOfSubList(List<?> source, List<?> target) {
        int sourceSize = sizeOf(source, "source");
        int targetSize = sizeOf(target, "target");
        int maxCandidate = sourceSize - targetSize;
        if (sourceSize < INDEXOFSUBLIST_THRESHOLD || (source instanceof RandomAccess && target instanceof RandomAccess)) {
            nextCand:
            for (int candidate = 0; candidate <= maxCandidate; candidate++) {
                for (int i = 0, j = candidate; i < targetSize; i++, j++) {
                    if (!eq(target.get(i), source.get(j))) continue nextCand;
                }
                return candidate;
            }
        } else {
            ListIterator<?> si = source.listIterator();
            nextCand:
            for (int candidate = 0; candidate <= maxCandidate; candidate++) {
                ListIterator<?> ti = target.listIterator();
                for (int i = 0; i < targetSize; i++) {
                    if (!eq(ti.next(), si.next())) {
                        for (int j = 0; j < i; j++) si.previous();
                        continue nextCand;
                    }
                }
                return candidate;
            }
        }
        return -1;
    }

    public static int lastIndexOfSubList(List<?> source, List<?> target) {
        int sourceSize = sizeOf(source, "source");
        int targetSize = sizeOf(target, "target");
        int maxCandidate = sourceSize - targetSize;
        if (sourceSize < INDEXOFSUBLIST_THRESHOLD || source instanceof RandomAccess) {
            nextCand:
            for (int candidate = maxCandidate; candidate >= 0; candidate--) {
                for (int i = 0, j = candidate; i < targetSize; i++, j++) {
                    if (!eq(target.get(i), source.get(j))) continue nextCand;
                }
                return candidate;
            }
        } else {
            if (maxCandidate < 0) return -1;
            ListIterator<?> si = source.listIterator(maxCandidate);
            nextCand:
            for (int candidate = maxCandidate; candidate >= 0; candidate--) {
                ListIterator<?> ti = target.listIterator();
                for (int i = 0; i < targetSize; i++) {
                    if (!eq(ti.next(), si.next())) {
                        if (candidate != 0) {
                            for (int j = 0; j <= i + 1; j++) si.previous();
                        }
                        continue nextCand;
                    }
                }
                return candidate;
            }
        }
        return -1;
    }

    // ---- unmodifiable views ----

    @SuppressWarnings("unchecked")
    public static <T> Collection<T> unmodifiableCollection(Collection<? extends T> c) {
        if (c == null) throw npe("java.util.Collection.getClass()", "c");
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
        if (s == null) throw npe("java.util.Set.getClass()", "s");
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

    public static <T> SortedSet<T> unmodifiableSortedSet(SortedSet<T> s) {
        if (s == null) throw npe("java.util.SortedSet.getClass()", "s");
        if (s.getClass() == UnmodifiableSortedSet.class) return s;
        return new UnmodifiableSortedSet<>(s);
    }

    static class UnmodifiableSortedSet<E> extends UnmodifiableSet<E> implements SortedSet<E>, java.io.Serializable {
        private final SortedSet<E> ss;

        UnmodifiableSortedSet(SortedSet<E> s) {
            super(s);
            ss = s;
        }

        @SuppressWarnings("unchecked")
        public Stream<E> stream() {
            return (Stream<E>) c.stream();
        }

        public Comparator<? super E> comparator() {
            return ss.comparator();
        }

        public SortedSet<E> subSet(E fromElement, E toElement) {
            return new UnmodifiableSortedSet<>(ss.subSet(fromElement, toElement));
        }

        public SortedSet<E> headSet(E toElement) {
            return new UnmodifiableSortedSet<>(ss.headSet(toElement));
        }

        public SortedSet<E> tailSet(E fromElement) {
            return new UnmodifiableSortedSet<>(ss.tailSet(fromElement));
        }

        public E first() {
            return ss.first();
        }

        public E last() {
            return ss.last();
        }
    }

    public static <T> NavigableSet<T> unmodifiableNavigableSet(NavigableSet<T> s) {
        if (s == null) throw npe("java.util.NavigableSet.getClass()", "s");
        if (s.getClass() == UnmodifiableNavigableSet.class) return s;
        return new UnmodifiableNavigableSet<>(s);
    }

    static class UnmodifiableNavigableSet<E> extends UnmodifiableSortedSet<E> implements NavigableSet<E>, java.io.Serializable {
        private static class EmptyNavigableSet<E> extends UnmodifiableNavigableSet<E> implements java.io.Serializable {
            EmptyNavigableSet() {
                super(new TreeSet<>());
            }
        }

        private static final NavigableSet<?> EMPTY_NAVIGABLE_SET = new EmptyNavigableSet<>();

        private final NavigableSet<E> ns;

        UnmodifiableNavigableSet(NavigableSet<E> s) {
            super(s);
            ns = s;
        }

        public E lower(E e) {
            return ns.lower(e);
        }

        public E floor(E e) {
            return ns.floor(e);
        }

        public E ceiling(E e) {
            return ns.ceiling(e);
        }

        public E higher(E e) {
            return ns.higher(e);
        }

        public E pollFirst() {
            throw new UnsupportedOperationException();
        }

        public E pollLast() {
            throw new UnsupportedOperationException();
        }

        public NavigableSet<E> descendingSet() {
            return new UnmodifiableNavigableSet<>(ns.descendingSet());
        }

        public Iterator<E> descendingIterator() {
            return descendingSet().iterator();
        }

        public NavigableSet<E> subSet(E fromElement, boolean fromInclusive, E toElement, boolean toInclusive) {
            return new UnmodifiableNavigableSet<>(ns.subSet(fromElement, fromInclusive, toElement, toInclusive));
        }

        public NavigableSet<E> headSet(E toElement, boolean inclusive) {
            return new UnmodifiableNavigableSet<>(ns.headSet(toElement, inclusive));
        }

        public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
            return new UnmodifiableNavigableSet<>(ns.tailSet(fromElement, inclusive));
        }
    }

    @SuppressWarnings("unchecked")
    public static <T> List<T> unmodifiableList(List<? extends T> list) {
        if (list == null) throw npe("java.util.List.getClass()", "list");
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
        if (m == null) throw npe("java.util.Map.getClass()", "m");
        if (m.getClass() == UnmodifiableMap.class) return (Map<K, V>) m;
        return new UnmodifiableMap<>(m);
    }

    private static class UnmodifiableMap<K, V> implements Map<K, V>, java.io.Serializable {
        final Map<? extends K, ? extends V> m;
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
        @SuppressWarnings({"unchecked", "rawtypes"})
        static class UnmodifiableEntrySet<K, V> extends UnmodifiableSet<Map.Entry<K, V>> {
            UnmodifiableEntrySet(Set<? extends Map.Entry<? extends K, ? extends V>> s) {
                super((Set) s);
            }

            static <K, V> Consumer<Map.Entry<? extends K, ? extends V>> entryConsumer(Consumer<? super Map.Entry<K, V>> action) {
                return e -> action.accept(new UnmodifiableEntry<>(e));
            }

            public void forEach(Consumer<? super Map.Entry<K, V>> action) {
                requireNonNull(action);
                ((Collection) c).forEach(entryConsumer(action));
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

                    public void forEachRemaining(Consumer<? super Map.Entry<K, V>> action) {
                        requireNonNull(action);
                        ((Iterator) i).forEachRemaining(entryConsumer(action));
                    }
                };
            }

            public Object[] toArray() {
                Object[] a = c.toArray();
                for (int i = 0; i < a.length; i++) a[i] = new UnmodifiableEntry<>((Map.Entry<? extends K, ? extends V>) a[i]);
                return a;
            }

            public <T> T[] toArray(T[] a) {
                Object[] arr = c.toArray(a.length == 0 ? a : Arrays.copyOf(a, 0));
                for (int i = 0; i < arr.length; i++) arr[i] = new UnmodifiableEntry<>((Map.Entry<? extends K, ? extends V>) arr[i]);
                if (arr.length > a.length) return (T[]) arr;
                System.arraycopy(arr, 0, a, 0, arr.length);
                if (a.length > arr.length) a[arr.length] = null;
                return a;
            }

            public boolean contains(Object o) {
                if (!(o instanceof Map.Entry)) return false;
                return c.contains(new UnmodifiableEntry<>((Map.Entry<?, ?>) o));
            }

            public boolean containsAll(Collection<?> coll) {
                if (coll == null) throw npe("java.util.Collection.iterator()", "coll");
                for (Object e : coll) {
                    if (!contains(e)) return false;
                }
                return true;
            }

            public boolean equals(Object o) {
                if (o == this) return true;
                if (!(o instanceof Set)) return false;
                Set<?> s = (Set<?>) o;
                return s.size() == c.size() && containsAll(s);
            }

            static class UnmodifiableEntry<K, V> implements Map.Entry<K, V> {
                private Map.Entry<? extends K, ? extends V> e;

                UnmodifiableEntry(Map.Entry<? extends K, ? extends V> e) {
                    this.e = requireNonNull(e);
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

    @SuppressWarnings("unchecked")
    public static <K, V> SortedMap<K, V> unmodifiableSortedMap(SortedMap<K, ? extends V> m) {
        if (m == null) throw npe("java.util.SortedMap.getClass()", "m");
        if (m.getClass() == UnmodifiableSortedMap.class) return (SortedMap<K, V>) m;
        return new UnmodifiableSortedMap<>(m);
    }

    static class UnmodifiableSortedMap<K, V> extends UnmodifiableMap<K, V> implements SortedMap<K, V>, java.io.Serializable {
        private final SortedMap<K, ? extends V> sm;

        UnmodifiableSortedMap(SortedMap<K, ? extends V> m) {
            super(m);
            sm = m;
        }

        public Comparator<? super K> comparator() {
            return sm.comparator();
        }

        public SortedMap<K, V> subMap(K fromKey, K toKey) {
            return new UnmodifiableSortedMap<>(sm.subMap(fromKey, toKey));
        }

        public SortedMap<K, V> headMap(K toKey) {
            return new UnmodifiableSortedMap<>(sm.headMap(toKey));
        }

        public SortedMap<K, V> tailMap(K fromKey) {
            return new UnmodifiableSortedMap<>(sm.tailMap(fromKey));
        }

        public K firstKey() {
            return sm.firstKey();
        }

        public K lastKey() {
            return sm.lastKey();
        }
    }

    @SuppressWarnings("unchecked")
    public static <K, V> NavigableMap<K, V> unmodifiableNavigableMap(NavigableMap<K, ? extends V> m) {
        if (m == null) throw npe("java.util.NavigableMap.getClass()", "m");
        if (m.getClass() == UnmodifiableNavigableMap.class) return (NavigableMap<K, V>) m;
        return new UnmodifiableNavigableMap<>(m);
    }

    @SuppressWarnings("unchecked")
    static class UnmodifiableNavigableMap<K, V> extends UnmodifiableSortedMap<K, V> implements NavigableMap<K, V>, java.io.Serializable {
        private static class EmptyNavigableMap<K, V> extends UnmodifiableNavigableMap<K, V> implements java.io.Serializable {
            EmptyNavigableMap() {
                super(new TreeMap<>());
            }

            public NavigableSet<K> navigableKeySet() {
                return emptyNavigableSet();
            }
        }

        private static final EmptyNavigableMap<?, ?> EMPTY_NAVIGABLE_MAP = new EmptyNavigableMap<>();

        private final NavigableMap<K, ? extends V> nm;

        UnmodifiableNavigableMap(NavigableMap<K, ? extends V> m) {
            super(m);
            nm = m;
        }

        private static <K, V> Map.Entry<K, V> wrap(Map.Entry<K, ? extends V> e) {
            return (null != e) ? new UnmodifiableMap.UnmodifiableEntrySet.UnmodifiableEntry<K, V>(e) : null;
        }

        public K lowerKey(K key) {
            return nm.lowerKey(key);
        }

        public K floorKey(K key) {
            return nm.floorKey(key);
        }

        public K ceilingKey(K key) {
            return nm.ceilingKey(key);
        }

        public K higherKey(K key) {
            return nm.higherKey(key);
        }

        public Map.Entry<K, V> lowerEntry(K key) {
            return wrap(nm.lowerEntry(key));
        }

        public Map.Entry<K, V> floorEntry(K key) {
            return wrap(nm.floorEntry(key));
        }

        public Map.Entry<K, V> ceilingEntry(K key) {
            return wrap(nm.ceilingEntry(key));
        }

        public Map.Entry<K, V> higherEntry(K key) {
            return wrap(nm.higherEntry(key));
        }

        public Map.Entry<K, V> firstEntry() {
            return wrap(nm.firstEntry());
        }

        public Map.Entry<K, V> lastEntry() {
            return wrap(nm.lastEntry());
        }

        public Map.Entry<K, V> pollFirstEntry() {
            throw new UnsupportedOperationException();
        }

        public Map.Entry<K, V> pollLastEntry() {
            throw new UnsupportedOperationException();
        }

        public NavigableMap<K, V> descendingMap() {
            return unmodifiableNavigableMap(nm.descendingMap());
        }

        public NavigableSet<K> navigableKeySet() {
            return unmodifiableNavigableSet(nm.navigableKeySet());
        }

        public NavigableSet<K> descendingKeySet() {
            return unmodifiableNavigableSet(nm.descendingKeySet());
        }

        public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
            return unmodifiableNavigableMap(nm.subMap(fromKey, fromInclusive, toKey, toInclusive));
        }

        public NavigableMap<K, V> headMap(K toKey, boolean inclusive) {
            return unmodifiableNavigableMap(nm.headMap(toKey, inclusive));
        }

        public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) {
            return unmodifiableNavigableMap(nm.tailMap(fromKey, inclusive));
        }
    }

    // ---- synchronized wrappers (every method synchronizes on the mutex; iterators, list
    //      iterators, spliterators and streams are left to the caller to synchronize) ----

    public static <T> Collection<T> synchronizedCollection(Collection<T> c) {
        return new SynchronizedCollection<>(c);
    }

    static <T> Collection<T> synchronizedCollection(Collection<T> c, Object mutex) {
        return new SynchronizedCollection<>(c, mutex);
    }

    static class SynchronizedCollection<E> implements Collection<E>, java.io.Serializable {
        final Collection<E> c;
        final Object mutex;

        SynchronizedCollection(Collection<E> c) {
            this.c = requireNonNull(c);
            this.mutex = this;
        }

        SynchronizedCollection(Collection<E> c, Object mutex) {
            this.c = requireNonNull(c);
            this.mutex = requireNonNull(mutex);
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
        public void forEach(Consumer<? super E> consumer) { synchronized (mutex) { c.forEach(consumer); } }
        public boolean removeIf(Predicate<? super E> filter) { synchronized (mutex) { return c.removeIf(filter); } }
        public Stream<E> stream() { return c.stream(); }
    }

    public static <T> Set<T> synchronizedSet(Set<T> s) {
        return new SynchronizedSet<>(s);
    }

    static <T> Set<T> synchronizedSet(Set<T> s, Object mutex) {
        return new SynchronizedSet<>(s, mutex);
    }

    static class SynchronizedSet<E> extends SynchronizedCollection<E> implements Set<E> {
        SynchronizedSet(Set<E> s) { super(s); }
        SynchronizedSet(Set<E> s, Object mutex) { super(s, mutex); }
        public boolean equals(Object o) { if (this == o) return true; synchronized (mutex) { return c.equals(o); } }
        public int hashCode() { synchronized (mutex) { return c.hashCode(); } }
    }

    public static <T> SortedSet<T> synchronizedSortedSet(SortedSet<T> s) {
        return new SynchronizedSortedSet<>(s);
    }

    static class SynchronizedSortedSet<E> extends SynchronizedSet<E> implements SortedSet<E> {
        private final SortedSet<E> ss;
        SynchronizedSortedSet(SortedSet<E> s) { super(s); ss = s; }
        SynchronizedSortedSet(SortedSet<E> s, Object mutex) { super(s, mutex); ss = s; }
        public Comparator<? super E> comparator() { synchronized (mutex) { return ss.comparator(); } }
        public SortedSet<E> subSet(E fromElement, E toElement) { synchronized (mutex) { return new SynchronizedSortedSet<>(ss.subSet(fromElement, toElement), mutex); } }
        public SortedSet<E> headSet(E toElement) { synchronized (mutex) { return new SynchronizedSortedSet<>(ss.headSet(toElement), mutex); } }
        public SortedSet<E> tailSet(E fromElement) { synchronized (mutex) { return new SynchronizedSortedSet<>(ss.tailSet(fromElement), mutex); } }
        public E first() { synchronized (mutex) { return ss.first(); } }
        public E last() { synchronized (mutex) { return ss.last(); } }
    }

    public static <T> NavigableSet<T> synchronizedNavigableSet(NavigableSet<T> s) {
        return new SynchronizedNavigableSet<>(s);
    }

    static class SynchronizedNavigableSet<E> extends SynchronizedSortedSet<E> implements NavigableSet<E> {
        private final NavigableSet<E> ns;
        SynchronizedNavigableSet(NavigableSet<E> s) { super(s); ns = s; }
        SynchronizedNavigableSet(NavigableSet<E> s, Object mutex) { super(s, mutex); ns = s; }
        public E lower(E e) { synchronized (mutex) { return ns.lower(e); } }
        public E floor(E e) { synchronized (mutex) { return ns.floor(e); } }
        public E ceiling(E e) { synchronized (mutex) { return ns.ceiling(e); } }
        public E higher(E e) { synchronized (mutex) { return ns.higher(e); } }
        public E pollFirst() { synchronized (mutex) { return ns.pollFirst(); } }
        public E pollLast() { synchronized (mutex) { return ns.pollLast(); } }
        public NavigableSet<E> descendingSet() { synchronized (mutex) { return new SynchronizedNavigableSet<>(ns.descendingSet(), mutex); } }
        public Iterator<E> descendingIterator() { synchronized (mutex) { return descendingSet().iterator(); } }
        public NavigableSet<E> subSet(E fromElement, E toElement) { synchronized (mutex) { return new SynchronizedNavigableSet<>(ns.subSet(fromElement, true, toElement, false), mutex); } }
        public NavigableSet<E> headSet(E toElement) { synchronized (mutex) { return new SynchronizedNavigableSet<>(ns.headSet(toElement, false), mutex); } }
        public NavigableSet<E> tailSet(E fromElement) { synchronized (mutex) { return new SynchronizedNavigableSet<>(ns.tailSet(fromElement, true), mutex); } }
        public NavigableSet<E> subSet(E fromElement, boolean fromInclusive, E toElement, boolean toInclusive) {
            synchronized (mutex) { return new SynchronizedNavigableSet<>(ns.subSet(fromElement, fromInclusive, toElement, toInclusive), mutex); }
        }
        public NavigableSet<E> headSet(E toElement, boolean inclusive) { synchronized (mutex) { return new SynchronizedNavigableSet<>(ns.headSet(toElement, inclusive), mutex); } }
        public NavigableSet<E> tailSet(E fromElement, boolean inclusive) { synchronized (mutex) { return new SynchronizedNavigableSet<>(ns.tailSet(fromElement, inclusive), mutex); } }
    }

    public static <T> List<T> synchronizedList(List<T> list) {
        return (list instanceof RandomAccess) ? new SynchronizedRandomAccessList<>(list) : new SynchronizedList<>(list);
    }

    static <T> List<T> synchronizedList(List<T> list, Object mutex) {
        return (list instanceof RandomAccess) ? new SynchronizedRandomAccessList<>(list, mutex) : new SynchronizedList<>(list, mutex);
    }

    static class SynchronizedList<E> extends SynchronizedCollection<E> implements List<E> {
        final List<E> list;
        SynchronizedList(List<E> list) { super(list); this.list = list; }
        SynchronizedList(List<E> list, Object mutex) { super(list, mutex); this.list = list; }
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
        public List<E> subList(int fromIndex, int toIndex) { synchronized (mutex) { return new SynchronizedList<>(list.subList(fromIndex, toIndex), mutex); } }
        public void replaceAll(UnaryOperator<E> operator) { synchronized (mutex) { list.replaceAll(operator); } }
        public void sort(Comparator<? super E> c) { synchronized (mutex) { list.sort(c); } }
    }

    static class SynchronizedRandomAccessList<E> extends SynchronizedList<E> implements RandomAccess {
        SynchronizedRandomAccessList(List<E> list) { super(list); }
        SynchronizedRandomAccessList(List<E> list, Object mutex) { super(list, mutex); }
        public List<E> subList(int fromIndex, int toIndex) {
            synchronized (mutex) { return new SynchronizedRandomAccessList<>(list.subList(fromIndex, toIndex), mutex); }
        }
    }

    public static <K, V> Map<K, V> synchronizedMap(Map<K, V> m) {
        return new SynchronizedMap<>(m);
    }

    private static class SynchronizedMap<K, V> implements Map<K, V>, java.io.Serializable {
        private final Map<K, V> m;
        final Object mutex;
        private transient Set<K> keySet;
        private transient Set<Map.Entry<K, V>> entrySet;
        private transient Collection<V> values;

        SynchronizedMap(Map<K, V> m) { this.m = requireNonNull(m); mutex = this; }
        SynchronizedMap(Map<K, V> m, Object mutex) { this.m = m; this.mutex = mutex; }
        public int size() { synchronized (mutex) { return m.size(); } }
        public boolean isEmpty() { synchronized (mutex) { return m.isEmpty(); } }
        public boolean containsKey(Object key) { synchronized (mutex) { return m.containsKey(key); } }
        public boolean containsValue(Object value) { synchronized (mutex) { return m.containsValue(value); } }
        public V get(Object key) { synchronized (mutex) { return m.get(key); } }
        public V put(K key, V value) { synchronized (mutex) { return m.put(key, value); } }
        public V remove(Object key) { synchronized (mutex) { return m.remove(key); } }
        public void putAll(Map<? extends K, ? extends V> map) { synchronized (mutex) { m.putAll(map); } }
        public void clear() { synchronized (mutex) { m.clear(); } }
        public Set<K> keySet() {
            synchronized (mutex) {
                if (keySet == null) keySet = new SynchronizedSet<>(m.keySet(), mutex);
                return keySet;
            }
        }
        public Set<Map.Entry<K, V>> entrySet() {
            synchronized (mutex) {
                if (entrySet == null) entrySet = new SynchronizedSet<>(m.entrySet(), mutex);
                return entrySet;
            }
        }
        public Collection<V> values() {
            synchronized (mutex) {
                if (values == null) values = new SynchronizedCollection<>(m.values(), mutex);
                return values;
            }
        }
        public boolean equals(Object o) { if (this == o) return true; synchronized (mutex) { return m.equals(o); } }
        public int hashCode() { synchronized (mutex) { return m.hashCode(); } }
        public String toString() { synchronized (mutex) { return m.toString(); } }
        public V getOrDefault(Object k, V defaultValue) { synchronized (mutex) { return m.getOrDefault(k, defaultValue); } }
        public void forEach(BiConsumer<? super K, ? super V> action) { synchronized (mutex) { m.forEach(action); } }
        public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) { synchronized (mutex) { m.replaceAll(function); } }
        public V putIfAbsent(K key, V value) { synchronized (mutex) { return m.putIfAbsent(key, value); } }
        public boolean remove(Object key, Object value) { synchronized (mutex) { return m.remove(key, value); } }
        public boolean replace(K key, V oldValue, V newValue) { synchronized (mutex) { return m.replace(key, oldValue, newValue); } }
        public V replace(K key, V value) { synchronized (mutex) { return m.replace(key, value); } }
        public V computeIfAbsent(K key, Function<? super K, ? extends V> f) { synchronized (mutex) { return m.computeIfAbsent(key, f); } }
        public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> f) { synchronized (mutex) { return m.computeIfPresent(key, f); } }
        public V compute(K key, BiFunction<? super K, ? super V, ? extends V> f) { synchronized (mutex) { return m.compute(key, f); } }
        public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> f) { synchronized (mutex) { return m.merge(key, value, f); } }
    }

    public static <K, V> SortedMap<K, V> synchronizedSortedMap(SortedMap<K, V> m) {
        return new SynchronizedSortedMap<>(m);
    }

    static class SynchronizedSortedMap<K, V> extends SynchronizedMap<K, V> implements SortedMap<K, V> {
        private final SortedMap<K, V> sm;
        SynchronizedSortedMap(SortedMap<K, V> m) { super(m); sm = m; }
        SynchronizedSortedMap(SortedMap<K, V> m, Object mutex) { super(m, mutex); sm = m; }
        public Comparator<? super K> comparator() { synchronized (mutex) { return sm.comparator(); } }
        public SortedMap<K, V> subMap(K fromKey, K toKey) { synchronized (mutex) { return new SynchronizedSortedMap<>(sm.subMap(fromKey, toKey), mutex); } }
        public SortedMap<K, V> headMap(K toKey) { synchronized (mutex) { return new SynchronizedSortedMap<>(sm.headMap(toKey), mutex); } }
        public SortedMap<K, V> tailMap(K fromKey) { synchronized (mutex) { return new SynchronizedSortedMap<>(sm.tailMap(fromKey), mutex); } }
        public K firstKey() { synchronized (mutex) { return sm.firstKey(); } }
        public K lastKey() { synchronized (mutex) { return sm.lastKey(); } }
    }

    public static <K, V> NavigableMap<K, V> synchronizedNavigableMap(NavigableMap<K, V> m) {
        return new SynchronizedNavigableMap<>(m);
    }

    static class SynchronizedNavigableMap<K, V> extends SynchronizedSortedMap<K, V> implements NavigableMap<K, V> {
        private final NavigableMap<K, V> nm;
        SynchronizedNavigableMap(NavigableMap<K, V> m) { super(m); nm = m; }
        SynchronizedNavigableMap(NavigableMap<K, V> m, Object mutex) { super(m, mutex); nm = m; }
        public Map.Entry<K, V> lowerEntry(K key) { synchronized (mutex) { return nm.lowerEntry(key); } }
        public K lowerKey(K key) { synchronized (mutex) { return nm.lowerKey(key); } }
        public Map.Entry<K, V> floorEntry(K key) { synchronized (mutex) { return nm.floorEntry(key); } }
        public K floorKey(K key) { synchronized (mutex) { return nm.floorKey(key); } }
        public Map.Entry<K, V> ceilingEntry(K key) { synchronized (mutex) { return nm.ceilingEntry(key); } }
        public K ceilingKey(K key) { synchronized (mutex) { return nm.ceilingKey(key); } }
        public Map.Entry<K, V> higherEntry(K key) { synchronized (mutex) { return nm.higherEntry(key); } }
        public K higherKey(K key) { synchronized (mutex) { return nm.higherKey(key); } }
        public Map.Entry<K, V> firstEntry() { synchronized (mutex) { return nm.firstEntry(); } }
        public Map.Entry<K, V> lastEntry() { synchronized (mutex) { return nm.lastEntry(); } }
        public Map.Entry<K, V> pollFirstEntry() { synchronized (mutex) { return nm.pollFirstEntry(); } }
        public Map.Entry<K, V> pollLastEntry() { synchronized (mutex) { return nm.pollLastEntry(); } }
        public NavigableMap<K, V> descendingMap() { synchronized (mutex) { return new SynchronizedNavigableMap<>(nm.descendingMap(), mutex); } }
        public NavigableSet<K> keySet() { return navigableKeySet(); }
        public NavigableSet<K> navigableKeySet() { synchronized (mutex) { return new SynchronizedNavigableSet<>(nm.navigableKeySet(), mutex); } }
        public NavigableSet<K> descendingKeySet() { synchronized (mutex) { return new SynchronizedNavigableSet<>(nm.descendingKeySet(), mutex); } }
        public SortedMap<K, V> subMap(K fromKey, K toKey) { synchronized (mutex) { return new SynchronizedNavigableMap<>(nm.subMap(fromKey, true, toKey, false), mutex); } }
        public SortedMap<K, V> headMap(K toKey) { synchronized (mutex) { return new SynchronizedNavigableMap<>(nm.headMap(toKey, false), mutex); } }
        public SortedMap<K, V> tailMap(K fromKey) { synchronized (mutex) { return new SynchronizedNavigableMap<>(nm.tailMap(fromKey, true), mutex); } }
        public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
            synchronized (mutex) { return new SynchronizedNavigableMap<>(nm.subMap(fromKey, fromInclusive, toKey, toInclusive), mutex); }
        }
        public NavigableMap<K, V> headMap(K toKey, boolean inclusive) { synchronized (mutex) { return new SynchronizedNavigableMap<>(nm.headMap(toKey, inclusive), mutex); } }
        public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) { synchronized (mutex) { return new SynchronizedNavigableMap<>(nm.tailMap(fromKey, inclusive), mutex); } }
    }

    // ---- checked (dynamically typesafe) views ----

    public static <E> Collection<E> checkedCollection(Collection<E> c, Class<E> type) {
        return new CheckedCollection<>(c, type);
    }

    @SuppressWarnings("unchecked")
    static <T> T[] zeroLengthArray(Class<T> type) {
        Object a = java.lang.reflect.Array.newInstance(type, 0);
        if (!(a instanceof Object[])) {
            String x = a.getClass().getName();
            throw new ClassCastException("class " + x + " cannot be cast to class [Ljava.lang.Object; (" + x
                + " and [Ljava.lang.Object; are in module java.base of loader 'bootstrap')");
        }
        return (T[]) a;
    }

    static class CheckedCollection<E> implements Collection<E>, java.io.Serializable {
        final Collection<E> c;
        final Class<E> type;
        private E[] zeroLengthElementArray;

        @SuppressWarnings("unchecked")
        E typeCheck(Object o) {
            if (o != null && !type.isInstance(o)) throw new ClassCastException(badElementMsg(o));
            return (E) o;
        }

        private String badElementMsg(Object o) {
            return "Attempt to insert " + o.getClass() + " element into collection with element type " + type;
        }

        CheckedCollection(Collection<E> c, Class<E> type) {
            this.c = requireNonNull(c, "c");
            this.type = requireNonNull(type, "type");
        }

        public int size() { return c.size(); }
        public boolean isEmpty() { return c.isEmpty(); }
        public boolean contains(Object o) { return c.contains(o); }
        public Object[] toArray() { return c.toArray(); }
        public <T> T[] toArray(T[] a) { return c.toArray(a); }
        public String toString() { return c.toString(); }
        public boolean remove(Object o) { return c.remove(o); }
        public void clear() { c.clear(); }
        public boolean containsAll(Collection<?> coll) { return c.containsAll(coll); }
        public boolean removeAll(Collection<?> coll) { return c.removeAll(coll); }
        public boolean retainAll(Collection<?> coll) { return c.retainAll(coll); }

        public Iterator<E> iterator() {
            final Iterator<E> it = c.iterator();
            return new Iterator<E>() {
                public boolean hasNext() { return it.hasNext(); }
                public E next() { return it.next(); }
                public void remove() { it.remove(); }
                public void forEachRemaining(Consumer<? super E> action) { it.forEachRemaining(action); }
            };
        }

        public boolean add(E e) { return c.add(typeCheck(e)); }

        private E[] zeroLengthElementArray() {
            return zeroLengthElementArray != null ? zeroLengthElementArray : (zeroLengthElementArray = zeroLengthArray(type));
        }

        @SuppressWarnings("unchecked")
        Collection<E> checkedCopyOf(Collection<? extends E> coll) {
            Object[] a;
            try {
                E[] z = zeroLengthElementArray();
                if (coll == null) throw npe("java.util.Collection.toArray(Object[])", "coll");
                a = coll.toArray(z);
                if (a.getClass() != z.getClass()) a = Arrays.copyOf(a, a.length, z.getClass());
            } catch (ArrayStoreException ignore) {
                a = coll.toArray().clone();
                for (Object o : a) typeCheck(o);
            }
            return (Collection<E>) Arrays.asList(a);
        }

        public boolean addAll(Collection<? extends E> coll) { return c.addAll(checkedCopyOf(coll)); }
        public void forEach(Consumer<? super E> action) { c.forEach(action); }
        public boolean removeIf(Predicate<? super E> filter) { return c.removeIf(filter); }
        public Stream<E> stream() { return c.stream(); }
    }

    public static <E> Queue<E> checkedQueue(Queue<E> queue, Class<E> type) {
        return new CheckedQueue<>(queue, type);
    }

    static class CheckedQueue<E> extends CheckedCollection<E> implements Queue<E>, java.io.Serializable {
        final Queue<E> queue;
        CheckedQueue(Queue<E> queue, Class<E> elementType) { super(queue, elementType); this.queue = queue; }
        public E element() { return queue.element(); }
        public boolean equals(Object o) { return o == this || c.equals(o); }
        public int hashCode() { return c.hashCode(); }
        public E peek() { return queue.peek(); }
        public E poll() { return queue.poll(); }
        public E remove() { return queue.remove(); }
        public boolean offer(E e) { return queue.offer(typeCheck(e)); }
    }

    public static <E> Set<E> checkedSet(Set<E> s, Class<E> type) {
        return new CheckedSet<>(s, type);
    }

    static class CheckedSet<E> extends CheckedCollection<E> implements Set<E>, java.io.Serializable {
        CheckedSet(Set<E> s, Class<E> elementType) { super(s, elementType); }
        public boolean equals(Object o) { return o == this || c.equals(o); }
        public int hashCode() { return c.hashCode(); }
    }

    public static <E> SortedSet<E> checkedSortedSet(SortedSet<E> s, Class<E> type) {
        return new CheckedSortedSet<>(s, type);
    }

    static class CheckedSortedSet<E> extends CheckedSet<E> implements SortedSet<E>, java.io.Serializable {
        private final SortedSet<E> ss;
        CheckedSortedSet(SortedSet<E> s, Class<E> type) { super(s, type); ss = s; }
        public Comparator<? super E> comparator() { return ss.comparator(); }
        public E first() { return ss.first(); }
        public E last() { return ss.last(); }
        public SortedSet<E> subSet(E fromElement, E toElement) { return checkedSortedSet(ss.subSet(fromElement, toElement), type); }
        public SortedSet<E> headSet(E toElement) { return checkedSortedSet(ss.headSet(toElement), type); }
        public SortedSet<E> tailSet(E fromElement) { return checkedSortedSet(ss.tailSet(fromElement), type); }
    }

    public static <E> NavigableSet<E> checkedNavigableSet(NavigableSet<E> s, Class<E> type) {
        return new CheckedNavigableSet<>(s, type);
    }

    static class CheckedNavigableSet<E> extends CheckedSortedSet<E> implements NavigableSet<E>, java.io.Serializable {
        private final NavigableSet<E> ns;
        CheckedNavigableSet(NavigableSet<E> s, Class<E> type) { super(s, type); ns = s; }
        public E lower(E e) { return ns.lower(e); }
        public E floor(E e) { return ns.floor(e); }
        public E ceiling(E e) { return ns.ceiling(e); }
        public E higher(E e) { return ns.higher(e); }
        public E pollFirst() { return ns.pollFirst(); }
        public E pollLast() { return ns.pollLast(); }
        public NavigableSet<E> descendingSet() { return checkedNavigableSet(ns.descendingSet(), type); }
        public Iterator<E> descendingIterator() { return checkedNavigableSet(ns.descendingSet(), type).iterator(); }
        public NavigableSet<E> subSet(E fromElement, E toElement) { return checkedNavigableSet(ns.subSet(fromElement, true, toElement, false), type); }
        public NavigableSet<E> headSet(E toElement) { return checkedNavigableSet(ns.headSet(toElement, false), type); }
        public NavigableSet<E> tailSet(E fromElement) { return checkedNavigableSet(ns.tailSet(fromElement, true), type); }
        public NavigableSet<E> subSet(E fromElement, boolean fromInclusive, E toElement, boolean toInclusive) {
            return checkedNavigableSet(ns.subSet(fromElement, fromInclusive, toElement, toInclusive), type);
        }
        public NavigableSet<E> headSet(E toElement, boolean inclusive) { return checkedNavigableSet(ns.headSet(toElement, inclusive), type); }
        public NavigableSet<E> tailSet(E fromElement, boolean inclusive) { return checkedNavigableSet(ns.tailSet(fromElement, inclusive), type); }
    }

    public static <E> List<E> checkedList(List<E> list, Class<E> type) {
        return (list instanceof RandomAccess) ? new CheckedRandomAccessList<>(list, type) : new CheckedList<>(list, type);
    }

    static class CheckedList<E> extends CheckedCollection<E> implements List<E> {
        final List<E> list;
        CheckedList(List<E> list, Class<E> type) { super(list, type); this.list = list; }
        public boolean equals(Object o) { return o == this || list.equals(o); }
        public int hashCode() { return list.hashCode(); }
        public E get(int index) { return list.get(index); }
        public E remove(int index) { return list.remove(index); }
        public int indexOf(Object o) { return list.indexOf(o); }
        public int lastIndexOf(Object o) { return list.lastIndexOf(o); }
        public E set(int index, E element) { return list.set(index, typeCheck(element)); }
        public void add(int index, E element) { list.add(index, typeCheck(element)); }
        public boolean addAll(int index, Collection<? extends E> c) { return list.addAll(index, checkedCopyOf(c)); }
        public ListIterator<E> listIterator() { return listIterator(0); }

        public ListIterator<E> listIterator(final int index) {
            final ListIterator<E> i = list.listIterator(index);
            return new ListIterator<E>() {
                public boolean hasNext() { return i.hasNext(); }
                public E next() { return i.next(); }
                public boolean hasPrevious() { return i.hasPrevious(); }
                public E previous() { return i.previous(); }
                public int nextIndex() { return i.nextIndex(); }
                public int previousIndex() { return i.previousIndex(); }
                public void remove() { i.remove(); }
                public void set(E e) { i.set(typeCheck(e)); }
                public void add(E e) { i.add(typeCheck(e)); }
                public void forEachRemaining(Consumer<? super E> action) { i.forEachRemaining(action); }
            };
        }

        public List<E> subList(int fromIndex, int toIndex) { return new CheckedList<>(list.subList(fromIndex, toIndex), type); }

        public void replaceAll(UnaryOperator<E> operator) {
            requireNonNull(operator);
            list.replaceAll(e -> typeCheck(operator.apply(e)));
        }

        public void sort(Comparator<? super E> c) { list.sort(c); }
    }

    static class CheckedRandomAccessList<E> extends CheckedList<E> implements RandomAccess {
        CheckedRandomAccessList(List<E> list, Class<E> type) { super(list, type); }
        public List<E> subList(int fromIndex, int toIndex) { return new CheckedRandomAccessList<>(list.subList(fromIndex, toIndex), type); }
    }

    public static <K, V> Map<K, V> checkedMap(Map<K, V> m, Class<K> keyType, Class<V> valueType) {
        return new CheckedMap<>(m, keyType, valueType);
    }

    private static class CheckedMap<K, V> implements Map<K, V>, java.io.Serializable {
        private final Map<K, V> m;
        final Class<K> keyType;
        final Class<V> valueType;
        private transient Set<Map.Entry<K, V>> entrySet;

        private void typeCheck(Object key, Object value) {
            if (key != null && !keyType.isInstance(key)) throw new ClassCastException(badKeyMsg(key));
            if (value != null && !valueType.isInstance(value)) throw new ClassCastException(badValueMsg(value));
        }

        private BiFunction<? super K, ? super V, ? extends V> typeCheck(BiFunction<? super K, ? super V, ? extends V> func) {
            requireNonNull(func);
            return (k, v) -> {
                V newValue = func.apply(k, v);
                typeCheck(k, newValue);
                return newValue;
            };
        }

        private String badKeyMsg(Object key) {
            return "Attempt to insert " + key.getClass() + " key into map with key type " + keyType;
        }

        private String badValueMsg(Object value) {
            return "Attempt to insert " + value.getClass() + " value into map with value type " + valueType;
        }

        CheckedMap(Map<K, V> m, Class<K> keyType, Class<V> valueType) {
            this.m = requireNonNull(m);
            this.keyType = requireNonNull(keyType);
            this.valueType = requireNonNull(valueType);
        }

        public int size() { return m.size(); }
        public boolean isEmpty() { return m.isEmpty(); }
        public boolean containsKey(Object key) { return m.containsKey(key); }
        public boolean containsValue(Object v) { return m.containsValue(v); }
        public V get(Object key) { return m.get(key); }
        public V remove(Object key) { return m.remove(key); }
        public void clear() { m.clear(); }
        public Set<K> keySet() { return m.keySet(); }
        public Collection<V> values() { return m.values(); }
        public boolean equals(Object o) { return o == this || m.equals(o); }
        public int hashCode() { return m.hashCode(); }
        public String toString() { return m.toString(); }

        public V put(K key, V value) {
            typeCheck(key, value);
            return m.put(key, value);
        }

        @SuppressWarnings("unchecked")
        public void putAll(Map<? extends K, ? extends V> t) {
            Object[] entries = t.entrySet().toArray();
            List<Map.Entry<K, V>> checked = new ArrayList<>(entries.length);
            for (Object o : entries) {
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                Object k = e.getKey();
                Object v = e.getValue();
                typeCheck(k, v);
                checked.add(new AbstractMap.SimpleImmutableEntry<>((K) k, (V) v));
            }
            for (Map.Entry<K, V> e : checked) m.put(e.getKey(), e.getValue());
        }

        public Set<Map.Entry<K, V>> entrySet() {
            if (entrySet == null) entrySet = new CheckedEntrySet<>(m.entrySet(), valueType);
            return entrySet;
        }

        public void forEach(BiConsumer<? super K, ? super V> action) { m.forEach(action); }
        public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) { m.replaceAll(typeCheck(function)); }

        public V putIfAbsent(K key, V value) {
            typeCheck(key, value);
            return m.putIfAbsent(key, value);
        }

        public boolean remove(Object key, Object value) { return m.remove(key, value); }

        public boolean replace(K key, V oldValue, V newValue) {
            typeCheck(key, newValue);
            return m.replace(key, oldValue, newValue);
        }

        public V replace(K key, V value) {
            typeCheck(key, value);
            return m.replace(key, value);
        }

        public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
            requireNonNull(mappingFunction);
            return m.computeIfAbsent(key, k -> {
                V value = mappingFunction.apply(k);
                typeCheck(k, value);
                return value;
            });
        }

        public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
            return m.computeIfPresent(key, typeCheck(remappingFunction));
        }

        public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
            return m.compute(key, typeCheck(remappingFunction));
        }

        public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
            requireNonNull(remappingFunction);
            return m.merge(key, value, (v1, v2) -> {
                V newValue = remappingFunction.apply(v1, v2);
                typeCheck(null, newValue);
                return newValue;
            });
        }

        static class CheckedEntrySet<K, V> implements Set<Map.Entry<K, V>> {
            private final Set<Map.Entry<K, V>> s;
            private final Class<V> valueType;

            CheckedEntrySet(Set<Map.Entry<K, V>> s, Class<V> valueType) {
                this.s = s;
                this.valueType = valueType;
            }

            public int size() { return s.size(); }
            public boolean isEmpty() { return s.isEmpty(); }
            public String toString() { return s.toString(); }
            public int hashCode() { return s.hashCode(); }
            public void clear() { s.clear(); }
            public boolean add(Map.Entry<K, V> e) { throw new UnsupportedOperationException(); }
            public boolean addAll(Collection<? extends Map.Entry<K, V>> coll) { throw new UnsupportedOperationException(); }

            public Iterator<Map.Entry<K, V>> iterator() {
                final Iterator<Map.Entry<K, V>> i = s.iterator();
                return new Iterator<Map.Entry<K, V>>() {
                    public boolean hasNext() { return i.hasNext(); }
                    public void remove() { i.remove(); }
                    public Map.Entry<K, V> next() { return checkedEntry(i.next(), valueType); }
                    public void forEachRemaining(Consumer<? super Map.Entry<K, V>> action) {
                        requireNonNull(action);
                        i.forEachRemaining(e -> action.accept(checkedEntry(e, valueType)));
                    }
                };
            }

            @SuppressWarnings("unchecked")
            public Object[] toArray() {
                Object[] source = s.toArray();
                Object[] dest = (source.getClass() == Object[].class) ? source : new Object[source.length];
                for (int i = 0; i < source.length; i++) dest[i] = checkedEntry((Map.Entry<K, V>) source[i], valueType);
                return dest;
            }

            @SuppressWarnings("unchecked")
            public <T> T[] toArray(T[] a) {
                T[] arr = s.toArray(a.length == 0 ? a : Arrays.copyOf(a, 0));
                for (int i = 0; i < arr.length; i++) arr[i] = (T) checkedEntry((Map.Entry<K, V>) arr[i], valueType);
                if (arr.length > a.length) return arr;
                System.arraycopy(arr, 0, a, 0, arr.length);
                if (a.length > arr.length) a[arr.length] = null;
                return a;
            }

            @SuppressWarnings({"unchecked", "rawtypes"})
            public boolean contains(Object o) {
                if (!(o instanceof Map.Entry)) return false;
                Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
                return s.contains((e instanceof CheckedEntry) ? e : checkedEntry((Map.Entry) e, valueType));
            }

            public boolean containsAll(Collection<?> c) {
                for (Object o : c) {
                    if (!contains(o)) return false;
                }
                return true;
            }

            public boolean remove(Object o) {
                if (!(o instanceof Map.Entry)) return false;
                return s.remove(new AbstractMap.SimpleImmutableEntry<>((Map.Entry<?, ?>) o));
            }

            public boolean removeAll(Collection<?> c) { return batchRemove(c, false); }
            public boolean retainAll(Collection<?> c) { return batchRemove(c, true); }

            private boolean batchRemove(Collection<?> c, boolean complement) {
                requireNonNull(c);
                boolean modified = false;
                Iterator<Map.Entry<K, V>> it = iterator();
                while (it.hasNext()) {
                    if (c.contains(it.next()) != complement) {
                        it.remove();
                        modified = true;
                    }
                }
                return modified;
            }

            public boolean equals(Object o) {
                if (o == this) return true;
                if (!(o instanceof Set)) return false;
                Set<?> that = (Set<?>) o;
                return that.size() == s.size() && containsAll(that);
            }

            static <K, V, T> CheckedEntry<K, V, T> checkedEntry(Map.Entry<K, V> e, Class<T> valueType) {
                return new CheckedEntry<>(e, valueType);
            }

            static class CheckedEntry<K, V, T> implements Map.Entry<K, V> {
                private final Map.Entry<K, V> e;
                private final Class<T> valueType;

                CheckedEntry(Map.Entry<K, V> e, Class<T> valueType) {
                    this.e = requireNonNull(e);
                    this.valueType = requireNonNull(valueType);
                }

                public K getKey() { return e.getKey(); }
                public V getValue() { return e.getValue(); }
                public int hashCode() { return e.hashCode(); }
                public String toString() { return e.toString(); }

                public V setValue(V value) {
                    if (value != null && !valueType.isInstance(value)) throw new ClassCastException(badValueMsg(value));
                    return e.setValue(value);
                }

                private String badValueMsg(Object value) {
                    return "Attempt to insert " + value.getClass() + " value into map with value type " + valueType;
                }

                public boolean equals(Object o) {
                    if (o == this) return true;
                    if (!(o instanceof Map.Entry)) return false;
                    return e.equals(new AbstractMap.SimpleImmutableEntry<>((Map.Entry<?, ?>) o));
                }
            }
        }
    }

    public static <K, V> SortedMap<K, V> checkedSortedMap(SortedMap<K, V> m, Class<K> keyType, Class<V> valueType) {
        return new CheckedSortedMap<>(m, keyType, valueType);
    }

    static class CheckedSortedMap<K, V> extends CheckedMap<K, V> implements SortedMap<K, V>, java.io.Serializable {
        private final SortedMap<K, V> sm;
        CheckedSortedMap(SortedMap<K, V> m, Class<K> keyType, Class<V> valueType) { super(m, keyType, valueType); sm = m; }
        public Comparator<? super K> comparator() { return sm.comparator(); }
        public K firstKey() { return sm.firstKey(); }
        public K lastKey() { return sm.lastKey(); }
        public SortedMap<K, V> subMap(K fromKey, K toKey) { return checkedSortedMap(sm.subMap(fromKey, toKey), keyType, valueType); }
        public SortedMap<K, V> headMap(K toKey) { return checkedSortedMap(sm.headMap(toKey), keyType, valueType); }
        public SortedMap<K, V> tailMap(K fromKey) { return checkedSortedMap(sm.tailMap(fromKey), keyType, valueType); }
    }

    public static <K, V> NavigableMap<K, V> checkedNavigableMap(NavigableMap<K, V> m, Class<K> keyType, Class<V> valueType) {
        return new CheckedNavigableMap<>(m, keyType, valueType);
    }

    static class CheckedNavigableMap<K, V> extends CheckedSortedMap<K, V> implements NavigableMap<K, V>, java.io.Serializable {
        private final NavigableMap<K, V> nm;
        CheckedNavigableMap(NavigableMap<K, V> m, Class<K> keyType, Class<V> valueType) { super(m, keyType, valueType); nm = m; }

        private Map.Entry<K, V> wrap(Map.Entry<K, V> e) {
            return (null != e) ? new CheckedMap.CheckedEntrySet.CheckedEntry<>(e, valueType) : null;
        }

        public Comparator<? super K> comparator() { return nm.comparator(); }
        public K firstKey() { return nm.firstKey(); }
        public K lastKey() { return nm.lastKey(); }
        public Map.Entry<K, V> lowerEntry(K key) { return wrap(nm.lowerEntry(key)); }
        public K lowerKey(K key) { return nm.lowerKey(key); }
        public Map.Entry<K, V> floorEntry(K key) { return wrap(nm.floorEntry(key)); }
        public K floorKey(K key) { return nm.floorKey(key); }
        public Map.Entry<K, V> ceilingEntry(K key) { return wrap(nm.ceilingEntry(key)); }
        public K ceilingKey(K key) { return nm.ceilingKey(key); }
        public Map.Entry<K, V> higherEntry(K key) { return wrap(nm.higherEntry(key)); }
        public K higherKey(K key) { return nm.higherKey(key); }
        public Map.Entry<K, V> firstEntry() { return wrap(nm.firstEntry()); }
        public Map.Entry<K, V> lastEntry() { return wrap(nm.lastEntry()); }
        public Map.Entry<K, V> pollFirstEntry() { return wrap(nm.pollFirstEntry()); }
        public Map.Entry<K, V> pollLastEntry() { return wrap(nm.pollLastEntry()); }
        public NavigableMap<K, V> descendingMap() { return checkedNavigableMap(nm.descendingMap(), keyType, valueType); }
        public NavigableSet<K> keySet() { return navigableKeySet(); }
        public NavigableSet<K> navigableKeySet() { return checkedNavigableSet(nm.navigableKeySet(), keyType); }
        public NavigableSet<K> descendingKeySet() { return checkedNavigableSet(nm.descendingKeySet(), keyType); }
        public NavigableMap<K, V> subMap(K fromKey, K toKey) { return checkedNavigableMap(nm.subMap(fromKey, true, toKey, false), keyType, valueType); }
        public NavigableMap<K, V> headMap(K toKey) { return checkedNavigableMap(nm.headMap(toKey, false), keyType, valueType); }
        public NavigableMap<K, V> tailMap(K fromKey) { return checkedNavigableMap(nm.tailMap(fromKey, true), keyType, valueType); }
        public NavigableMap<K, V> subMap(K fromKey, boolean fromInclusive, K toKey, boolean toInclusive) {
            return checkedNavigableMap(nm.subMap(fromKey, fromInclusive, toKey, toInclusive), keyType, valueType);
        }
        public NavigableMap<K, V> headMap(K toKey, boolean inclusive) { return checkedNavigableMap(nm.headMap(toKey, inclusive), keyType, valueType); }
        public NavigableMap<K, V> tailMap(K fromKey, boolean inclusive) { return checkedNavigableMap(nm.tailMap(fromKey, inclusive), keyType, valueType); }
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
            requireNonNull(action);
        }
    }

    @SuppressWarnings("unchecked")
    public static <T> ListIterator<T> emptyListIterator() {
        return (ListIterator<T>) EmptyListIterator.EMPTY_ITERATOR;
    }

    private static class EmptyListIterator<E> extends EmptyIterator<E> implements ListIterator<E> {
        static final EmptyListIterator<Object> EMPTY_ITERATOR = new EmptyListIterator<>();

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

    @SuppressWarnings("unchecked")
    public static <T> Enumeration<T> emptyEnumeration() {
        return (Enumeration<T>) EmptyEnumeration.EMPTY_ENUMERATION;
    }

    private static class EmptyEnumeration<E> implements Enumeration<E> {
        static final EmptyEnumeration<Object> EMPTY_ENUMERATION = new EmptyEnumeration<>();

        public boolean hasMoreElements() {
            return false;
        }

        public E nextElement() {
            throw new NoSuchElementException();
        }

        public Iterator<E> asIterator() {
            return emptyIterator();
        }
    }

    @SuppressWarnings("unchecked")
    public static final <T> Set<T> emptySet() {
        return (Set<T>) EMPTY_SET;
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
            if (c == null) throw npe("java.util.Collection.isEmpty()", "c");
            return c.isEmpty();
        }

        public Object[] toArray() {
            return new Object[0];
        }

        public <T> T[] toArray(T[] a) {
            if (a == null) throw ImmutableCollections.lengthOfNull("a");
            if (a.length > 0) a[0] = null;
            return a;
        }

        public void forEach(Consumer<? super E> action) {
            requireNonNull(action);
        }

        public boolean removeIf(Predicate<? super E> filter) {
            requireNonNull(filter);
            return false;
        }

        public int hashCode() {
            return 0;
        }
    }

    @SuppressWarnings("unchecked")
    public static <E> SortedSet<E> emptySortedSet() {
        return (SortedSet<E>) UnmodifiableNavigableSet.EMPTY_NAVIGABLE_SET;
    }

    @SuppressWarnings("unchecked")
    public static <E> NavigableSet<E> emptyNavigableSet() {
        return (NavigableSet<E>) UnmodifiableNavigableSet.EMPTY_NAVIGABLE_SET;
    }

    @SuppressWarnings("unchecked")
    public static final <T> List<T> emptyList() {
        return (List<T>) EMPTY_LIST;
    }

    private static class EmptyList<E> extends AbstractList<E> implements RandomAccess, java.io.Serializable {
        public Iterator<E> iterator() {
            return emptyIterator();
        }

        public ListIterator<E> listIterator() {
            return emptyListIterator();
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
            if (c == null) throw npe("java.util.Collection.isEmpty()", "c");
            return c.isEmpty();
        }

        public Object[] toArray() {
            return new Object[0];
        }

        public <T> T[] toArray(T[] a) {
            if (a == null) throw ImmutableCollections.lengthOfNull("a");
            if (a.length > 0) a[0] = null;
            return a;
        }

        public E get(int index) {
            throw new IndexOutOfBoundsException("Index: " + index);
        }

        public boolean equals(Object o) {
            return (o instanceof List) && ((List<?>) o).isEmpty();
        }

        public int hashCode() {
            return 1;
        }

        public boolean removeIf(Predicate<? super E> filter) {
            requireNonNull(filter);
            return false;
        }

        public void replaceAll(UnaryOperator<E> operator) {
            requireNonNull(operator);
        }

        public void sort(Comparator<? super E> c) {
        }

        public void forEach(Consumer<? super E> action) {
            requireNonNull(action);
        }
    }

    @SuppressWarnings("unchecked")
    public static final <K, V> Map<K, V> emptyMap() {
        return (Map<K, V>) EMPTY_MAP;
    }

    @SuppressWarnings("unchecked")
    public static final <K, V> SortedMap<K, V> emptySortedMap() {
        return (SortedMap<K, V>) UnmodifiableNavigableMap.EMPTY_NAVIGABLE_MAP;
    }

    @SuppressWarnings("unchecked")
    public static final <K, V> NavigableMap<K, V> emptyNavigableMap() {
        return (NavigableMap<K, V>) UnmodifiableNavigableMap.EMPTY_NAVIGABLE_MAP;
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
            requireNonNull(action);
        }

        public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
            requireNonNull(function);
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
            private boolean hasNext = true;

            public boolean hasNext() {
                return hasNext;
            }

            public E next() {
                if (hasNext) {
                    hasNext = false;
                    return e;
                }
                throw new NoSuchElementException();
            }

            public void remove() {
                throw new UnsupportedOperationException();
            }

            public void forEachRemaining(Consumer<? super E> action) {
                requireNonNull(action);
                if (hasNext) {
                    hasNext = false;
                    action.accept(e);
                }
            }
        };
    }

    /** The JDK's singletonSpliterator is the anonymous class Collections$2 (there is no
     *  Spliterator model): this placeholder keeps the JDK's numbering of the anonymous classes
     *  (singletonIterator $1, enumeration $3). Never called. */
    private static Object singletonSpliteratorPlaceholder() {
        return new Object() {
        };
    }

    private static NullPointerException acceptOnNull() {
        return npe("java.util.function.Consumer.accept(Object)", "action");
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
            if (action == null) throw acceptOnNull();
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
            if (index != 0) throw new IndexOutOfBoundsException("Index: " + index + ", Size: 1");
            return element;
        }

        public void forEach(Consumer<? super E> action) {
            if (action == null) throw acceptOnNull();
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

    public static <K, V> Map<K, V> singletonMap(K key, V value) {
        return new SingletonMap<>(key, value);
    }

    private static class SingletonMap<K, V> extends AbstractMap<K, V> implements java.io.Serializable {
        private final K k;
        private final V v;
        private transient Set<K> keySet;
        private transient Set<Map.Entry<K, V>> entrySet;
        private transient Collection<V> values;

        SingletonMap(K key, V value) {
            k = key;
            v = value;
        }

        public int size() {
            return 1;
        }

        public boolean isEmpty() {
            return false;
        }

        public boolean containsKey(Object key) {
            return eq(key, k);
        }

        public boolean containsValue(Object value) {
            return eq(value, v);
        }

        public V get(Object key) {
            return (eq(key, k) ? v : null);
        }

        public Set<K> keySet() {
            if (keySet == null) keySet = singleton(k);
            return keySet;
        }

        public Set<Map.Entry<K, V>> entrySet() {
            if (entrySet == null) entrySet = Collections.<Map.Entry<K, V>>singleton(new SimpleImmutableEntry<>(k, v));
            return entrySet;
        }

        public Collection<V> values() {
            if (values == null) values = singleton(v);
            return values;
        }

        public V getOrDefault(Object key, V defaultValue) {
            return eq(key, k) ? v : defaultValue;
        }

        public void forEach(BiConsumer<? super K, ? super V> action) {
            if (action == null) throw npe("java.util.function.BiConsumer.accept(Object, Object)", "action");
            action.accept(k, v);
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

        public int hashCode() {
            return AbstractMap.hashOf(k) ^ AbstractMap.hashOf(v);
        }
    }

    // ---- nCopies ----

    public static <T> List<T> nCopies(int n, T o) {
        if (n < 0) throw new IllegalArgumentException("List length = " + n);
        return new CopiesList<>(n, o);
    }

    private static class CopiesList<E> extends AbstractList<E> implements RandomAccess, java.io.Serializable {
        final int n;
        final E element;

        CopiesList(int n, E e) {
            this.n = n;
            element = e;
        }

        public int size() {
            return n;
        }

        public boolean contains(Object obj) {
            return n != 0 && eq(obj, element);
        }

        public int indexOf(Object o) {
            return contains(o) ? 0 : -1;
        }

        public int lastIndexOf(Object o) {
            return contains(o) ? n - 1 : -1;
        }

        public E get(int index) {
            Objects.checkIndex(index, n);
            return element;
        }

        public void forEach(Consumer<? super E> action) {
            requireNonNull(action);
            int n = this.n;
            E element = this.element;
            for (int i = 0; i < n; i++) action.accept(element);
        }

        public Object[] toArray() {
            final Object[] a = new Object[n];
            if (element != null) Arrays.fill(a, 0, n, element);
            return a;
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] a) {
            final int n = this.n;
            if (a == null) throw ImmutableCollections.lengthOfNull("a");
            if (a.length < n) {
                a = (T[]) java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), n);
                if (element != null) Arrays.fill(a, 0, n, element);
            } else {
                Arrays.fill(a, 0, n, element);
                if (a.length > n) a[n] = null;
            }
            return a;
        }

        public List<E> subList(int fromIndex, int toIndex) {
            if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex = " + fromIndex);
            if (toIndex > n) throw new IndexOutOfBoundsException("toIndex = " + toIndex);
            if (fromIndex > toIndex) throw new IllegalArgumentException("fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
            return new CopiesList<>(toIndex - fromIndex, element);
        }

        public int hashCode() {
            if (n == 0) return 1;
            // the hash of n copies, 31^n + sum 31^i * h, by repeated squaring as in the JDK
            int pow = 31;
            int sum = 1;
            for (int i = Integer.numberOfLeadingZeros(n) + 1; i < Integer.SIZE; i++) {
                sum *= pow + 1;
                pow *= pow;
                if ((n << i) < 0) {
                    pow *= 31;
                    sum = sum * 31 + 1;
                }
            }
            return pow + sum * (element == null ? 0 : element.hashCode());
        }

        public boolean equals(Object o) {
            if (o == this) return true;
            if (o instanceof CopiesList) {
                CopiesList<?> other = (CopiesList<?>) o;
                return n == other.n && (n == 0 || eq(element, other.element));
            }
            if (!(o instanceof List)) return false;
            int remaining = n;
            E e = element;
            Iterator<?> itr = ((List<?>) o).iterator();
            if (e == null) {
                while (itr.hasNext() && remaining-- > 0) {
                    if (itr.next() != null) return false;
                }
            } else {
                while (itr.hasNext() && remaining-- > 0) {
                    if (!e.equals(itr.next())) return false;
                }
            }
            return remaining == 0 && !itr.hasNext();
        }

        public Stream<E> stream() {
            return IntStream.range(0, n).mapToObj(i -> element);
        }
    }

    // ---- orderings (reverseOrder; the natural and null-tolerant comparators of Comparator) ----

    static final class NaturalOrder implements Comparator<Comparable<Object>>, java.io.Serializable {
        static final NaturalOrder INSTANCE = new NaturalOrder();

        public int compare(Comparable<Object> c1, Comparable<Object> c2) {
            if (c1 == null) throw npe("java.lang.Comparable.compareTo(Object)", "c1");
            return c1.compareTo(c2);
        }

        public Comparator<Comparable<Object>> reversed() {
            return Collections.reverseOrder();
        }
    }

    private static final class ReverseComparator implements Comparator<Comparable<Object>>, java.io.Serializable {
        static final ReverseComparator REVERSE_ORDER = new ReverseComparator();

        public int compare(Comparable<Object> c1, Comparable<Object> c2) {
            if (c2 == null) throw npe("java.lang.Comparable.compareTo(Object)", "c2");
            return c2.compareTo(c1);
        }

        @SuppressWarnings("unchecked")
        public Comparator<Comparable<Object>> reversed() {
            return (Comparator<Comparable<Object>>) (Comparator<?>) NaturalOrder.INSTANCE;
        }
    }

    private static final class ReverseComparator2<T> implements Comparator<T>, java.io.Serializable {
        final Comparator<T> cmp;

        ReverseComparator2(Comparator<T> cmp) {
            this.cmp = cmp;
        }

        public int compare(T t1, T t2) {
            return cmp.compare(t2, t1);
        }

        public boolean equals(Object o) {
            return (o == this) || (o instanceof ReverseComparator2 && cmp.equals(((ReverseComparator2<?>) o).cmp));
        }

        public int hashCode() {
            return cmp.hashCode() ^ Integer.MIN_VALUE;
        }

        public Comparator<T> reversed() {
            return cmp;
        }
    }

    static final class NullComparator<T> implements Comparator<T>, java.io.Serializable {
        private final boolean nullFirst;
        private final Comparator<T> real;

        @SuppressWarnings("unchecked")
        NullComparator(boolean nullFirst, Comparator<? super T> real) {
            this.nullFirst = nullFirst;
            this.real = (Comparator<T>) real;
        }

        public int compare(T a, T b) {
            if (a == null) return (b == null) ? 0 : (nullFirst ? -1 : 1);
            else if (b == null) return nullFirst ? 1 : -1;
            else return (real == null) ? 0 : real.compare(a, b);
        }

        public Comparator<T> thenComparing(Comparator<? super T> other) {
            if (other == null) throw new NullPointerException();
            return new NullComparator<>(nullFirst, real == null ? other : real.thenComparing(other));
        }

        public Comparator<T> reversed() {
            return new NullComparator<>(!nullFirst, real == null ? null : real.reversed());
        }
    }

    @SuppressWarnings("unchecked")
    public static <T> Comparator<T> reverseOrder() {
        return (Comparator<T>) ReverseComparator.REVERSE_ORDER;
    }

    @SuppressWarnings("unchecked")
    public static <T> Comparator<T> reverseOrder(Comparator<T> cmp) {
        if (cmp == null) return (Comparator<T>) ReverseComparator.REVERSE_ORDER;
        else if (cmp == ReverseComparator.REVERSE_ORDER) return (Comparator<T>) NaturalOrder.INSTANCE;
        else if (cmp == (Comparator<?>) NaturalOrder.INSTANCE) return (Comparator<T>) ReverseComparator.REVERSE_ORDER;
        else if (cmp instanceof ReverseComparator2) return ((ReverseComparator2<T>) cmp).cmp;
        else return new ReverseComparator2<>(cmp);
    }

    // ---- enumeration / list / frequency / disjoint / addAll ----

    public static <T> Enumeration<T> enumeration(final Collection<T> c) {
        if (c == null) throw npe("java.util.Collection.iterator()", "this.val$c");
        return new Enumeration<T>() {
            private final Iterator<T> i = c.iterator();

            public boolean hasMoreElements() {
                return i.hasNext();
            }

            public T nextElement() {
                return i.next();
            }
        };
    }

    public static <T> ArrayList<T> list(Enumeration<T> e) {
        ArrayList<T> l = new ArrayList<>();
        if (e == null) throw npe("java.util.Enumeration.hasMoreElements()", "e");
        while (e.hasMoreElements()) l.add(e.nextElement());
        return l;
    }

    public static int frequency(Collection<?> c, Object o) {
        if (c == null) throw npe("java.util.Collection.iterator()", "c");
        int result = 0;
        if (o == null) {
            for (Object e : c) {
                if (e == null) result++;
            }
        } else {
            for (Object e : c) {
                if (o.equals(e)) result++;
            }
        }
        return result;
    }

    public static boolean disjoint(Collection<?> c1, Collection<?> c2) {
        Collection<?> contains = c2;
        Collection<?> iterate = c1;
        if (c1 instanceof Set) {
            iterate = c2;
            contains = c1;
        } else if (!(c2 instanceof Set)) {
            if (c1 == null) throw npe("java.util.Collection.size()", "c1");
            int c1size = c1.size();
            if (c2 == null) throw npe("java.util.Collection.size()", "c2");
            int c2size = c2.size();
            if (c1size == 0 || c2size == 0) return true;
            if (c1size > c2size) {
                iterate = c2;
                contains = c1;
            }
        }
        if (iterate == null) throw npe("java.util.Collection.iterator()", "iterate");
        for (Object e : iterate) {
            if (contains.contains(e)) return false;
        }
        return true;
    }

    @SafeVarargs
    public static <T> boolean addAll(Collection<? super T> c, T... elements) {
        boolean result = false;
        if (elements == null) throw new NullPointerException("Cannot read the array length because \"<local3>\" is null");
        for (T element : elements) {
            if (c == null) throw npe("java.util.Collection.add(Object)", "c");
            result |= c.add(element);
        }
        return result;
    }

    // ---- newSetFromMap / asLifoQueue ----

    public static <E> Set<E> newSetFromMap(Map<E, Boolean> map) {
        if (map == null) throw npe("java.util.Map.isEmpty()", "map");
        if (!map.isEmpty()) throw new IllegalArgumentException("Map is non-empty");
        return new SetFromMap<>(map);
    }

    private static class SetFromMap<E> extends AbstractSet<E> implements Set<E>, java.io.Serializable {
        final Map<E, Boolean> m;
        private transient Set<E> s;

        SetFromMap(Map<E, Boolean> map) {
            m = map;
            s = map.keySet();
        }

        public void clear() { m.clear(); }
        public int size() { return m.size(); }
        public boolean isEmpty() { return m.isEmpty(); }
        public boolean contains(Object o) { return m.containsKey(o); }
        public boolean remove(Object o) { return m.remove(o) != null; }
        public boolean add(E e) { return m.put(e, Boolean.TRUE) == null; }
        public Iterator<E> iterator() { return s.iterator(); }
        public Object[] toArray() { return s.toArray(); }
        public <T> T[] toArray(T[] a) { return s.toArray(a); }
        public String toString() { return s.toString(); }
        public int hashCode() { return s.hashCode(); }
        public boolean equals(Object o) { return o == this || s.equals(o); }
        public boolean containsAll(Collection<?> c) { return s.containsAll(c); }
        public boolean removeAll(Collection<?> c) { return s.removeAll(c); }
        public boolean retainAll(Collection<?> c) { return s.retainAll(c); }
        public void forEach(Consumer<? super E> action) { s.forEach(action); }
        public boolean removeIf(Predicate<? super E> filter) { return s.removeIf(filter); }
        public Stream<E> stream() { return s.stream(); }
    }

    public static <T> Queue<T> asLifoQueue(Deque<T> deque) {
        return new AsLIFOQueue<>(requireNonNull(deque));
    }

    static class AsLIFOQueue<E> extends AbstractQueue<E> implements Queue<E>, java.io.Serializable {
        private final Deque<E> q;

        AsLIFOQueue(Deque<E> q) { this.q = q; }
        public boolean add(E e) { q.addFirst(e); return true; }
        public boolean offer(E e) { return q.offerFirst(e); }
        public E poll() { return q.pollFirst(); }
        public E remove() { return q.removeFirst(); }
        public E peek() { return q.peekFirst(); }
        public E element() { return q.getFirst(); }
        public void clear() { q.clear(); }
        public int size() { return q.size(); }
        public boolean isEmpty() { return q.isEmpty(); }
        public boolean contains(Object o) { return q.contains(o); }
        public boolean remove(Object o) { return q.remove(o); }
        public Iterator<E> iterator() { return q.iterator(); }
        public Object[] toArray() { return q.toArray(); }
        public <T> T[] toArray(T[] a) { return q.toArray(a); }
        public String toString() { return q.toString(); }
        public boolean containsAll(Collection<?> c) { return q.containsAll(c); }
        public boolean removeAll(Collection<?> c) { return q.removeAll(c); }
        public boolean retainAll(Collection<?> c) { return q.retainAll(c); }
        public void forEach(Consumer<? super E> action) { q.forEach(action); }
        public boolean removeIf(Predicate<? super E> filter) { return q.removeIf(filter); }
        public Stream<E> stream() { return q.stream(); }
    }
}

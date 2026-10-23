package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of the skeletal implementations: a user AbstractList (fixed array plus
 *  set/add/remove, with modCount) and a user AbstractMap (entry set over an ArrayList of
 *  SimpleEntry), so that AbstractList's iterators/equals/hashCode/indexOf/clear/addAll and
 *  AbstractMap's entrySet-based get/containsKey/remove/keySet/values/equals/hashCode run. */
public final class AbsOps {
    private AbsOps() {
    }

    /** Array-backed list written against AbstractList's contract. */
    static final class AList extends AbstractList<Object> {
        Object[] a = new Object[4];
        int n;
        final boolean mutable;

        AList(boolean mutable) {
            this.mutable = mutable;
        }

        public Object get(int i) {
            if (i < 0 || i >= n) throw new IndexOutOfBoundsException();
            return a[i];
        }

        public int size() {
            return n;
        }

        public Object set(int i, Object e) {
            if (!mutable) return super.set(i, e);
            Object old = get(i);
            a[i] = e;
            return old;
        }

        public void add(int i, Object e) {
            if (!mutable) {
                super.add(i, e);
                return;
            }
            if (i < 0 || i > n) throw new IndexOutOfBoundsException();
            if (n == a.length) {
                Object[] b = new Object[2 * n];
                for (int j = 0; j < n; j++) b[j] = a[j];
                a = b;
            }
            for (int j = n; j > i; j--) a[j] = a[j - 1];
            a[i] = e;
            n++;
            modCount++;
        }

        public Object remove(int i) {
            if (!mutable) return super.remove(i);
            Object old = get(i);
            for (int j = i; j < n - 1; j++) a[j] = a[j + 1];
            a[--n] = null;
            modCount++;
            return old;
        }
    }

    /** Map whose only state is its entry set. */
    static final class AMap extends AbstractMap<Object, Object> {
        final ArrayList<Map.Entry<Object, Object>> es = new ArrayList<>();
        final boolean mutable;

        AMap(boolean mutable) {
            this.mutable = mutable;
        }

        public Set<Map.Entry<Object, Object>> entrySet() {
            return new AbstractSet<Map.Entry<Object, Object>>() {
                public Iterator<Map.Entry<Object, Object>> iterator() {
                    return es.iterator();
                }

                public int size() {
                    return es.size();
                }
            };
        }

        public Object put(Object k, Object v) {
            if (!mutable) return super.put(k, v);
            for (Map.Entry<Object, Object> e : es) {
                if (Objects.equals(e.getKey(), k)) return e.setValue(v);
            }
            es.add(es.size() % 3 == 1 ? new AbstractMap.SimpleEntry<>(k, v) : new AbstractMap.SimpleEntry<>(new AbstractMap.SimpleImmutableEntry<>(k, v)));
            return null;
        }
    }

    public static int abstractList(int seed, int in) {
        T t = new T(seed);
        AList l = new AList(t.chance(85));
        for (int i = 0; i < 40; i++) {
            try {
                int op = t.r(14);
                switch (op) {
                    case 0: case 1: case 2:
                        t.f(l.add(ListOps.elem(t)));
                        break;
                    case 3:
                        l.add(ListOps.idx(t, l, in), ListOps.elem(t));
                        break;
                    case 4:
                        t.f(l.indexOf(ListOps.elem(t)));
                        t.f(l.lastIndexOf(ListOps.elem(t)));
                        t.f(l.contains(ListOps.elem(t)));
                        break;
                    case 5: {
                        Iterator<Object> it = l.iterator();
                        while (it.hasNext()) {
                            t.fo(it.next());
                            if (t.chance(25)) it.remove();
                        }
                        if (t.chance(30)) it.next();
                        if (t.chance(30)) it.remove();
                        break;
                    }
                    case 6: {
                        ListIterator<Object> it = l.listIterator(ListOps.idx(t, l, in));
                        int n = t.r(8);
                        for (int j = 0; j < n; j++) {
                            int w = t.r(7);
                            if (w == 0) t.fo(it.next());
                            else if (w == 1) t.fo(it.previous());
                            else if (w == 2) it.add(ListOps.elem(t));
                            else if (w == 3) it.set(ListOps.elem(t));
                            else if (w == 4) it.remove();
                            else t.f(it.hasNext() ? it.nextIndex() : -it.previousIndex());
                        }
                        break;
                    }
                    case 7: {
                        Iterator<Object> it = l.iterator();
                        if (it.hasNext()) t.fo(it.next());
                        l.add(ListOps.elem(t));
                        t.fo(it.next());
                        break;
                    }
                    case 8: {
                        ArrayList<Object> c = new ArrayList<>();
                        int n = t.r(4);
                        for (int j = 0; j < n; j++) c.add(ListOps.elem(t));
                        int w = t.r(5);
                        if (w == 0) t.f(l.addAll(ListOps.idx(t, l, in), c));
                        else if (w == 1) t.f(l.removeAll(c));
                        else if (w == 2) t.f(l.retainAll(c));
                        else if (w == 3) t.f(l.addAll(c));
                        else t.f(l.containsAll(c));
                        break;
                    }
                    case 9: {
                        ArrayList<Object> c = new ArrayList<>(l);
                        t.f(l.equals(c));
                        t.f(c.equals(l));
                        t.f(l.hashCode());
                        if (!c.isEmpty() && t.chance(50)) c.remove(c.size() - 1);
                        t.f(l.equals(c));
                        t.f(l.equals(new AList(true)));
                        break;
                    }
                    case 10:
                        if (t.chance(25)) l.clear();
                        t.f(l.size());
                        break;
                    case 11:
                        t.f(l.remove(ListOps.elem(t)));
                        break;
                    case 12:
                        l.replaceAll(o -> o == null ? (Object) 0 : o);
                        break;
                    default: {
                        Object[] a = l.toArray();
                        for (Object o : a) t.fo(o);
                        t.f(a.length);
                        t.f(l.toArray(new Object[t.r(4)]).length);
                        break;
                    }
                }
            } catch (RuntimeException e) {
                t.fe(e);
            }
        }
        ListOps.fold(t, l);
        return t.acc;
    }

    public static int abstractMap(int seed) {
        T t = new T(seed);
        AMap m = new AMap(t.chance(85));
        int fam = 1 + t.r(2);
        int range = 4 + t.r(20);
        for (int i = 0; i < 30; i++) {
            try {
                Object k = MapOps.key(t, fam, 0, range);
                int op = t.r(16);
                switch (op) {
                    case 0: case 1: case 2: case 3:
                        t.fo(m.put(k, MapOps.val(t)));
                        break;
                    case 4:
                        t.fo(m.get(k));
                        t.f(m.containsKey(k));
                        t.f(m.containsValue(MapOps.val(t)));
                        break;
                    case 5:
                        t.fo(m.remove(k));
                        break;
                    case 6:
                        MapOps.foldViews(t, m);
                        break;
                    case 7: {
                        HashMap<Object, Object> h = new HashMap<>(m);
                        t.f(m.equals(h));
                        t.f(h.equals(m));
                        t.f(m.hashCode());
                        t.f(m.hashCode() == h.hashCode());
                        t.f(m.keySet().equals(h.keySet()));
                        if (t.chance(50)) h.put(k, -1);
                        t.f(m.equals(h));
                        break;
                    }
                    case 8:
                        t.fo(m.getOrDefault(k, 42));
                        t.fo(m.putIfAbsent(k, MapOps.val(t)));
                        break;
                    case 9: {
                        Iterator<Object> it = m.keySet().iterator();
                        while (it.hasNext()) {
                            t.fo(it.next());
                            if (t.chance(30)) it.remove();
                        }
                        Iterator<Object> vi = m.values().iterator();
                        while (vi.hasNext()) {
                            t.fo(vi.next());
                            if (t.chance(20)) vi.remove();
                        }
                        break;
                    }
                    case 10:
                        t.fo(m.computeIfAbsent(k, x -> 9));
                        t.fo(m.merge(k, 1, (a, b) -> (Integer) a + (Integer) b));
                        t.fo(m.compute(k, (x, v) -> v == null ? null : (Object) ((Integer) v + 1)));
                        t.fo(m.computeIfPresent(k, (x, v) -> (Integer) v % 2 == 0 ? null : v));
                        break;
                    case 11:
                        t.f(m.remove(k, MapOps.val(t)));
                        t.f(m.replace(k, MapOps.val(t), MapOps.val(t)));
                        t.fo(m.replace(k, MapOps.val(t)));
                        break;
                    case 12: {
                        for (Map.Entry<Object, Object> e : m.entrySet()) {
                            t.f(e.equals(new AbstractMap.SimpleEntry<>(e.getKey(), e.getValue())));
                            t.f(e.hashCode());
                            t.fo(e.setValue(MapOps.val(t)));
                        }
                        break;
                    }
                    case 13: {
                        HashMap<Object, Object> h = new HashMap<>();
                        h.put(k, 3);
                        m.putAll(h);
                        t.f(m.size());
                        t.f(m.isEmpty());
                        break;
                    }
                    case 14: {
                        final T tt = t;
                        m.forEach((a, b) -> tt.f(T.code(a) - T.code(b)));
                        m.replaceAll((a, b) -> b == null ? (Object) 1 : b);
                        break;
                    }
                    default:
                        if (t.chance(30)) m.clear();
                        t.f(m.keySet().contains(k));
                        t.f(m.values().contains(3));
                        break;
                }
            } catch (RuntimeException e) {
                t.fe(e);
            }
        }
        MapOps.foldViews(t, m);
        return t.acc;
    }
}

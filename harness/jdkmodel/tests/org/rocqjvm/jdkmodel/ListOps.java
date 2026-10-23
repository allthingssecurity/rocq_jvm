package org.rocqjvm.jdkmodel;

import java.util.*;

/** Differential tests of ArrayList (and AbstractList / AbstractCollection through it). */
public final class ListOps {
    private ListOps() {
    }

    static Object elem(T t) {
        if (t.chance(6)) return null;
        return t.chance(30) ? (Object) ("e" + t.r(9)) : (Object) t.r(12);
    }

    static void fold(T t, List<Object> l) {
        for (Object o : l) t.fo(o);
        t.f(l.size());
    }

    /** idx: an index near the bounds, sometimes from the input. */
    static int idx(T t, List<?> l, int in) {
        int w = t.r(8);
        if (w == 0) return in;
        if (w == 1) return -1;
        if (w == 2) return l.size();
        if (w == 3) return l.size() + 1;
        return t.r(l.size() + 1);
    }

    static void step(T t, ArrayList<Object> l, int in) {
        int op = t.r(30);
        try {
            switch (op) {
                case 0: case 1: case 2:
                    t.f(l.add(elem(t)));
                    break;
                case 3:
                    l.add(idx(t, l, in), elem(t));
                    break;
                case 4:
                    t.fo(l.get(idx(t, l, in)));
                    break;
                case 5:
                    t.fo(l.set(idx(t, l, in), elem(t)));
                    break;
                case 6:
                    t.fo(l.remove(idx(t, l, in)));
                    break;
                case 7:
                    t.f(l.remove(elem(t)));
                    break;
                case 8:
                    t.f(l.indexOf(elem(t)));
                    t.f(l.lastIndexOf(elem(t)));
                    t.f(l.contains(elem(t)));
                    break;
                case 9: {
                    Iterator<Object> it = l.iterator();
                    while (it.hasNext()) {
                        t.fo(it.next());
                        if (t.chance(25)) it.remove();
                    }
                    if (t.chance(30)) it.next();
                    break;
                }
                case 10: {
                    ListIterator<Object> it = l.listIterator(idx(t, l, in));
                    int n = t.r(8);
                    for (int i = 0; i < n; i++) {
                        int w = t.r(8);
                        if (w == 0 && it.hasNext()) t.fo(it.next());
                        else if (w == 1 && it.hasPrevious()) t.fo(it.previous());
                        else if (w == 2) it.add(elem(t));
                        else if (w == 3) it.set(elem(t));
                        else if (w == 4) it.remove();
                        else if (w == 5) t.fo(it.next());
                        else if (w == 6) t.fo(it.previous());
                        t.f(it.nextIndex());
                        t.f(it.previousIndex());
                    }
                    break;
                }
                case 11: {   // fail-fast
                    Iterator<Object> it = l.iterator();
                    if (it.hasNext()) t.fo(it.next());
                    int w = t.r(5);
                    if (w == 0) l.add(elem(t));
                    else if (w == 1 && !l.isEmpty()) l.remove(0);
                    else if (w == 2 && !l.isEmpty()) l.set(0, elem(t));
                    else if (w == 3) l.ensureCapacity(t.r(30));
                    else l.trimToSize();
                    t.f(it.hasNext());
                    t.fo(it.next());
                    it.remove();
                    break;
                }
                case 12: {
                    ArrayList<Object> c = new ArrayList<>();
                    int n = t.r(5);
                    for (int i = 0; i < n; i++) c.add(elem(t));
                    int w = t.r(5);
                    if (w == 0) t.f(l.addAll(c));
                    else if (w == 1) t.f(l.addAll(idx(t, l, in), c));
                    else if (w == 2) t.f(l.removeAll(c));
                    else if (w == 3) t.f(l.retainAll(c));
                    else t.f(l.containsAll(c));
                    break;
                }
                case 13: {
                    final int salt = t.r(4);
                    t.f(l.removeIf(o -> (T.code(o) + salt) % 3 == 0));
                    break;
                }
                case 14: {
                    final ArrayList<Object> ll = l;
                    final T tt = t;
                    final boolean modify = t.chance(20);
                    l.forEach(o -> {
                        tt.fo(o);
                        if (modify) ll.add(1);
                    });
                    break;
                }
                case 15:
                    l.replaceAll(o -> o instanceof Integer ? (Object) ((Integer) o + 1) : o);
                    break;
                case 16: {
                    List<Object> other = t.chance(50) ? new ArrayList<>(l) : Arrays.asList(l.toArray());
                    t.f(l.equals(other));
                    t.f(other.equals(l));
                    t.f(l.hashCode());
                    t.f(other.hashCode());
                    if (!other.isEmpty()) other.set(t.r(other.size()), elem(t));
                    t.f(l.equals(other));
                    break;
                }
                case 17: {
                    Object[] a = l.toArray();
                    t.f(a.length);
                    for (Object o : a) t.fo(o);
                    Object[] b = l.toArray(new Object[t.r(l.size() + 3)]);
                    t.f(b.length);
                    for (Object o : b) t.fo(o);
                    break;
                }
                case 18:
                    if (t.chance(20)) l.clear();
                    break;
                case 19: {   // iterator misuse and ListIterator after modification
                    ListIterator<Object> it = l.listIterator();
                    if (t.chance(50)) it.set(elem(t));
                    if (t.chance(50)) it.remove();
                    if (it.hasNext()) {
                        t.fo(it.next());
                        it.add(elem(t));
                        it.set(elem(t));
                    }
                    break;
                }
                case 20: {
                    Iterator<Object> it = l.iterator();
                    if (it.hasNext()) t.fo(it.next());
                    final T tt = t;
                    it.forEachRemaining(o -> tt.fo(o));
                    t.f(it.hasNext());
                    it.remove();
                    break;
                }
                case 21: {   // ensureCapacity's modCount depends on the capacity (growth policy)
                    Iterator<Object> it = l.iterator();
                    l.ensureCapacity(t.r(40));
                    t.fo(it.next());
                    break;
                }
                default:
                    t.f(l.size());
                    t.f(l.isEmpty());
                    break;
            }
        } catch (RuntimeException e) {
            t.fe(e);
        }
    }

    public static int arrayList(int seed, int in) {
        T t = new T(seed);
        ArrayList<Object> l;
        try {
            int w = t.r(4);
            if (w == 0) l = new ArrayList<>();
            else if (w == 1) l = new ArrayList<>(t.chance(80) ? t.r(15) : (in % 50));
            else if (w == 2) l = new ArrayList<>(Arrays.asList(elem(t), elem(t), elem(t)));
            else l = new ArrayList<>(new HashSet<>(Arrays.asList(1, 2, 3, 40, 17)));
        } catch (RuntimeException e) {
            t.fe(e);
            l = new ArrayList<>(0);
        }
        int steps = 40;
        for (int i = 0; i < steps; i++) step(t, l, in);
        fold(t, l);
        return t.acc;
    }
}

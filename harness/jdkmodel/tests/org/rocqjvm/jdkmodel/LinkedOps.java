package org.rocqjvm.jdkmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;

/** Differential tests of LinkedList (List and Deque operations, list iterators with
 *  modification, fail-fast iteration, sub lists, clone, messages). */
public final class LinkedOps {
    private LinkedOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static String el() {
        return r(8) == 0 ? null : "e" + r(5);
    }

    public static String ops(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        LinkedList<String> l = new LinkedList<>();
        for (int i = r(5); i > 0; i--) l.add(el());
        ListIterator<String> it = null;
        List<String> sub = null;
        int ops = 8 + r(16);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(26)) {
                    case 0: case 1: l.add(el()); break;
                    case 2: l.add(r(6) - 1, el()); break;
                    case 3: out.append(l.get(r(6) - 1)); break;
                    case 4: out.append(l.set(r(6) - 1, el())); break;
                    case 5: out.append(l.remove(r(6) - 1)); break;
                    case 6: out.append(l.remove((Object) el())); break;
                    case 7: l.addFirst(el()); out.append(l.peekLast()); break;
                    case 8: out.append(l.pollFirst()).append(l.pollLast()); break;
                    case 9: out.append(l.removeFirst()); break;
                    case 10: out.append(l.getLast()); break;
                    case 11: out.append(l.removeLastOccurrence(el())).append(l.removeFirstOccurrence(el())); break;
                    case 12: out.append(l.indexOf(el())).append(l.lastIndexOf(el())); break;
                    case 13: it = l.listIterator(r(5)); out.append(it.nextIndex()); break;
                    case 14: if (it != null) out.append(it.hasNext() ? it.next() : it.hasPrevious() ? it.previous() : "-"); break;
                    case 15: if (it != null) it.remove(); break;
                    case 16: if (it != null) it.add("i" + k); break;
                    case 17: if (it != null) it.set("s" + k); break;
                    case 18: { Iterator<String> d = l.descendingIterator(); while (d.hasNext()) out.append(d.next()); break; }
                    case 19: out.append(l.addAll(r(5) - 1, Arrays.asList("a", "b"))); break;
                    case 20: { @SuppressWarnings("unchecked") LinkedList<String> c = (LinkedList<String>) l.clone(); c.push("p"); out.append(c).append(c.equals(l)).append(c.hashCode()); break; }
                    case 21: sub = l.subList(r(3), Math.min(l.size(), r(4) + 1)); out.append(sub).append(sub.size()); break;
                    case 22: if (sub != null) { sub.add("q"); out.append(sub); } break;
                    case 23: out.append(Arrays.toString(l.toArray(new String[r(4)]))).append(l.equals(new ArrayList<>(l))); break;
                    case 24: out.append(l.removeIf(x -> x == null || x.endsWith("2"))); break;
                    default: out.append(l.pop()).append(l.element()); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(l).append(';');
        }
        return out.toString();
    }
}

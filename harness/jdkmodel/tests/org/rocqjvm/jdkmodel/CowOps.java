package org.rocqjvm.jdkmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.ConcurrentLinkedDeque;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.CopyOnWriteArraySet;

/** Differential tests (one thread) of CopyOnWriteArrayList/Set, ConcurrentLinkedQueue/Deque:
 *  random operation sequences, including modification during iteration (snapshot and weakly
 *  consistent iterators), sub lists and their co-modification checks, and the exceptions. */
public final class CowOps {
    private CowOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static String el() {
        return r(9) == 0 ? null : "e" + r(6);
    }

    static String ex(RuntimeException e) {
        return "!" + e.getClass().getSimpleName() + ":" + e.getMessage();
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String cowList(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        CopyOnWriteArrayList<String> l = r(2) == 0 ? new CopyOnWriteArrayList<>()
            : new CopyOnWriteArrayList<>(Arrays.asList("e1", "e2", null));
        List<String> sub = null;
        Iterator<String> it = null;
        int ops = 8 + r(14);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(24)) {
                    case 0: case 1: out.append(l.add(el())); break;
                    case 2: l.add(r(5) - 1, el()); break;
                    case 3: out.append(l.remove(r(5) - 1)); break;
                    case 4: out.append(l.remove((Object) el())); break;
                    case 5: out.append(l.set(r(4) - 1, el())); break;
                    case 6: out.append(l.get(r(4) - 1)); break;
                    case 7: out.append(l.addIfAbsent(el())); break;
                    case 8: out.append(l.addAllAbsent(Arrays.asList(el(), el(), el()))); break;
                    case 9: out.append(l.indexOf(el())).append(l.lastIndexOf(el())).append(l.indexOf(el(), r(3))).append(l.lastIndexOf(el(), r(3))); break;
                    case 10: out.append(l.removeIf(x -> x == null || x.endsWith(String.valueOf(r(3))))); break;
                    case 11: out.append(l.addAll(r(4) - 1, Arrays.asList("a", "b"))); break;
                    case 12: sub = l.subList(r(3) - 1 + 1, r(4)); out.append(sub); break;
                    case 13: if (sub != null) { out.append(sub.size()); sub.add("s"); out.append(sub).append(l); } break;
                    case 14: if (sub != null) { out.append(sub.get(r(3) - 1)); out.append(sub.remove(0)); } break;
                    case 15: it = l.iterator(); out.append(it.hasNext()); break;
                    case 16: if (it != null) { while (it.hasNext()) out.append(it.next()); it.next(); } break;
                    case 17: if (it != null) it.remove(); break;
                    case 18: { ListIterator<String> li = l.listIterator(r(4)); out.append(li.nextIndex()).append(li.hasPrevious() ? li.previous() : "-"); li.set("x"); break; }
                    case 19: out.append(l.equals(new ArrayList<>(l))).append(l.hashCode()).append(l.containsAll(Arrays.asList(el()))); break;
                    case 20: l.replaceAll(x -> x == null ? "N" : x + "!"); break;
                    case 21: l.sort((a, b) -> String.valueOf(a).compareTo(String.valueOf(b))); break;
                    case 22: out.append(l.retainAll(Arrays.asList("e1", "e2", "e3", null))).append(l.removeAll(Arrays.asList(el()))); break;
                    default: out.append(Arrays.toString(l.toArray())).append(Arrays.toString(l.toArray(new String[r(5)]))); if (sub != null) out.append(sub.hashCode()); break;
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(l).append(';');
        }
        return out.toString();
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String cowSet(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        CopyOnWriteArraySet<String> st = new CopyOnWriteArraySet<>(r(2) == 0 ? List.<String>of() : Arrays.asList("e1", "e2", "e1"));
        int ops = 8 + r(12);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(9)) {
                    case 0: case 1: out.append(st.add(el())); break;
                    case 2: out.append(st.remove(el())); break;
                    case 3: out.append(st.contains(el())); break;
                    case 4: out.append(st.addAll(Arrays.asList(el(), el()))); break;
                    case 5: out.append(st.equals(new java.util.HashSet<>(Arrays.asList(el(), el())))).append(st.equals(new java.util.HashSet<>(st))); break;
                    case 6: out.append(st.containsAll(new java.util.HashSet<>(Arrays.asList(el())))).append(st.containsAll(Arrays.asList(el()))); break;
                    case 7: { Iterator<String> it = st.iterator(); st.add("late"); while (it.hasNext()) out.append(it.next()); break; }
                    default: out.append(st.hashCode()).append(st.size()); break;
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(st).append(';');
        }
        return out.toString();
    }

    public static String linkedQueue(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        ConcurrentLinkedQueue<String> q = new ConcurrentLinkedQueue<>();
        Iterator<String> it = null;
        int ops = 8 + r(16);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(14)) {
                    case 0: case 1: case 2: out.append(q.offer(el())); break;
                    case 3: out.append(q.poll()); break;
                    case 4: out.append(q.peek()).append(q.isEmpty()); break;
                    case 5: out.append(q.remove(el())); break;
                    case 6: out.append(q.contains(el())); break;
                    case 7: out.append(q.addAll(Arrays.asList(el(), el()))); break;
                    case 8: it = q.iterator(); out.append(it.hasNext()); break;
                    case 9: if (it != null) out.append(it.next()); break;
                    case 10: if (it != null) it.remove(); break;
                    case 11: out.append(q.size()).append(Arrays.toString(q.toArray())); break;
                    case 12: out.append(q.removeIf(x -> x.endsWith("1"))); break;
                    default: out.append(q.remove()).append(q.element()); break;
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(q).append(';');
        }
        return out.toString();
    }

    public static String linkedDeque(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        ConcurrentLinkedDeque<String> d = new ConcurrentLinkedDeque<>();
        Iterator<String> it = null;
        int ops = 8 + r(16);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(18)) {
                    case 0: case 1: d.addFirst(el()); break;
                    case 2: case 3: out.append(d.offerLast(el())); break;
                    case 4: out.append(d.pollFirst()).append(d.pollLast()); break;
                    case 5: out.append(d.peekFirst()).append(d.peekLast()); break;
                    case 6: out.append(d.getFirst()); break;
                    case 7: out.append(d.removeLast()); break;
                    case 8: out.append(d.removeFirstOccurrence(el())); break;
                    case 9: out.append(d.removeLastOccurrence(el())); break;
                    case 10: out.append(d.contains(el())); break;
                    case 11: it = r(2) == 0 ? d.iterator() : d.descendingIterator(); out.append(it.hasNext()); break;
                    case 12: if (it != null) out.append(it.next()); break;
                    case 13: if (it != null) it.remove(); break;
                    case 14: d.push(el()); out.append(d.pop()); break;
                    case 15: out.append(d.size()).append(Arrays.toString(d.toArray(new String[r(3)]))); break;
                    case 16: out.append(d.addAll(Arrays.asList(el(), el()))); break;
                    default: out.append(d.remove(el())); break;
                }
            } catch (RuntimeException e) {
                out.append(ex(e));
            }
            out.append(d).append(';');
        }
        return out.toString();
    }
}

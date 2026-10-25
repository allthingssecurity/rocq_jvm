package org.rocqjvm.jdkmodel;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Iterator;
import java.util.NoSuchElementException;

/** Differential tests of the ArrayDeque/Deque/Queue model against the JDK (written by the r82 Camel hunt session). */
public final class DequeTests {
    static int next(int[] s) {
        s[0] = s[0] * 1103515245 + 12345;
        return (s[0] >>> 8) & 0xffff;
    }

    /** n random operations of the Deque API on Integers 0..9 (with boxing), the trace of results. */
    public static String ops(int seed) {
        int[] s = { seed };
        int n = 1 + next(s) % 60;
        Deque<Integer> d = (next(s) & 1) == 0 ? new ArrayDeque<>() : new ArrayDeque<>(1 + next(s) % 4);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < n; i++) {
            int op = next(s) % 24, v = next(s) % 10;
            try {
                switch (op) {
                    case 0: d.addFirst(v); sb.append('a'); break;
                    case 1: d.addLast(v); sb.append('b'); break;
                    case 2: sb.append(d.offerFirst(v)); break;
                    case 3: sb.append(d.offerLast(v)); break;
                    case 4: sb.append(d.removeFirst()); break;
                    case 5: sb.append(d.removeLast()); break;
                    case 6: sb.append(d.pollFirst()); break;
                    case 7: sb.append(d.pollLast()); break;
                    case 8: sb.append(d.getFirst()); break;
                    case 9: sb.append(d.getLast()); break;
                    case 10: sb.append(d.peekFirst()); break;
                    case 11: sb.append(d.peekLast()); break;
                    case 12: sb.append(d.removeFirstOccurrence(v)); break;
                    case 13: sb.append(d.removeLastOccurrence(v)); break;
                    case 14: sb.append(d.add(v)); break;
                    case 15: sb.append(d.poll()); break;
                    case 16: sb.append(d.element()); break;
                    case 17: d.push(v); sb.append('p'); break;
                    case 18: sb.append(d.pop()); break;
                    case 19: sb.append(d.contains(v)); break;
                    case 20: sb.append(d.size()).append(d.isEmpty()); break;
                    case 21: d.clear(); sb.append('c'); break;
                    case 22: {
                        Iterator<Integer> it = (v & 1) == 0 ? d.iterator() : d.descendingIterator();
                        int k = 0;
                        while (it.hasNext()) {
                            int x = it.next();
                            sb.append(x);
                            if (x == v || (k++ == 1 && (v & 2) != 0)) it.remove();
                        }
                        break;
                    }
                    default: sb.append(d.remove(Integer.valueOf(v))); break;
                }
            } catch (NoSuchElementException e) {
                sb.append('!');
            } catch (IllegalStateException e) {
                sb.append('?');
            }
            sb.append(',');
        }
        return sb.append(d).toString();
    }

    /** null handling: NPE on null elements, false on null queries. */
    public static String nulls(int seed) {
        Deque<String> d = new ArrayDeque<>();
        StringBuilder sb = new StringBuilder();
        d.add("x" + (seed & 3));
        try { d.addFirst(null); } catch (NullPointerException e) { sb.append('N'); }
        try { d.offerLast(null); } catch (NullPointerException e) { sb.append('N'); }
        try { d.push(null); } catch (NullPointerException e) { sb.append('N'); }
        sb.append(d.contains(null)).append(d.remove(null)).append(d.removeFirstOccurrence(null));
        sb.append(d.peekFirst()).append(d.size());
        return sb.toString();
    }
}

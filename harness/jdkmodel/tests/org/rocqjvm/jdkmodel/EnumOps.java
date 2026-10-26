package org.rocqjvm.jdkmodel;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

/** Differential tests of EnumMap, EnumSet, Enum.compareTo/getDeclaringClass and
 *  Class.getEnumConstants (enums with and without constant bodies). */
public final class EnumOps {
    private EnumOps() {
    }

    enum Color { RED, GREEN, BLUE, CYAN, MAGENTA }

    enum Op {
        PLUS { int apply(int a, int b) { return a + b; } },
        TIMES { int apply(int a, int b) { return a * b; } },
        NEG { int apply(int a, int b) { return -a; } };
        abstract int apply(int a, int b);
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static Color c() {
        return Color.values()[r(5)];
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String maps(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        EnumMap<Color, String> m = new EnumMap<>(Color.class);
        int ops = 6 + r(12);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(14)) {
                    case 0: case 1: out.append(m.put(c(), r(4) == 0 ? null : "v" + r(5))); break;
                    case 2: out.append(m.remove(c())); break;
                    case 3: out.append(m.get(c())).append(m.containsKey(c())).append(m.containsValue("v1")).append(m.containsValue(null)); break;
                    case 4: { Iterator<Map.Entry<Color, String>> it = m.entrySet().iterator(); while (it.hasNext()) { Map.Entry<Color, String> e = it.next(); out.append(e); if (r(3) == 0) { it.remove(); out.append(e.getKey()); } } break; }
                    case 5: out.append(m.keySet()).append(m.values()).append(m.size()); break;
                    case 6: { EnumMap<Color, String> c2 = m.clone(); c2.put(Color.RED, "r"); out.append(c2).append(c2.equals(m)).append(m.equals(new HashMap<>(m))); break; }
                    case 7: { Map raw = m; raw.put(Op.PLUS, "x"); break; }
                    case 8: { HashMap<Color, String> h = new HashMap<>(); if (r(2) == 0) h.put(c(), "h"); out.append(new EnumMap<>(h)); break; }
                    case 9: { EnumMap<Op, Integer> om = new EnumMap<>(Op.class); om.put(Op.values()[r(3)], 1); om.put(Op.TIMES, 2); out.append(om); break; }
                    case 10: { Iterator<Color> it = m.keySet().iterator(); it.remove(); break; }
                    case 11: m.values().remove("v2"); out.append(m.entrySet().contains(new java.util.AbstractMap.SimpleEntry<>(Color.RED, "v1"))); break;
                    case 12: { Object[] a = m.entrySet().toArray(); out.append(a.length).append(Arrays.toString(a)); break; }
                    default: { EnumMap<Color, String> o = new EnumMap<>(Color.class); o.put(c(), "o"); m.putAll(o); break; }
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(m).append(';');
        }
        return out.toString();
    }

    public static String sets(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        EnumSet<Color> st = r(2) == 0 ? EnumSet.noneOf(Color.class) : EnumSet.of(c(), c());
        for (int k = 0; k < 6 + r(10); k++) {
            try {
                switch (r(12)) {
                    case 0: case 1: out.append(st.add(c())); break;
                    case 2: out.append(st.remove(c())); break;
                    case 3: out.append(EnumSet.complementOf(st)); break;
                    case 4: { Color a = c(), b = c(); out.append(EnumSet.range(a, b)); break; }
                    case 5: out.append(EnumSet.allOf(Color.class)).append(EnumSet.allOf(Op.class)); break;
                    case 6: out.append(st.containsAll(EnumSet.of(c()))).append(st.retainAll(EnumSet.of(c(), c(), c()))); break;
                    case 7: { Iterator<Color> it = st.iterator(); while (it.hasNext()) { Color x = it.next(); if (r(2) == 0) it.remove(); out.append(x); } break; }
                    case 8: out.append(EnumSet.copyOf(new ArrayList<>(Arrays.asList(c(), c())))).append(EnumSet.copyOf(st)); break;
                    case 9: out.append(st.equals(EnumSet.copyOf(st))).append(st.size()).append(st.getClass().getName()); break;
                    case 10: EnumSet.copyOf(new ArrayList<Color>()); break;
                    default: out.append(EnumSet.of(Op.NEG, Op.PLUS)).append(Op.TIMES.getDeclaringClass().getName()); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(st).append(';');
        }
        return out.toString();
    }

    @SuppressWarnings({"unchecked", "rawtypes"})
    public static String enums(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 4; k++) {
            try {
                switch (r(6)) {
                    case 0: out.append(c().compareTo(c())); break;
                    case 1: out.append(Op.values()[r(3)].compareTo(Op.values()[r(3)])).append(Op.PLUS.apply(3, 4)); break;
                    case 2: { Comparable x = Color.RED; out.append(x.compareTo(Op.PLUS)); break; }
                    case 3: out.append(Arrays.toString(Color.class.getEnumConstants())).append(Arrays.toString(Op.class.getEnumConstants()))
                                .append(String.class.getEnumConstants() == null).append(Op.PLUS.getClass().getEnumConstants() == null); break;
                    case 4: out.append(c().compareTo(null)); break;
                    default: out.append(Op.NEG.getDeclaringClass() == Op.class).append(Color.BLUE.getDeclaringClass().getSimpleName()); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    /** Enum.valueOf / the generated valueOf(String) (constants with bodies, nested and local enums),
     *  their exceptions, and the unsigned int/long operations. */
    public static String valueOfs(int seed) {
        s = seed;
        enum Local { ONE, TWO }
        String[] names = {"RED", "BLUE", "red", "", "MAGENTA", null, "PLUS", "TIMES", "ONE", "TWO", "Color"};
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 8; k++) {
            String n = names[r(names.length)];
            try {
                switch (r(6)) {
                    case 0: out.append(Color.valueOf(n)).append(Color.valueOf(n) == Color.valueOf(n)); break;
                    case 1: out.append(Op.valueOf(n)).append(Op.valueOf(n).getClass() == Op.class); break;
                    case 2: out.append(Enum.valueOf(Local.class, n)); break;
                    case 3: { @SuppressWarnings({"unchecked", "rawtypes"}) Class<Color> c = (Class) (r(2) == 0 ? String.class : null);
                              out.append(Enum.valueOf(c, n)); break; }
                    case 4: out.append(Enum.valueOf(Op.class, n).apply(3, 4)); break;
                    default: out.append(Local.valueOf(n).ordinal()); break;
                }
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        int a = r(1 << 30) * (r(2) == 0 ? -1 : 1) * (1 + r(3)), b = r(5) == 0 ? 0 : r(1 << 30) - r(1 << 29) * 3;
        long la = (long) a * 9876543211L, lb = b == 0 ? 0 : (long) b * -77;
        out.append(Integer.compareUnsigned(a, b)).append(',').append(Long.compareUnsigned(la, lb)).append(',')
           .append(Integer.toUnsignedLong(a)).append(',').append(Integer.toUnsignedString(a)).append(',').append(Long.toUnsignedString(la));
        try {
            out.append(',').append(Integer.divideUnsigned(a, b)).append(',').append(Integer.remainderUnsigned(a, b))
               .append(',').append(Long.divideUnsigned(la, lb)).append(',').append(Long.remainderUnsigned(la, lb));
        } catch (ArithmeticException x) {
            out.append("!AE:").append(x.getMessage());
        }
        return out.toString();
    }
}

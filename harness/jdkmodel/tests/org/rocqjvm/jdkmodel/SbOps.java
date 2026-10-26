package org.rocqjvm.jdkmodel;

/** Differential tests of StringBuilder's editing operations (delete, replace, setCharAt, reverse
 *  with surrogates, substring/subSequence, append(char[]), appendCodePoint, codePointAt/Before,
 *  compareTo, isEmpty) and of StringBuffer (every operation, StringBuffer arguments to
 *  StringBuilder and String), with their exception texts. */
public final class SbOps {
    private SbOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static final String POOL = "abcXYZ019 😀𐀀􏿿é";

    static String str() {
        StringBuilder b = new StringBuilder();
        for (int i = r(8); i > 0; i--) b.append(POOL.charAt(r(POOL.length())));
        return b.toString();
    }

    static String show(CharSequence c) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < c.length(); i++) b.append((int) c.charAt(i)).append(' ');
        return b.toString();
    }

    public static String builder(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            StringBuilder b = new StringBuilder(str());
            int a = r(10) - 2, e = r(12) - 2;
            try {
                switch (r(13)) {
                    case 0: b.delete(a, e); break;
                    case 1: b.replace(a, e, r(5) == 0 ? null : str()); break;
                    case 2: b.setCharAt(a, (char) ('A' + r(26))); break;
                    case 3: b.reverse(); break;
                    case 4: out.append(b.substring(a)).append('|').append(b.substring(a, e) == "").append(b.subSequence(a, e)); break;
                    case 5: b.append(r(4) == 0 ? null : str().toCharArray()); break;
                    case 6: b.appendCodePoint(r(3) == 0 ? r(0x120000) - 0x8000 : r(0x400) + 0x1F000); break;
                    case 7: out.append(b.codePointAt(a)).append(',').append(b.codePointBefore(e)); break;
                    case 8: out.append(b.compareTo(r(5) == 0 ? null : new StringBuilder(str()))).append(b.isEmpty()); break;
                    case 9: b.ensureCapacity(r(100)); b.trimToSize(); b.setLength(Math.max(0, a)); break;
                    case 10: b.append(r(4) == 0 ? null : new StringBuffer(str())).append((CharSequence) new StringBuffer("cs")); break;
                    case 11: out.append(new String(r(4) == 0 ? null : new StringBuffer(str()))); break;
                    default: b.reverse().reverse(); out.append(b.toString().equals(new StringBuilder(b).reverse().reverse().toString())); break;
                }
                out.append(show(b));
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String buffer(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        StringBuffer b = new StringBuffer(r(3) == 0 ? "init" : str());
        for (int k = 0; k < 14; k++) {
            int a = r(10) - 2, e = r(12) - 2;
            try {
                switch (r(20)) {
                    case 0: b.append(str()).append(r(100)).append('c').append(1.5).append(2.5f).append(7L).append(true); break;
                    case 1: b.append((Object) (r(3) == 0 ? null : new StringBuilder("o"))).append((String) null).append((StringBuffer) null); break;
                    case 2: b.append(new StringBuffer("sb")).append((CharSequence) new StringBuilder("cs"), 0, 1).append((CharSequence) null); break;
                    case 3: b.insert(a, str()).insert(Math.max(0, Math.min(a, b.length())), 42).insert(0, 'x').insert(0, 3.25); break;
                    case 4: b.delete(a, e); break;
                    case 5: b.deleteCharAt(a); break;
                    case 6: b.replace(a, e, str()); break;
                    case 7: b.reverse(); break;
                    case 8: out.append(b.substring(Math.max(0, a))).append(b.subSequence(0, Math.max(0, Math.min(e, b.length())))); break;
                    case 9: out.append(b.indexOf("a")).append(b.lastIndexOf("b")).append(b.indexOf("X", a)).append(b.lastIndexOf("Z", e)); break;
                    case 10: out.append(b.charAt(a)).append(b.codePointAt(Math.max(0, a))); break;
                    case 11: b.setCharAt(a, 'Q'); break;
                    case 12: b.setLength(a); break;
                    case 13: out.append(b.compareTo(r(4) == 0 ? null : new StringBuffer(str()))); break;
                    case 14: b.appendCodePoint(r(0x30000)); break;
                    case 15: b.append(str().toCharArray(), 0, r(2)).insert(0, "ab".toCharArray()); break;
                    case 16: out.append(b.length()).append(b.isEmpty()).append(new StringBuilder(b).append(b)); break;
                    case 17: out.append(String.valueOf(b)).append(b.toString().equals("" + b)).append(b.equals(b)).append(b.hashCode() == System.identityHashCode(b)); break;
                    case 18: { Appendable ap = b; ap.append('z').append("ap").append("xyz", 1, 2); break; }
                    default: out.append(b.getClass().getName()).append(b instanceof CharSequence); break;
                }
                out.append('[').append(show(b)).append(']');
            } catch (RuntimeException | java.io.IOException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        try {
            new StringBuffer((CharSequence) null);
        } catch (NullPointerException x) {
            out.append(x.getMessage());
        }
        return out.toString();
    }

    static final String CI = "aAbBéÉ\u00b5\u039c\u03bcß\u0130i\u0131I\uD801\uDC00\uD801\uDC28\u01c5\u01c4\u01c6\u00ff\u0178 ";

    static String ci() {
        StringBuilder b = new StringBuilder();
        for (int i = r(7); i > 0; i--) b.append(CI.charAt(r(CI.length())));
        return b.toString();
    }

    /** String.getChars, regionMatches (both), contentEquals, codePointCount, offsetByCodePoints,
     *  chars, codePoints, lines, transform; StringBuilder.getChars/codePointCount/chars. */
    public static String strs(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            String t = r(2) == 0 ? str() : ci();
            int a = r(10) - 2, e = r(10) - 2;
            try {
                switch (r(12)) {
                    case 0: { char[] d = new char[r(8)]; java.util.Arrays.fill(d, '.'); t.getChars(a, e, r(6) == 0 ? null : d, r(5) - 1); out.append(d); break; }
                    case 1: out.append(t.regionMatches(a, r(6) == 0 ? null : ci(), r(4) - 1, r(6) - 1)); break;
                    case 2: { String o = r(2) == 0 ? ci() : t.toUpperCase(); out.append(t.regionMatches(r(3) != 0, a, r(8) == 0 ? null : o, r(4) - 1, r(8) - 1)); break; }
                    case 3: out.append(t.contentEquals(r(5) == 0 ? null : r(2) == 0 ? (CharSequence) new StringBuilder(t) : "x" + t))
                               .append(t.contentEquals(new StringBuffer(t))); break;
                    case 4: out.append(t.codePointCount(a, e)); break;
                    case 5: out.append(t.offsetByCodePoints(Math.max(0, a), r(7) - 3)); break;
                    case 6: out.append(t.chars().sum()).append(',').append(t.chars().filter(c -> c > 'a').count()).append(',').append(t.chars().boxed().toList()); break;
                    case 7: out.append(t.codePoints().boxed().toList()).append(t.codePoints().peek(c -> out.append('p')).count()); break;
                    case 8: { String m = t + "\n" + (r(2) == 0 ? "\r\n" : "\r") + str() + (r(2) == 0 ? "\n" : "");
                              out.append(m.lines().toList()).append(m.lines().peek(x -> out.append('q')).count()); break; }
                    case 9: { java.util.function.Function<String, String> f = r(4) == 0 ? null : String::trim;
                              String u = t.transform(x -> x.length() + "!"); String v = t.transform(f); out.append(u).append(v); break; }
                    case 10: { StringBuilder b = new StringBuilder(t); char[] d = new char[r(8)]; b.getChars(a, e, r(6) == 0 ? null : d, r(5) - 1);
                               out.append(d).append(b.codePointCount(Math.max(0, a), Math.max(0, Math.min(b.length(), e)))).append(b.chars().count()).append(b.offsetByCodePoints(0, b.codePointCount(0, b.length()))); break; }
                    default: out.append(t.regionMatches(true, 0, t.toLowerCase(), 0, t.length())).append(t.equalsIgnoreCase(t.toUpperCase())); break;
                }
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }
}

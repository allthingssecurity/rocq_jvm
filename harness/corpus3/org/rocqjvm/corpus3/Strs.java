package org.rocqjvm.corpus3;

import java.util.Arrays;
import java.util.Objects;

/** Phase 4 corpus: the modelled String / StringBuilder / Character / Integer / Long / Math / Objects /
 *  System.arraycopy / Arrays / Enum methods, javac's indy string concatenation, String switch. */
public class Strs {
    enum Color { RED, GREEN, BLUE }

    static int len(String s) { return s.length(); }
    static int charAt(String s, int i) { return s.charAt(i); }
    static int hash(String s) { return s.hashCode(); }
    static boolean eq(String a, String b) { return a.equals(b); }
    static boolean eqIC(String a, String b) { return a.equalsIgnoreCase(b); }
    static int cmp(String a, String b) { return a.compareTo(b); }
    static int idxC(String s, int c) { return s.indexOf(c); }
    static int idxCF(String s, int c, int f) { return s.indexOf(c, f); }
    static int lidxC(String s, int c) { return s.lastIndexOf(c); }
    static int lidxCF(String s, int c, int f) { return s.lastIndexOf(c, f); }
    static int idxS(String s, String t) { return s.indexOf(t); }
    static int idxSF(String s, String t, int f) { return s.indexOf(t, f); }
    static int lidxS(String s, String t) { return s.lastIndexOf(t); }
    static int lidxSF(String s, String t, int f) { return s.lastIndexOf(t, f); }
    static boolean contains(String s, String t) { return s.contains(t); }
    static boolean starts(String s, String t) { return s.startsWith(t); }
    static boolean startsAt(String s, String t, int o) { return s.startsWith(t, o); }
    static boolean ends(String s, String t) { return s.endsWith(t); }
    static String sub1(String s, int b) { return s.substring(b); }
    static String sub2(String s, int b, int e) { return s.substring(b, e); }
    static boolean subSame(String s) { return s.substring(0) == s && s.substring(0, s.length()) == s; }
    static String trim(String s) { return s.trim(); }
    static boolean trimSame(String s) { return s.trim() == s; }
    static String concat(String a, String b) { return a.concat(b); }
    static String replace(String s, int o, int n) { return s.replace((char) o, (char) n); }
    static boolean empty(String s) { return s.isEmpty(); }
    static int chars(String s) { char[] c = s.toCharArray(); int h = 0; for (char x : c) h = h * 7 + x; return h; }
    static String plus(String a, int i, long l, String b) { return a + "-" + i + ":" + l + '|' + b + true + (char) (i & 0x7f); }
    static String plusNull(String a) { String n = null; return "x" + a + n + 'c'; }
    static String valueOfs(int i, long l, int c) { return String.valueOf(i) + String.valueOf(l) + String.valueOf((char) c) + String.valueOf(i > 0) + String.valueOf((Object) null); }
    static boolean literals(int a) { String x = "lit" + ""; String y = "lit"; return x == y && String.valueOf(a > 0) == (a > 0 ? "true" : "false"); }
    static String sb(String a, int i, long l) {
        StringBuilder sb = new StringBuilder(a); sb.append(i).append(',').append(l).append(true).append((String) null).append((Object) "o");
        if (sb.length() > 3) sb.setLength(3 + (i & 3)); sb.insert(1, "<>"); if (sb.length() > 2) sb.deleteCharAt(2);
        return sb.toString() + sb.length() + sb.charAt(0);
    }
    static int sbBad(int i) { StringBuilder sb = new StringBuilder(i); sb.append("ab"); return sb.charAt(i); }
    static int upper(int c) { return Character.toUpperCase((char) c); }
    static int lower(int c) { return Character.toLowerCase((char) c); }
    static int upperCp(int c) { return Character.toUpperCase(c & 0x1fffff); }
    static int lowerCp(int c) { return Character.toLowerCase(c & 0x1fffff); }
    static int classes(int c) { char ch = (char) c; return (Character.isDigit(ch) ? 1 : 0) | (Character.isLetter(ch) ? 2 : 0) | (Character.isLetterOrDigit(ch) ? 4 : 0) | (Character.isWhitespace(ch) ? 8 : 0) | (Character.isUpperCase(ch) ? 16 : 0) | (Character.isLowerCase(ch) ? 32 : 0) | (Character.isHighSurrogate(ch) ? 64 : 0); }
    static int digit(int c) { return Character.digit((char) c, 10); }
    static int parse(String s) { return Integer.parseInt(s); }
    static long parseL(String s) { return Long.parseLong(s); }
    static String itos(int i, long l) { return Integer.toString(i) + "/" + Long.toString(l); }
    static int maths(int a, int b, long c) { return Math.max(a, b) - Math.min(a, b) + Math.abs(a) + (int) Math.abs(c) + Integer.compare(a, b) + Long.compare(c, a) + (int) Math.max(c, 7L); }
    static boolean objEq(String a, String b) { return Objects.equals(a, b) && Objects.hashCode(a) == Objects.hashCode(b); }
    static int reqNN(String a) { return Objects.requireNonNull(a).length(); }
    static int copy(int n, int sp, int dp, int len) {
        int[] a = new int[n & 15]; for (int i = 0; i < a.length; i++) a[i] = i * 3 + 1;
        System.arraycopy(a, sp, a, dp, len); int h = 0; for (int x : a) h = h * 31 + x; return h;
    }
    static int copyTypes(int k) {
        Object[] src = { "a", null, "b" }; String[] dst = new String[3]; Object[] o = { "x", 1 == k ? new int[1] : (Object) "y" };
        if (k == 2) { long[] l = new long[3]; System.arraycopy(new int[3], 0, l, 0, 3); }
        System.arraycopy(src, 0, dst, 0, 3); System.arraycopy(o, 0, dst, 0, 2); return dst.length;
    }
    static int fills(int v, int f, int t) { int[] a = new int[8]; Arrays.fill(a, v); Arrays.fill(a, f, t, v + 1); int h = 0; for (int x : a) h = h * 31 + x; return h; }
    static int copyOfs(int n) { int[] a = { 1, 2, 3 }; int[] b = Arrays.copyOf(a, n); String[] s = Arrays.copyOf(new String[] { "q" }, n & 7); return b.length + b[b.length > 0 ? b.length - 1 : 0] * 10 + s.length; }
    static int clones(int n) { int[] a = new int[n & 7]; int[] b = a.clone(); b[0] = 5; return a[0] + b[0] + b.length; }
    static String sw(String s) {
        switch (s) { case "Aa": return "1"; case "BB": return "2"; case "content-type": return "ct"; case "": return "empty"; default: return s.length() > 2 ? s.substring(1) : "d"; }
    }
    static int enums(int i) { Color c = Color.values()[i & 3 % 3]; return c.ordinal() * 10 + c.name().length() + (c == Color.GREEN ? 100 : 0); }
    static String enumName(int i) { return Color.values()[Math.abs(i % 3)].toString(); }
}

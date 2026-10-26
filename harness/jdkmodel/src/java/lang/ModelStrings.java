/*
 * rocq-jvm helper (not a JDK class; clean-room, Apache-2.0): String and StringBuilder methods that
 * theories/Jdk/Jdk.v forwards to bytecode, written from the Javadoc on top of the modelled String
 * natives, with JDK 21's checks and exception texts (getChars, regionMatches, contentEquals,
 * codePointCount, offsetByCodePoints, chars, codePoints, lines, transform). chars() is a SIZED stream
 * as in the JDK; codePoints() is SIZED only for a string whose characters are all below U+0100 (the
 * JDK's Latin-1 strings), else of unknown size; lines() is of unknown size. HotSpot never loads this
 * class.
 */
package java.lang;

import java.util.ArrayList;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.ModelIterStreams;
import java.util.stream.Stream;

public final class ModelStrings {
    private ModelStrings() {
    }

    private static String range(int b, int e) {
        return "Range [" + b + ", " + e + ") out of bounds for length ";
    }

    /** String.getChars: checkBoundsBeginEnd(srcBegin, srcEnd, length()), then
     *  checkBoundsOffCount(dstBegin, srcEnd - srcBegin, dst.length). */
    public static void getChars$(String s, int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        int n = s.length();
        if (srcBegin < 0 || srcBegin > srcEnd || srcEnd > n)
            throw new StringIndexOutOfBoundsException(range(srcBegin, srcEnd) + n);
        if (dst == null) throw new NullPointerException("Cannot read the array length because \"dst\" is null");
        int c = srcEnd - srcBegin;
        if (dstBegin < 0 || dstBegin > dst.length - c)
            throw new StringIndexOutOfBoundsException("Range [" + dstBegin + ", " + dstBegin + " + " + c + ") out of bounds for length " + dst.length);
        for (int i = 0; i < c; i++) dst[dstBegin + i] = s.charAt(srcBegin + i);
    }

    /** AbstractStringBuilder.getChars: checkFromToIndex(srcBegin, srcEnd, count) (SIOOBE), then
     *  checkFromToIndex(dstBegin, dstBegin + n, dst.length) (IOOBE). */
    public static void sbGetChars$(StringBuilder sb, int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        int n = sb.length();
        if (srcBegin < 0 || srcBegin > srcEnd || srcEnd > n)
            throw new StringIndexOutOfBoundsException(range(srcBegin, srcEnd) + n);
        int c = srcEnd - srcBegin;
        if (dst == null) throw new NullPointerException("Cannot read the array length because \"dst\" is null");
        int e = dstBegin + c;
        if (dstBegin < 0 || dstBegin > e || e > dst.length)
            throw new IndexOutOfBoundsException(range(dstBegin, e) + dst.length);
        for (int i = 0; i < c; i++) dst[dstBegin + i] = sb.charAt(srcBegin + i);
    }

    public static boolean regionMatches$(String s, int toffset, String other, int ooffset, int len) {
        if (ooffset < 0 || toffset < 0 || toffset > (long) s.length() - len) return false;
        if (other == null) throw new NullPointerException("Cannot invoke \"String.length()\" because \"other\" is null");
        if (ooffset > (long) other.length() - len) return false;
        for (int i = 0; i < len; i++) if (s.charAt(toffset + i) != other.charAt(ooffset + i)) return false;
        return true;
    }

    /** The case-insensitive comparison of the two regions is equalsIgnoreCase of the substrings
     *  (the JDK compares the regions with the same per-character rules). */
    public static boolean regionMatchesCI$(String s, boolean ignoreCase, int toffset, String other, int ooffset, int len) {
        if (!ignoreCase) return regionMatches$(s, toffset, other, ooffset, len);
        if (ooffset < 0 || toffset < 0 || toffset > (long) s.length() - len) return false;
        if (other == null) throw new NullPointerException("Cannot invoke \"String.length()\" because \"other\" is null");
        if (ooffset > (long) other.length() - len) return false;
        if (len <= 0) return true;
        return s.substring(toffset, toffset + len).equalsIgnoreCase(other.substring(ooffset, ooffset + len));
    }

    /** contentEquals(CharSequence): a String, StringBuilder or StringBuffer by its contents (the
     *  JDK reads other CharSequences through length()/charAt(), which is STUCK here). */
    public static boolean contentEquals$(String s, CharSequence cs) {
        if (cs == null) throw new NullPointerException("Cannot invoke \"java.lang.CharSequence.length()\" because \"cs\" is null");
        if (cs instanceof String || cs instanceof StringBuilder || cs instanceof StringBuffer) return s.equals(cs.toString());
        throw ModelStuckLang.unsupported("String.contentEquals of a user CharSequence");
    }

    public static boolean contentEqualsSb$(String s, StringBuffer sb) {
        if (sb == null) throw new NullPointerException("Cannot invoke \"java.lang.CharSequence.length()\" because \"cs\" is null");
        return s.equals(sb.toString());
    }

    private static int cpCount(CharSequence s, int b, int e) {
        int n = e - b;
        for (int i = b; i < e - 1; i++) {
            if (Character.isHighSurrogate(s.charAt(i)) && Character.isLowSurrogate(s.charAt(i + 1))) {
                n--;
                i++;
            }
        }
        return n;
    }

    public static int codePointCount$(String s, int b, int e) {
        if (b < 0 || b > e || e > s.length()) throw new IndexOutOfBoundsException(range(b, e) + s.length());
        return cpCount(s, b, e);
    }

    public static int sbCodePointCount$(StringBuilder s, int b, int e) {
        if (b < 0 || b > e || e > s.length()) throw new IndexOutOfBoundsException(range(b, e) + s.length());
        return cpCount(s, b, e);
    }

    /** Character.offsetByCodePoints(seq, index, codePointOffset). */
    public static int offsetByCodePoints$(CharSequence seq, int index, int codePointOffset) {
        int length = seq.length();
        if (index < 0 || index > length) throw new IndexOutOfBoundsException();
        int x = index;
        if (codePointOffset >= 0) {
            int i;
            for (i = 0; x < length && i < codePointOffset; i++) {
                if (Character.isHighSurrogate(seq.charAt(x++)) && x < length && Character.isLowSurrogate(seq.charAt(x))) x++;
            }
            if (i < codePointOffset) throw new IndexOutOfBoundsException();
        } else {
            int i;
            for (i = codePointOffset; x > 0 && i < 0; i++) {
                if (Character.isLowSurrogate(seq.charAt(--x)) && x > 0 && Character.isHighSurrogate(seq.charAt(x - 1))) x--;
            }
            if (i < 0) throw new IndexOutOfBoundsException();
        }
        return x;
    }

    public static IntStream chars$(CharSequence s) {
        int[] a = new int[s.length()];
        for (int i = 0; i < a.length; i++) a[i] = s.charAt(i);
        return IntStream.of(a);
    }

    public static IntStream codePoints$(String s) {
        boolean latin1 = true;
        for (int i = 0; i < s.length(); i++) if (s.charAt(i) > 0xFF) latin1 = false;
        if (latin1) return chars$(s);
        ArrayList<Integer> cps = new ArrayList<>();
        for (int i = 0; i < s.length(); ) {
            int c = s.codePointAt(i);
            cps.add(c);
            i += Character.charCount(c);
        }
        return ModelIterStreams.orderedUnknownSizeInt(cps.iterator());
    }

    /** lines(): split at \n, \r and \r\n; no empty last line. */
    public static Stream<String> lines$(String s) {
        ArrayList<String> ls = new ArrayList<>();
        int n = s.length();
        int start = 0;
        for (int i = 0; i < n; i++) {
            char c = s.charAt(i);
            if (c == '\n' || c == '\r') {
                ls.add(s.substring(start, i));
                if (c == '\r' && i + 1 < n && s.charAt(i + 1) == '\n') i++;
                start = i + 1;
            }
        }
        if (start < n) ls.add(s.substring(start, n));
        return ModelIterStreams.orderedUnknownSize(ls.iterator());
    }

    public static <R> R transform$(String s, Function<? super String, ? extends R> f) {
        if (f == null) throw new NullPointerException("Cannot invoke \"java.util.function.Function.apply(Object)\" because \"f\" is null");
        return f.apply(s);
    }
}

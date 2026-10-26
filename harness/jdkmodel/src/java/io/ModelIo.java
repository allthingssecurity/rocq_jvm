/*
 * rocq-jvm helper (not a JDK class; clean-room, Apache-2.0) for the java.io model classes.
 * - unsupported: a native method without a Rocq model, so calling it makes the machine STUCK
 *   (no claim about the rest of the run), as java.util.ModelStuck does.
 * - the index checks of jdk.internal.util.Preconditions with the JDK 21 messages
 *   (Objects.checkFromIndexSize / checkFromToIndex throw IndexOutOfBoundsException,
 *   String.getChars and subSequence throw StringIndexOutOfBoundsException);
 * - helpers for things the machine has no native model of (String.getChars,
 *   CharSequence.subSequence of a StringBuilder).
 * The line separator is "\n" (Linux; the model Formatter assumes the same).
 * HotSpot never loads this class.
 */
package java.io;

import java.nio.charset.Charset;

final class ModelIo {
    private ModelIo() {
    }

    static native RuntimeException unsupported(String what);

    static final String LINE_SEPARATOR = "\n";

    static String rangeSize(int off, int len, int length) {
        return "Range [" + off + ", " + off + " + " + len + ") out of bounds for length " + length;
    }

    static String rangeFromTo(int from, int to, int length) {
        return "Range [" + from + ", " + to + ") out of bounds for length " + length;
    }

    static boolean outOfSize(int off, int len, int length) {
        return (length | off | len) < 0 || len > length - off;
    }

    static boolean outOfFromTo(int from, int to, int length) {
        return from < 0 || from > to || to > length;
    }

    /** Objects.checkFromIndexSize. */
    static void checkFromIndexSize(int off, int len, int length) {
        if (outOfSize(off, len, length)) throw new IndexOutOfBoundsException(rangeSize(off, len, length));
    }

    /** Objects.checkFromToIndex. */
    static void checkFromToIndex(int from, int to, int length) {
        if (outOfFromTo(from, to, length)) throw new IndexOutOfBoundsException(rangeFromTo(from, to, length));
    }

    static NullPointerException npe(String msg) {
        return new NullPointerException(msg);
    }

    static NullPointerException arrayLengthOfNull(String var) {
        return new NullPointerException("Cannot read the array length because \"" + var + "\" is null");
    }

    static NullPointerException invokeOnNull(String method, String var) {
        return new NullPointerException("Cannot invoke \"" + method + "\" because \"" + var + "\" is null");
    }

    /** String.getChars(begin, end, dst, dstBegin) with the JDK 21 checks and messages. The
     *  caller has checked s != null. */
    static void getChars(String s, int begin, int end, char[] dst, int dstBegin) {
        int n = s.length();
        if (outOfFromTo(begin, end, n)) throw new StringIndexOutOfBoundsException(rangeFromTo(begin, end, n));
        if (dst == null) throw arrayLengthOfNull("dst");
        int cnt = end - begin;
        if (outOfSize(dstBegin, cnt, dst.length))
            throw new StringIndexOutOfBoundsException(rangeSize(dstBegin, cnt, dst.length));
        for (int i = 0; i < cnt; i++) dst[dstBegin + i] = s.charAt(begin + i);
    }

    /** csq.subSequence(start, end) for a non-null csq: String.substring / AbstractStringBuilder
     *  (both checkFromToIndex with StringIndexOutOfBoundsException), else the object's own
     *  method. */
    static CharSequence subSequence(CharSequence csq, int start, int end) {
        if (csq instanceof String || csq instanceof StringBuilder) {
            int n = csq.length();
            if (outOfFromTo(start, end, n)) throw new StringIndexOutOfBoundsException(rangeFromTo(start, end, n));
            if (csq instanceof String) return ((String) csq).substring(start, end);
            StringBuilder b = new StringBuilder(end - start);
            for (int i = start; i < end; i++) b.append(csq.charAt(i));
            return b.toString();
        }
        if (csq instanceof StringBuffer) throw unsupported("subSequence of a StringBuffer");
        return csq.subSequence(start, end);
    }

    /** String.valueOf(csq) for the append methods: toString() of the object. */
    static String valueOf(CharSequence csq) {
        return String.valueOf((Object) csq);
    }

    // ---- the six modelled charsets ----------------------------------------------------------

    static final int UTF8 = 0, LATIN1 = 1, ASCII = 2, UTF16 = 3, UTF16BE = 4, UTF16LE = 5;

    static int kindOf(Charset cs) {
        if (cs == sun.nio.cs.UTF_8.INSTANCE) return UTF8;
        if (cs == sun.nio.cs.ISO_8859_1.INSTANCE) return LATIN1;
        if (cs == sun.nio.cs.US_ASCII.INSTANCE) return ASCII;
        if (cs == sun.nio.cs.UTF_16.INSTANCE) return UTF16;
        if (cs == sun.nio.cs.UTF_16BE.INSTANCE) return UTF16BE;
        if (cs == sun.nio.cs.UTF_16LE.INSTANCE) return UTF16LE;
        throw unsupported("a charset other than the six standard ones");
    }

    /** The historical names of StreamEncoder/StreamDecoder.getEncoding. */
    static String historicalName(int kind) {
        switch (kind) {
            case UTF8: return "UTF8";
            case LATIN1: return "ISO8859_1";
            case ASCII: return "ASCII";
            case UTF16: return "UTF-16";
            case UTF16BE: return "UnicodeBigUnmarked";
            default: return "UnicodeLittleUnmarked";
        }
    }

    /** Charset.forName for a charset name in StreamEncoder/StreamDecoder/PrintStream/PrintWriter:
     *  an illegal name (or one the JDK does not support) is UnsupportedEncodingException(name). */
    static Charset charsetFor(String csn) throws UnsupportedEncodingException {
        try {
            return Charset.forName(csn);
        } catch (java.nio.charset.IllegalCharsetNameException x) {
            throw new UnsupportedEncodingException(csn);
        }
    }
}

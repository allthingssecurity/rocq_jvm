/*
 * rocq-jvm model of java.nio.charset.Charset (clean-room, Apache-2.0), with the six standard
 * charsets (sun.nio.cs.UTF_8, ISO_8859_1, US_ASCII, UTF_16, UTF_16BE, UTF_16LE: their JDK 21
 * names and aliases) and their String codecs: String.getBytes and new String(byte[], ...) run
 * the static helpers getBytes$ / newString$ below (called by theories/Jdk/Jdk.v), which follow
 * JDK 21's String coding: replacement of malformed input by U+FFFD (UTF-8 with the JDK's
 * malformed-length rules), of unmappable characters by '?' (or the UTF-16 replacement bytes).
 * Charset.defaultCharset() is UTF-8 (the JDK 18+ default; TRUST.md).
 * Not modelled (STUCK): other charsets (a legal name that is none of the six may or may not be
 * supported by the JDK), availableCharsets, encoders/decoders and ByteBuffer/CharBuffer.
 */
package java.nio.charset;

import java.util.Set;

public abstract class Charset implements Comparable<Charset> {
    private final String name;
    private final String[] aliases;
    private Set<String> aliasSet;

    protected Charset(String canonicalName, String[] aliases) {
        String[] as = aliases == null ? new String[0] : aliases.clone();
        checkName(canonicalName);
        for (String a : as) checkName(a);
        this.name = canonicalName;
        this.aliases = as;
    }

    private static void checkName(String s) {
        int n = s.length();
        if (n == 0) throw new IllegalCharsetNameException(s);
        for (int i = 0; i < n; i++) {
            char c = s.charAt(i);
            if (c >= 'A' && c <= 'Z') continue;
            if (c >= 'a' && c <= 'z') continue;
            if (c >= '0' && c <= '9') continue;
            if (c == '-' && i != 0) continue;
            if (c == '+' && i != 0) continue;
            if (c == ':' && i != 0) continue;
            if (c == '_' && i != 0) continue;
            if (c == '.' && i != 0) continue;
            throw new IllegalCharsetNameException(s);
        }
    }

    protected static final int K_UTF8 = 0, K_LATIN1 = 1, K_ASCII = 2, K_UTF16 = 3, K_UTF16BE = 4, K_UTF16LE = 5;

    /** Which of the modelled codecs this charset uses. */
    protected abstract int kind$();

    private static Charset[] standard() {
        return new Charset[] {sun.nio.cs.UTF_8.INSTANCE, sun.nio.cs.ISO_8859_1.INSTANCE, sun.nio.cs.US_ASCII.INSTANCE,
            sun.nio.cs.UTF_16.INSTANCE, sun.nio.cs.UTF_16BE.INSTANCE, sun.nio.cs.UTF_16LE.INSTANCE};
    }

    /** The charset of this name, or null for a legal name that is not one of the six (STUCK at the
     *  callers: the JDK may support it); IllegalCharsetNameException for an illegal name. */
    private static Charset lookup(String charsetName) {
        if (charsetName == null) throw new IllegalArgumentException("Null charset name");
        for (Charset cs : standard()) {
            if (cs.name.equalsIgnoreCase(charsetName)) return cs;
            for (String a : cs.aliases) {
                if (a.equalsIgnoreCase(charsetName)) return cs;
            }
        }
        checkName(charsetName);
        return null;
    }

    private static RuntimeException otherCharset(String name) {
        return ModelStuckCs.unsupported("Charset: a charset other than the six standard ones: " + name);
    }

    public static boolean isSupported(String charsetName) {
        Charset cs = lookup(charsetName);
        if (cs == null) throw otherCharset(charsetName);
        return true;
    }

    public static Charset forName(String charsetName) {
        Charset cs = lookup(charsetName);
        if (cs == null) throw otherCharset(charsetName);
        return cs;
    }

    public static Charset forName(String charsetName, Charset fallback) {
        try {
            Charset cs = lookup(charsetName);
            if (cs == null) throw otherCharset(charsetName);
            return cs;
        } catch (IllegalCharsetNameException x) {
            return fallback;
        }
    }

    public static Charset defaultCharset() {
        return sun.nio.cs.UTF_8.INSTANCE;
    }

    public static java.util.SortedMap<String, Charset> availableCharsets() {
        throw ModelStuckCs.unsupported("Charset.availableCharsets");
    }

    public final String name() {
        return name;
    }

    /** JDK 21: Set.of(aliases) (so its iteration order depends on the run's salt). */
    public final Set<String> aliases() {
        Set<String> s = aliasSet;
        if (s == null) {
            s = aliasSet = Set.of(aliases);
        }
        return s;
    }

    public String displayName() {
        return name;
    }

    public final boolean isRegistered() {
        return !name.startsWith("X-") && !name.startsWith("x-");
    }

    public boolean canEncode() {
        return true;
    }

    public abstract boolean contains(Charset cs);

    public CharsetDecoder newDecoder() {
        throw ModelStuckCs.unsupported("Charset.newDecoder");
    }

    public CharsetEncoder newEncoder() {
        throw ModelStuckCs.unsupported("Charset.newEncoder");
    }

    public final int compareTo(Charset that) {
        return name().compareToIgnoreCase(that.name());
    }

    public final int hashCode() {
        return name().hashCode();
    }

    public final boolean equals(Object ob) {
        if (this == ob) return true;
        if (!(ob instanceof Charset)) return false;
        return name.equals(((Charset) ob).name());
    }

    public final String toString() {
        return name();
    }

    // ---------------------------------------------------------------------------------------
    // String coding (rocq-jvm helpers, not JDK API: String's constructors and getBytes in the
    // machine run these as bytecode).

    static final char REPL = '�';

    private static NullPointerException lengthOfNull(String what) {
        return new NullPointerException("Cannot read the array length because \"" + what + "\" is null");
    }

    private static void checkBoundsOffCount(int offset, int count, int length) {
        if ((length | offset | count) < 0 || count > length - offset)
            throw new StringIndexOutOfBoundsException("Range [" + offset + ", " + offset + " + " + count
                + ") out of bounds for length " + length);
    }

    private static Charset lookupCharset(String csn) throws java.io.UnsupportedEncodingException {
        if (csn == null) throw new NullPointerException();
        try {
            Charset cs = lookup(csn);
            if (cs == null) throw otherCharset(csn);
            return cs;
        } catch (IllegalCharsetNameException x) {
            throw new java.io.UnsupportedEncodingException(csn);
        }
    }

    public static String newString$(byte[] bytes) {
        if (bytes == null) throw lengthOfNull("bytes");
        return decode(defaultCharset(), bytes, 0, bytes.length);
    }

    public static String newString$(byte[] bytes, int offset, int length) {
        if (bytes == null) throw lengthOfNull("bytes");
        checkBoundsOffCount(offset, length, bytes.length);
        return decode(defaultCharset(), bytes, offset, length);
    }

    public static String newString$(byte[] bytes, Charset charset) {
        if (charset == null) throw new NullPointerException();
        if (bytes == null) throw lengthOfNull("bytes");
        return decode(charset, bytes, 0, bytes.length);
    }

    public static String newString$(byte[] bytes, int offset, int length, Charset charset) {
        if (charset == null) throw new NullPointerException();
        if (bytes == null) throw lengthOfNull("bytes");
        checkBoundsOffCount(offset, length, bytes.length);
        return decode(charset, bytes, offset, length);
    }

    public static String newString$(byte[] bytes, String charsetName) throws java.io.UnsupportedEncodingException {
        Charset cs = lookupCharset(charsetName);
        if (bytes == null) throw lengthOfNull("bytes");
        return decode(cs, bytes, 0, bytes.length);
    }

    public static String newString$(byte[] bytes, int offset, int length, String charsetName)
            throws java.io.UnsupportedEncodingException {
        Charset cs = lookupCharset(charsetName);
        if (bytes == null) throw lengthOfNull("bytes");
        checkBoundsOffCount(offset, length, bytes.length);
        return decode(cs, bytes, offset, length);
    }

    public static byte[] getBytes$(String s) {
        return encode(defaultCharset(), s);
    }

    public static byte[] getBytes$(String s, Charset charset) {
        if (charset == null) throw new NullPointerException();
        return encode(charset, s);
    }

    public static byte[] getBytes$(String s, String charsetName) throws java.io.UnsupportedEncodingException {
        return encode(lookupCharset(charsetName), s);
    }

    private static String decode(Charset cs, byte[] b, int off, int len) {
        if (len == 0) return "";
        StringBuilder sb = new StringBuilder(len);
        switch (cs.kind$()) {
            case K_UTF8: decodeUtf8(b, off, off + len, sb); break;
            case K_LATIN1: for (int i = off; i < off + len; i++) sb.append((char) (b[i] & 0xff)); break;
            case K_ASCII: for (int i = off; i < off + len; i++) sb.append(b[i] >= 0 ? (char) b[i] : REPL); break;
            case K_UTF16: decodeUtf16(b, off, off + len, 0, sb); break;
            case K_UTF16BE: decodeUtf16(b, off, off + len, 1, sb); break;
            default: decodeUtf16(b, off, off + len, 2, sb); break;
        }
        return sb.toString();
    }

    private static boolean isNotContinuation(int b) {
        return (b & 0xc0) != 0x80;
    }

    private static boolean isMalformed3(int b1, int b2, int b3) {
        return (b1 == (byte) 0xe0 && (b2 & 0xe0) == 0x80) || (b2 & 0xc0) != 0x80 || (b3 & 0xc0) != 0x80;
    }

    private static boolean isMalformed3_2(int b1, int b2) {
        return (b1 == (byte) 0xe0 && (b2 & 0xe0) == 0x80) || (b2 & 0xc0) != 0x80;
    }

    private static boolean isMalformed4(int b2, int b3, int b4) {
        return (b2 & 0xc0) != 0x80 || (b3 & 0xc0) != 0x80 || (b4 & 0xc0) != 0x80;
    }

    private static boolean isMalformed4_2(int b1, int b2) {
        return (b1 == 0xf0 && (b2 < 0x90 || b2 > 0xbf)) || (b1 == 0xf4 && (b2 & 0xf0) != 0x80) || (b2 & 0xc0) != 0x80;
    }

    private static int malformed3(byte[] src, int sp) {
        int b1 = src[sp];
        int b2 = src[sp + 1];
        return ((b1 == (byte) 0xe0 && (b2 & 0xe0) == 0x80) || isNotContinuation(b2)) ? 1 : 2;
    }

    private static int malformed4(byte[] src, int sp) {
        int b1 = src[sp] & 0xff;
        int b2 = src[sp + 1] & 0xff;
        if (b1 > 0xf4 || (b1 == 0xf0 && (b2 < 0x90 || b2 > 0xbf)) || (b1 == 0xf4 && (b2 & 0xf0) != 0x80)
                || isNotContinuation(b2)) return 1;
        if (isNotContinuation(src[sp + 2])) return 2;
        return 3;
    }

    private static boolean isSurrogateChar(int c) {
        return c >= 0xD800 && c <= 0xDFFF;
    }

    /** JDK 21 String.decodeUTF8_UTF16 with replacement. */
    private static void decodeUtf8(byte[] src, int sp, int sl, StringBuilder out) {
        while (sp < sl) {
            int b1 = src[sp++];
            if (b1 >= 0) {
                out.append((char) b1);
            } else if ((b1 >> 5) == -2 && (b1 & 0x1e) != 0) {
                if (sp < sl) {
                    int b2 = src[sp++];
                    if (isNotContinuation(b2)) {
                        out.append(REPL);
                        sp--;
                    } else {
                        out.append((char) (((b1 << 6) ^ b2) ^ (((byte) 0xC0 << 6) ^ ((byte) 0x80))));
                    }
                    continue;
                }
                out.append(REPL);
                break;
            } else if ((b1 >> 4) == -2) {
                if (sp + 1 < sl) {
                    int b2 = src[sp++];
                    int b3 = src[sp++];
                    if (isMalformed3(b1, b2, b3)) {
                        out.append(REPL);
                        sp -= 3;
                        sp += malformed3(src, sp);
                    } else {
                        char c = (char) ((b1 << 12) ^ (b2 << 6) ^ (b3 ^ (((byte) 0xE0 << 12) ^ ((byte) 0x80 << 6) ^ ((byte) 0x80))));
                        out.append(isSurrogateChar(c) ? REPL : c);
                    }
                    continue;
                }
                if (sp < sl && isMalformed3_2(b1, src[sp])) {
                    out.append(REPL);
                    continue;
                }
                out.append(REPL);
                break;
            } else if ((b1 >> 3) == -2) {
                if (sp + 2 < sl) {
                    int b2 = src[sp++];
                    int b3 = src[sp++];
                    int b4 = src[sp++];
                    int uc = ((b1 << 18) ^ (b2 << 12) ^ (b3 << 6)
                        ^ (b4 ^ (((byte) 0xF0 << 18) ^ ((byte) 0x80 << 12) ^ ((byte) 0x80 << 6) ^ ((byte) 0x80))));
                    if (isMalformed4(b2, b3, b4) || !(uc >= 0x10000 && uc < 0x110000)) {
                        out.append(REPL);
                        sp -= 4;
                        sp += malformed4(src, sp);
                    } else {
                        out.append((char) ((uc >>> 10) + (0xD800 - (0x10000 >>> 10))));
                        out.append((char) ((uc & 0x3ff) + 0xDC00));
                    }
                    continue;
                }
                b1 &= 0xff;
                if (b1 > 0xf4 || sp < sl && isMalformed4_2(b1, src[sp] & 0xff)) {
                    out.append(REPL);
                    continue;
                }
                sp++;
                out.append(REPL);
                if (sp < sl && isNotContinuation(src[sp])) {
                    continue;
                }
                break;
            } else {
                out.append(REPL);
            }
        }
    }

    /** sun.nio.cs.UnicodeDecoder (JDK 21) with replacement: order 0 = UTF-16 (a leading byte-order
     *  mark is consumed and decides the order; default big-endian), 1 = big-, 2 = little-endian.
     *  An unpaired low surrogate is malformed (2 bytes), a high surrogate not followed by a low one
     *  is malformed with the next unit (4 bytes); bytes left at the end (an odd byte, a final high
     *  surrogate) are one malformed input. Each malformed input becomes one U+FFFD. */
    private static void decodeUtf16(byte[] b, int sp, int sl, int order, StringBuilder out) {
        boolean known = order != 0;
        boolean big = order != 2;
        while (sl - sp > 1) {
            int b1 = b[sp] & 0xff, b2 = b[sp + 1] & 0xff;
            sp += 2;
            if (!known) {
                known = true;
                int m = (b1 << 8) | b2;
                if (m == 0xFEFF) {
                    big = true;
                    continue;
                } else if (m == 0xFFFE) {
                    big = false;
                    continue;
                }
                big = true;
            }
            char c = (char) (big ? (b1 << 8) | b2 : (b2 << 8) | b1);
            if (isSurrogateChar(c)) {
                if (c < 0xDC00) {
                    if (sl - sp < 2) {
                        sp -= 2;
                        break;
                    }
                    char d = decodeUnit(b, sp, big);
                    sp += 2;
                    if (d >= 0xDC00 && d <= 0xDFFF) {
                        out.append(c).append(d);
                    } else {
                        out.append(REPL);
                    }
                    continue;
                }
                out.append(REPL);
                continue;
            }
            out.append(c);
        }
        if (sp < sl) out.append(REPL);
    }

    private static char decodeUnit(byte[] b, int i, boolean big) {
        int b1 = b[i] & 0xff, b2 = b[i + 1] & 0xff;
        return (char) (big ? (b1 << 8) | b2 : (b2 << 8) | b1);
    }

    private static byte[] encode(Charset cs, String s) {
        int n = s.length();
        int k = cs.kind$();
        if (n == 0 && k >= K_UTF16) return new byte[0];
        Bytes out = new Bytes(n * 2 + 2);
        switch (k) {
            case K_UTF8:
                for (int i = 0; i < n; i++) {
                    char c = s.charAt(i);
                    if (c < 0x80) {
                        out.write(c);
                    } else if (c < 0x800) {
                        out.write(0xc0 | (c >> 6));
                        out.write(0x80 | (c & 0x3f));
                    } else if (isSurrogateChar(c)) {
                        char c2;
                        if (c < 0xDC00 && i + 1 < n && (c2 = s.charAt(i + 1)) >= 0xDC00 && c2 <= 0xDFFF) {
                            int uc = ((c - 0xD800) << 10) + (c2 - 0xDC00) + 0x10000;
                            out.write(0xf0 | (uc >> 18));
                            out.write(0x80 | ((uc >> 12) & 0x3f));
                            out.write(0x80 | ((uc >> 6) & 0x3f));
                            out.write(0x80 | (uc & 0x3f));
                            i++;
                        } else {
                            out.write('?');
                        }
                    } else {
                        out.write(0xe0 | (c >> 12));
                        out.write(0x80 | ((c >> 6) & 0x3f));
                        out.write(0x80 | (c & 0x3f));
                    }
                }
                break;
            case K_LATIN1:
            case K_ASCII: {
                int max = (k == K_LATIN1) ? 0xff : 0x7f;
                for (int i = 0; i < n; i++) {
                    char c = s.charAt(i);
                    if (c <= max) {
                        out.write(c);
                    } else {
                        if (c >= 0xD800 && c < 0xDC00 && i + 1 < n) {
                            char c2 = s.charAt(i + 1);
                            if (c2 >= 0xDC00 && c2 <= 0xDFFF) i++;
                        }
                        out.write('?');
                    }
                }
                break;
            }
            default: {
                boolean big = k != K_UTF16LE;
                if (k == K_UTF16) {
                    out.write(0xfe);
                    out.write(0xff);
                }
                for (int i = 0; i < n; i++) {
                    char c = s.charAt(i);
                    if (isSurrogateChar(c)) {
                        char c2;
                        if (c < 0xDC00 && i + 1 < n && (c2 = s.charAt(i + 1)) >= 0xDC00 && c2 <= 0xDFFF) {
                            unit(out, c, big);
                            unit(out, c2, big);
                            i++;
                        } else {
                            unit(out, (char) 0xFFFD, big);
                        }
                    } else {
                        unit(out, c, big);
                    }
                }
                break;
            }
        }
        return out.toBytes();
    }

    private static void unit(Bytes out, char c, boolean big) {
        if (big) {
            out.write(c >> 8);
            out.write(c & 0xff);
        } else {
            out.write(c & 0xff);
            out.write(c >> 8);
        }
    }

    /** A growable byte buffer. */
    private static final class Bytes {
        byte[] a;
        int n;

        Bytes(int cap) {
            a = new byte[Math.max(cap, 4)];
        }

        void write(int b) {
            if (n == a.length) {
                byte[] r = new byte[a.length * 2];
                System.arraycopy(a, 0, r, 0, n);
                a = r;
            }
            a[n++] = (byte) b;
        }

        byte[] toBytes() {
            byte[] r = new byte[n];
            System.arraycopy(a, 0, r, 0, n);
            return r;
        }
    }
}

final class ModelStuckCs {
    private ModelStuckCs() {
    }

    static native RuntimeException unsupported(String what);
}

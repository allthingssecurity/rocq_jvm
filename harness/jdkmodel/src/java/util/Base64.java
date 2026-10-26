/*
 * rocq-jvm model of java.util.Base64 (clean-room, Apache-2.0), JDK 21 behaviour: the basic, URL
 * and MIME encoders (MIME: lines of 76 chars separated by CRLF, or a custom line length rounded
 * down to a multiple of 4 and a separator without base64 characters) with and without padding;
 * the decoders with the JDK's IllegalArgumentException messages (the output size is computed
 * from the input first, so some malformed inputs fail with the JDK's array index error; MIME
 * ignores non-base64 characters); encode(byte[], byte[]) / decode(byte[], byte[]) size checks;
 * decode(String) through the ISO-8859-1 encoding of the string; wrap(OutputStream) and
 * wrap(InputStream) with the JDK's buffering and IOException messages.
 * Not modelled (STUCK): the ByteBuffer methods.
 */
package java.util;

import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

public class Base64 {
    private Base64() {
    }

    public static Encoder getEncoder() {
        return Encoder.RFC4648;
    }

    public static Encoder getUrlEncoder() {
        return Encoder.RFC4648_URLSAFE;
    }

    public static Encoder getMimeEncoder() {
        return Encoder.RFC2045;
    }

    /** Arrays.copyOf(a, n) for n <= a.length. */
    static byte[] prefix(byte[] a, int n) {
        byte[] r = new byte[n];
        System.arraycopy(a, 0, r, 0, n);
        return r;
    }

    static NullPointerException lengthOfNull(String var) {
        return new NullPointerException("Cannot read the array length because \"" + var + "\" is null");
    }

    /** Integer.toString(v, 16) (signed). */
    static String hex(int v) {
        if (v == 0) return "0";
        boolean neg = v < 0;
        long u = neg ? -(long) v : v;
        StringBuilder b = new StringBuilder();
        while (u > 0) {
            b.insert(0, "0123456789abcdef".charAt((int) (u & 15)));
            u >>>= 4;
        }
        if (neg) b.insert(0, '-');
        return b.toString();
    }

    public static Encoder getMimeEncoder(int lineLength, byte[] lineSeparator) {
        Objects.requireNonNull(lineSeparator);
        int[] table = Decoder.FROM_BASE64;
        for (byte b : lineSeparator) {
            if (table[b & 0xff] != -1)
                throw new IllegalArgumentException("Illegal base64 line separator character 0x" + hex(b));
        }
        lineLength &= ~0b11;
        if (lineLength <= 0) return Encoder.RFC4648;
        return new Encoder(false, lineSeparator, lineLength, true);
    }

    public static Decoder getDecoder() {
        return Decoder.RFC4648;
    }

    public static Decoder getUrlDecoder() {
        return Decoder.RFC4648_URLSAFE;
    }

    public static Decoder getMimeDecoder() {
        return Decoder.RFC2045;
    }

    static final String ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";

    static char[] alphabet(boolean url) {
        char[] a = new char[64];
        for (int i = 0; i < 62; i++) a[i] = ALPHABET.charAt(i);
        a[62] = url ? '-' : '+';
        a[63] = url ? '_' : '/';
        return a;
    }

    public static class Encoder {
        private final byte[] newline;
        private final int linemax;
        private final boolean isURL;
        private final boolean doPadding;

        private Encoder(boolean isURL, byte[] newline, int linemax, boolean doPadding) {
            this.isURL = isURL;
            this.newline = newline;
            this.linemax = linemax;
            this.doPadding = doPadding;
        }

        static final char[] TO_BASE64 = alphabet(false);
        static final char[] TO_BASE64_URL = alphabet(true);
        private static final byte[] CRLF = new byte[] {'\r', '\n'};

        static final Encoder RFC4648 = new Encoder(false, null, -1, true);
        static final Encoder RFC4648_URLSAFE = new Encoder(true, null, -1, true);
        static final Encoder RFC2045 = new Encoder(false, CRLF, 76, true);

        /** The encoded length, -1 on int overflow (throwOOME: STUCK, the JDK throws OutOfMemoryError). */
        private int outLength(int srclen, boolean throwOOME) {
            long len;
            if (doPadding) {
                len = 4L * ((srclen + 2L) / 3);
            } else {
                int n = srclen % 3;
                len = 4L * (srclen / 3) + (n == 0 ? 0 : n + 1);
            }
            if (len <= Integer.MAX_VALUE && linemax > 0) len += (len - 1) / linemax * newline.length;
            if (len > Integer.MAX_VALUE) {
                if (throwOOME) throw ModelStuck.unsupported("Base64: encoded size beyond int");
                return -1;
            }
            return (int) len;
        }

        public byte[] encode(byte[] src) {
            if (src == null) throw lengthOfNull("src");
            int len = outLength(src.length, true);
            byte[] dst = new byte[len];
            int ret = encode0(src, 0, src.length, dst);
            if (ret != dst.length) return prefix(dst, ret);
            return dst;
        }

        public int encode(byte[] src, byte[] dst) {
            if (src == null) throw lengthOfNull("src");
            int len = outLength(src.length, false);
            if (dst == null) throw lengthOfNull("dst");
            if (dst.length < len || len == -1)
                throw new IllegalArgumentException("Output byte array is too small for encoding all input bytes");
            return encode0(src, 0, src.length, dst);
        }

        public String encodeToString(byte[] src) {
            byte[] e = encode(src);
            char[] cs = new char[e.length];
            for (int i = 0; i < e.length; i++) cs[i] = (char) (e[i] & 0xff);
            return new String(cs);
        }

        public java.nio.ByteBuffer encode(java.nio.ByteBuffer buffer) {
            throw ModelStuck.unsupported("Base64.Encoder.encode(ByteBuffer)");
        }

        public OutputStream wrap(OutputStream os) {
            Objects.requireNonNull(os);
            return new EncOutputStream(os, isURL ? TO_BASE64_URL : TO_BASE64, newline, linemax, doPadding);
        }

        public Encoder withoutPadding() {
            if (!doPadding) return this;
            return new Encoder(isURL, newline, linemax, false);
        }

        private int encode0(byte[] src, int off, int end, byte[] dst) {
            char[] t = isURL ? TO_BASE64_URL : TO_BASE64;
            int sp = off;
            int whole = (end - off) / 3 * 3;
            int sl = off + whole;
            int step = whole;
            if (linemax > 0 && step > linemax / 4 * 3) step = linemax / 4 * 3;
            int dp = 0;
            while (sp < sl) {
                int sl0 = Math.min(sp + step, sl);
                for (int s = sp; s < sl0; s += 3) {
                    int bits = (src[s] & 0xff) << 16 | (src[s + 1] & 0xff) << 8 | (src[s + 2] & 0xff);
                    dst[dp++] = (byte) t[(bits >>> 18) & 0x3f];
                    dst[dp++] = (byte) t[(bits >>> 12) & 0x3f];
                    dst[dp++] = (byte) t[(bits >>> 6) & 0x3f];
                    dst[dp++] = (byte) t[bits & 0x3f];
                }
                int dlen = (sl0 - sp) / 3 * 4;
                sp = sl0;
                if (dlen == linemax && sp < end) {
                    for (byte b : newline) dst[dp++] = b;
                }
            }
            if (sp < end) {
                int b0 = src[sp++] & 0xff;
                dst[dp++] = (byte) t[b0 >> 2];
                if (sp == end) {
                    dst[dp++] = (byte) t[(b0 << 4) & 0x3f];
                    if (doPadding) {
                        dst[dp++] = '=';
                        dst[dp++] = '=';
                    }
                } else {
                    int b1 = src[sp++] & 0xff;
                    dst[dp++] = (byte) t[(b0 << 4) & 0x3f | (b1 >> 4)];
                    dst[dp++] = (byte) t[(b1 << 2) & 0x3f];
                    if (doPadding) dst[dp++] = '=';
                }
            }
            return dp;
        }
    }

    public static class Decoder {
        private final boolean isURL;
        private final boolean isMIME;

        private Decoder(boolean isURL, boolean isMIME) {
            this.isURL = isURL;
            this.isMIME = isMIME;
        }

        private static int[] table(char[] alphabet) {
            int[] t = new int[256];
            for (int i = 0; i < 256; i++) t[i] = -1;
            for (int i = 0; i < alphabet.length; i++) t[alphabet[i]] = i;
            t['='] = -2;
            return t;
        }

        static final int[] FROM_BASE64 = table(Encoder.TO_BASE64);
        static final int[] FROM_BASE64_URL = table(Encoder.TO_BASE64_URL);

        static final Decoder RFC4648 = new Decoder(false, false);
        static final Decoder RFC4648_URLSAFE = new Decoder(true, false);
        static final Decoder RFC2045 = new Decoder(false, true);

        public byte[] decode(byte[] src) {
            if (src == null) throw lengthOfNull("src");
            byte[] dst = new byte[outLength(src, 0, src.length)];
            int ret = decode0(src, 0, src.length, dst);
            if (ret != dst.length) dst = prefix(dst, ret);
            return dst;
        }

        public byte[] decode(String src) {
            if (src == null)
                throw new NullPointerException("Cannot invoke \"String.getBytes(java.nio.charset.Charset)\" because \"src\" is null");
            return decode(src.getBytes(java.nio.charset.StandardCharsets.ISO_8859_1));
        }

        public int decode(byte[] src, byte[] dst) {
            if (src == null) throw lengthOfNull("src");
            int len = outLength(src, 0, src.length);
            if (dst == null) throw lengthOfNull("dst");
            if (dst.length < len || len == -1)
                throw new IllegalArgumentException("Output byte array is too small for decoding all input bytes");
            return decode0(src, 0, src.length, dst);
        }

        public java.nio.ByteBuffer decode(java.nio.ByteBuffer buffer) {
            throw ModelStuck.unsupported("Base64.Decoder.decode(ByteBuffer)");
        }

        public InputStream wrap(InputStream is) {
            Objects.requireNonNull(is);
            return new DecInputStream(is, isURL ? FROM_BASE64_URL : FROM_BASE64, isMIME);
        }

        /** The JDK's estimate of the decoded size (exact for well-formed input). */
        private int outLength(byte[] src, int sp, int sl) {
            int[] t = isURL ? FROM_BASE64_URL : FROM_BASE64;
            int paddings = 0;
            int len = sl - sp;
            if (len == 0) return 0;
            if (len < 2) {
                if (isMIME && t[0] == -1) return 0;
                throw new IllegalArgumentException("Input byte[] should at least have 2 bytes for base64 bytes");
            }
            if (isMIME) {
                int n = 0;
                while (sp < sl) {
                    int b = src[sp++] & 0xff;
                    if (b == '=') {
                        len -= (sl - sp + 1);
                        break;
                    }
                    if (t[b] == -1) n++;
                }
                len -= n;
            } else {
                if (src[sl - 1] == '=') {
                    paddings++;
                    if (src[sl - 2] == '=') paddings++;
                }
            }
            if (paddings == 0 && (len & 0x3) != 0) paddings = 4 - (len & 0x3);
            return 3 * (int) ((len + 3L) / 4) - paddings;
        }

        private int decode0(byte[] src, int sp, int sl, byte[] dst) {
            int[] t = isURL ? FROM_BASE64_URL : FROM_BASE64;
            int dp = 0;
            int bits = 0;
            int shiftto = 18;
            while (sp < sl) {
                int b = src[sp++] & 0xff;
                if ((b = t[b]) < 0) {
                    if (b == -2) {
                        if (shiftto == 6 && (sp == sl || src[sp++] != '=') || shiftto == 18)
                            throw new IllegalArgumentException("Input byte array has wrong 4-byte ending unit");
                        break;
                    }
                    if (isMIME) continue;
                    throw new IllegalArgumentException("Illegal base64 character " + hex(src[sp - 1]));
                }
                bits |= (b << shiftto);
                shiftto -= 6;
                if (shiftto < 0) {
                    dst[dp++] = (byte) (bits >> 16);
                    dst[dp++] = (byte) (bits >> 8);
                    dst[dp++] = (byte) bits;
                    shiftto = 18;
                    bits = 0;
                }
            }
            if (shiftto == 6) {
                dst[dp++] = (byte) (bits >> 16);
            } else if (shiftto == 0) {
                dst[dp++] = (byte) (bits >> 16);
                dst[dp++] = (byte) (bits >> 8);
            } else if (shiftto == 12) {
                throw new IllegalArgumentException("Last unit does not have enough valid bits");
            }
            while (sp < sl) {
                if (isMIME && t[src[sp++] & 0xff] < 0) continue;
                throw new IllegalArgumentException("Input byte array has incorrect ending byte at " + sp);
            }
            return dp;
        }
    }

    private static class EncOutputStream extends FilterOutputStream {
        private int leftover = 0;
        private int b0, b1, b2;
        private boolean closed = false;
        private final char[] base64;
        private final byte[] newline;
        private final int linemax;
        private final boolean doPadding;
        private int linepos = 0;
        private final byte[] buf;

        EncOutputStream(OutputStream os, char[] base64, byte[] newline, int linemax, boolean doPadding) {
            super(os);
            this.base64 = base64;
            this.newline = newline;
            this.linemax = linemax;
            this.doPadding = doPadding;
            this.buf = new byte[linemax <= 0 ? 8124 : linemax];
        }

        public void write(int b) throws IOException {
            byte[] one = new byte[] {(byte) (b & 0xff)};
            write(one, 0, 1);
        }

        private void checkNewline() throws IOException {
            if (linepos == linemax) {
                out.write(newline);
                linepos = 0;
            }
        }

        private void writeb4(char c1, char c2, char c3, char c4) throws IOException {
            buf[0] = (byte) c1;
            buf[1] = (byte) c2;
            buf[2] = (byte) c3;
            buf[3] = (byte) c4;
            out.write(buf, 0, 4);
        }

        public void write(byte[] b, int off, int len) throws IOException {
            if (closed) throw new IOException("Stream is closed");
            if (b == null) throw new NullPointerException("Cannot read the array length because \"b\" is null");
            if ((b.length | off | len) < 0 || len > b.length - off)
                throw new ArrayIndexOutOfBoundsException("Range [" + off + ", " + off + " + " + len
                    + ") out of bounds for length " + b.length);
            if (len == 0) return;
            if (leftover != 0) {
                if (leftover == 1) {
                    b1 = b[off++] & 0xff;
                    len--;
                    if (len == 0) {
                        leftover++;
                        return;
                    }
                }
                b2 = b[off++] & 0xff;
                len--;
                checkNewline();
                writeb4(base64[b0 >> 2], base64[(b0 << 4) & 0x3f | (b1 >> 4)], base64[(b1 << 2) & 0x3f | (b2 >> 6)],
                    base64[b2 & 0x3f]);
                linepos += 4;
            }
            int nBits24 = len / 3;
            leftover = len - (nBits24 * 3);
            while (nBits24 > 0) {
                checkNewline();
                int dl = linemax <= 0 ? buf.length : buf.length - linepos;
                int sl = off + Math.min(nBits24, dl / 4) * 3;
                int dp = 0;
                for (int sp = off; sp < sl; sp += 3) {
                    int bits = (b[sp] & 0xff) << 16 | (b[sp + 1] & 0xff) << 8 | (b[sp + 2] & 0xff);
                    buf[dp++] = (byte) base64[(bits >>> 18) & 0x3f];
                    buf[dp++] = (byte) base64[(bits >>> 12) & 0x3f];
                    buf[dp++] = (byte) base64[(bits >>> 6) & 0x3f];
                    buf[dp++] = (byte) base64[bits & 0x3f];
                }
                out.write(buf, 0, dp);
                off = sl;
                linepos += dp;
                nBits24 -= dp / 4;
            }
            if (leftover == 1) {
                b0 = b[off++] & 0xff;
            } else if (leftover == 2) {
                b0 = b[off++] & 0xff;
                b1 = b[off++] & 0xff;
            }
        }

        public void close() throws IOException {
            if (!closed) {
                closed = true;
                if (leftover == 1) {
                    checkNewline();
                    out.write(base64[b0 >> 2]);
                    out.write(base64[(b0 << 4) & 0x3f]);
                    if (doPadding) {
                        out.write('=');
                        out.write('=');
                    }
                } else if (leftover == 2) {
                    checkNewline();
                    out.write(base64[b0 >> 2]);
                    out.write(base64[(b0 << 4) & 0x3f | (b1 >> 4)]);
                    out.write(base64[(b1 << 2) & 0x3f]);
                    if (doPadding) out.write('=');
                }
                leftover = 0;
                out.close();
            }
        }
    }

    private static class DecInputStream extends InputStream {
        private final InputStream is;
        private final boolean isMIME;
        private final int[] base64;
        private int bits = 0;
        private int wpos = 0;
        private int rpos = 0;
        private boolean eof = false;
        private boolean closed = false;
        private final byte[] one = new byte[1];

        DecInputStream(InputStream is, int[] base64, boolean isMIME) {
            this.is = is;
            this.base64 = base64;
            this.isMIME = isMIME;
        }

        public int read() throws IOException {
            return read(one, 0, 1) == -1 ? -1 : one[0] & 0xff;
        }

        private int leftovers(byte[] b, int off, int pos, int limit) {
            eof = true;
            while (rpos - 8 >= wpos && pos != limit) {
                rpos -= 8;
                b[pos++] = (byte) (bits >> rpos);
            }
            return pos - off != 0 || rpos - 8 >= wpos ? pos - off : -1;
        }

        private int atEof(byte[] b, int off, int pos, int limit) throws IOException {
            if (wpos == 18) throw new IOException("Base64 stream has one un-decoded dangling byte.");
            rpos = 24;
            return leftovers(b, off, pos, limit);
        }

        private int padding(byte[] b, int off, int pos, int limit) throws IOException {
            if (wpos >= 18 || wpos == 12 && is.read() != '=') throw new IOException("Illegal base64 ending sequence:" + wpos);
            rpos = 24;
            return leftovers(b, off, pos, limit);
        }

        public int read(byte[] b, int off, int len) throws IOException {
            if (closed) throw new IOException("Stream is closed");
            if (b == null) throw new NullPointerException("Cannot read the array length because \"b\" is null");
            if ((b.length | off | len) < 0 || len > b.length - off)
                throw new IndexOutOfBoundsException("Range [" + off + ", " + off + " + " + len
                    + ") out of bounds for length " + b.length);
            if (len == 0) return 0;
            int pos = off;
            final int limit = off + len;
            if (eof) return leftovers(b, off, pos, limit);
            if (rpos == 16) {
                b[pos++] = (byte) (bits >> 8);
                rpos = 8;
                if (pos == limit) return len;
            }
            if (rpos == 8) {
                b[pos++] = (byte) bits;
                rpos = 0;
                if (pos == limit) return len;
            }
            bits = 0;
            wpos = 24;
            for (;;) {
                final int i = is.read();
                if (i < 0) return atEof(b, off, pos, limit);
                final int v = base64[i];
                if (v < 0) {
                    if (v == -1) {
                        if (isMIME) continue;
                        throw new IOException("Illegal base64 character 0x" + Integer.toHexString(i));
                    }
                    return padding(b, off, pos, limit);
                }
                wpos -= 6;
                bits |= v << wpos;
                if (wpos != 0) continue;
                if (limit - pos >= 3) {
                    b[pos++] = (byte) (bits >> 16);
                    b[pos++] = (byte) (bits >> 8);
                    b[pos++] = (byte) bits;
                    bits = 0;
                    wpos = 24;
                    if (pos == limit) return len;
                    continue;
                }
                b[pos++] = (byte) (bits >> 16);
                if (pos == limit) {
                    rpos = 16;
                    return len;
                }
                b[pos++] = (byte) (bits >> 8);
                rpos = 8;
                return len;
            }
        }

        public int available() throws IOException {
            if (closed) throw new IOException("Stream is closed");
            return is.available();
        }

        public void close() throws IOException {
            if (!closed) {
                closed = true;
                is.close();
            }
        }
    }
}

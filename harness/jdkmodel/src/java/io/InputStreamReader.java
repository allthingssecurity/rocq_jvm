/*
 * rocq-jvm model of java.io.InputStreamReader (clean-room, Apache-2.0) for the six standard
 * charsets, with the observable behaviour of JDK 21's sun.nio.cs.StreamDecoder and of the
 * charsets' decoders (malformed input replaced by U+FFFD; UTF-8 with the JDK's malformed
 * lengths, UTF-16 with byte-order-mark detection that starts again after the end of input):
 * - an 8192-byte buffer, refilled (after moving the unread bytes to its start) by one read of
 *   the stream into the rest of it; a stream read returning 0 is
 *   IOException("Underlying input stream returned zero bytes");
 * - read(char[], off, len) decodes into the caller's array and reads the stream again only
 *   while nothing has been decoded or the stream has bytes available(); read() and
 *   read(cbuf, off, 1) decode two chars and keep the second one for the next read;
 * - at the end of input, the bytes left in the buffer are one malformed input and the decoder
 *   is reset; ready() is a kept char, buffered bytes, or the stream's available() > 0.
 * The decisions where each decoder stops (output full, incomplete input) follow the JDK's
 * decode loops, so the stream sees the same reads and each read returns the same chars.
 * Not modelled (STUCK): other charsets, CharsetDecoder arguments, read(CharBuffer).
 */
package java.io;

import java.nio.charset.Charset;
import java.nio.charset.CharsetDecoder;

public class InputStreamReader extends Reader {
    private static final int UNDER = -1, OVER = -2;
    private static final int NONE = 0, BIG = 1, LITTLE = 2;

    private final InputStream in;
    private final int kind;
    private final byte[] bb = new byte[8192];
    private int bpos = 0, blim = 0;
    private volatile boolean closed;
    private boolean haveLeftover = false;
    private char leftover;
    private final int expectedOrder;
    private int order;
    // the char destination of the current decode step
    private char[] dst;
    private int dp, dl;

    public InputStreamReader(InputStream in) {
        super(in);
        this.in = in;
        this.kind = ModelIo.kindOf(Charset.defaultCharset());
        this.expectedOrder = this.order = initialOrder(kind);
    }

    public InputStreamReader(InputStream in, String charsetName) throws UnsupportedEncodingException {
        super(in);
        if (charsetName == null) throw new NullPointerException("charsetName");
        this.in = in;
        this.kind = ModelIo.kindOf(ModelIo.charsetFor(charsetName));
        this.expectedOrder = this.order = initialOrder(kind);
    }

    public InputStreamReader(InputStream in, Charset cs) {
        super(in);
        if (cs == null) throw new NullPointerException("charset");
        this.in = in;
        this.kind = ModelIo.kindOf(cs);
        this.expectedOrder = this.order = initialOrder(kind);
    }

    public InputStreamReader(InputStream in, CharsetDecoder dec) {
        super(in);
        if (dec == null) throw new NullPointerException("charset decoder");
        throw ModelIo.unsupported("InputStreamReader with a CharsetDecoder");
    }

    private static int initialOrder(int kind) {
        if (kind == ModelIo.UTF16) return NONE;
        if (kind == ModelIo.UTF16LE) return LITTLE;
        return BIG;
    }

    public String getEncoding() {
        return closed ? null : ModelIo.historicalName(kind);
    }

    // ---- the decoders ----------------------------------------------------------------------

    private static boolean notCont(int b) {
        return (b & 0xc0) != 0x80;
    }

    private static boolean malformed3_2(int b1, int b2) {
        return (b1 == (byte) 0xe0 && (b2 & 0xe0) == 0x80) || (b2 & 0xc0) != 0x80;
    }

    private static boolean malformed4_2(int b1, int b2) {
        return (b1 == 0xf0 && (b2 < 0x90 || b2 > 0xbf)) || (b1 == 0xf4 && (b2 & 0xf0) != 0x80) || (b2 & 0xc0) != 0x80;
    }

    private char unit(int b1, int b2) {
        return (char) (order == BIG ? (b1 << 8) | b2 : (b2 << 8) | b1);
    }

    /** One decodeLoop over bb[bpos..blim) into dst[dp..dl): UNDER, OVER, or the length (>= 1)
     *  of a malformed input at bpos. */
    private int decodeLoop() {
        switch (kind) {
            case ModelIo.LATIN1:
                while (bpos < blim) {
                    if (dp >= dl) return OVER;
                    dst[dp++] = (char) (bb[bpos++] & 0xff);
                }
                return UNDER;
            case ModelIo.ASCII:
                while (bpos < blim) {
                    if (dp >= dl) return OVER;
                    byte b = bb[bpos];
                    if (b < 0) return 1;
                    dst[dp++] = (char) b;
                    bpos++;
                }
                return UNDER;
            case ModelIo.UTF8:
                return decodeUtf8();
            default:
                return decodeUtf16();
        }
    }

    private int decodeUtf8() {
        while (bpos < blim) {
            int b1 = bb[bpos];
            int rem = blim - bpos;
            if (b1 >= 0) {
                if (dp >= dl) return OVER;
                dst[dp++] = (char) b1;
                bpos++;
            } else if ((b1 >> 5) == -2 && (b1 & 0x1e) != 0) {
                if (rem < 2) return UNDER;
                if (dp >= dl) return OVER;
                int b2 = bb[bpos + 1];
                if (notCont(b2)) return 1;
                dst[dp++] = (char) (((b1 << 6) ^ b2) ^ (((byte) 0xC0 << 6) ^ ((byte) 0x80)));
                bpos += 2;
            } else if ((b1 >> 4) == -2) {
                if (rem < 3 || dp >= dl) {
                    if (rem > 1 && malformed3_2(b1, bb[bpos + 1])) return 1;
                    return rem < 3 ? UNDER : OVER;
                }
                int b2 = bb[bpos + 1];
                int b3 = bb[bpos + 2];
                if ((b1 == (byte) 0xe0 && (b2 & 0xe0) == 0x80) || notCont(b2)) return 1;
                if (notCont(b3)) return 2;
                char c = (char) ((b1 << 12) ^ (b2 << 6) ^ (b3 ^ (((byte) 0xE0 << 12) ^ ((byte) 0x80 << 6) ^ ((byte) 0x80))));
                if (c >= '\uD800' && c <= '\uDFFF') return 3;
                dst[dp++] = c;
                bpos += 3;
            } else if ((b1 >> 3) == -2) {
                int u1 = b1 & 0xff;
                if (rem < 4 || dl - dp < 2) {
                    if (u1 > 0xf4 || rem > 1 && malformed4_2(u1, bb[bpos + 1] & 0xff)) return 1;
                    if (rem > 2 && notCont(bb[bpos + 2])) return 2;
                    return rem < 4 ? UNDER : OVER;
                }
                int b2 = bb[bpos + 1];
                int b3 = bb[bpos + 2];
                int b4 = bb[bpos + 3];
                int uc = (b1 << 18) ^ (b2 << 12) ^ (b3 << 6)
                    ^ (b4 ^ (((byte) 0xF0 << 18) ^ ((byte) 0x80 << 12) ^ ((byte) 0x80 << 6) ^ ((byte) 0x80)));
                if (notCont(b2) || notCont(b3) || notCont(b4) || uc < 0x10000 || uc > 0x10FFFF) {
                    int u2 = b2 & 0xff;
                    if (u1 > 0xf4 || (u1 == 0xf0 && (u2 < 0x90 || u2 > 0xbf)) || (u1 == 0xf4 && (u2 & 0xf0) != 0x80)
                            || notCont(u2)) return 1;
                    if (notCont(b3)) return 2;
                    return 3;
                }
                dst[dp++] = (char) ((uc >>> 10) + (0xD800 - (0x10000 >>> 10)));
                dst[dp++] = (char) ((uc & 0x3ff) + 0xDC00);
                bpos += 4;
            } else {
                return 1;
            }
        }
        return UNDER;
    }

    private int decodeUtf16() {
        while (blim - bpos > 1) {
            int b1 = bb[bpos] & 0xff;
            int b2 = bb[bpos + 1] & 0xff;
            if (order == NONE) {
                int m = (b1 << 8) | b2;
                if (m == 0xFEFF) {
                    order = BIG;
                    bpos += 2;
                    continue;
                } else if (m == 0xFFFE) {
                    order = LITTLE;
                    bpos += 2;
                    continue;
                }
                order = BIG;
            }
            char c = unit(b1, b2);
            if (c >= '\uD800' && c <= '\uDFFF') {
                if (c <= '\uDBFF') {
                    if (blim - bpos - 2 < 2) return UNDER;
                    char c2 = unit(bb[bpos + 2] & 0xff, bb[bpos + 3] & 0xff);
                    if (c2 < '\uDC00' || c2 > '\uDFFF') return 4;
                    if (dl - dp < 2) return OVER;
                    bpos += 4;
                    dst[dp++] = c;
                    dst[dp++] = c2;
                    continue;
                }
                return 2;
            }
            if (dp >= dl) return OVER;
            bpos += 2;
            dst[dp++] = c;
        }
        return UNDER;
    }

    /** CharsetDecoder.decode(bb, dst, endOfInput) with the REPLACE actions. */
    private int decode(boolean endOfInput) {
        for (;;) {
            int r = decodeLoop();
            if (r == OVER) return OVER;
            int len;
            if (r == UNDER) {
                if (endOfInput && bpos < blim) len = blim - bpos;
                else return UNDER;
            } else {
                len = r;
            }
            if (dp >= dl) return OVER;
            dst[dp++] = '�';
            bpos += len;
        }
    }

    // ---- StreamDecoder ---------------------------------------------------------------------

    private void checkOpen() throws IOException {
        if (closed) throw new IOException("Stream closed");
    }

    /** compact, one read of the stream into the free space, flip. */
    private int readBytes() throws IOException {
        int rem = blim - bpos;
        System.arraycopy(bb, bpos, bb, 0, rem);
        int filled = rem;
        try {
            int n = in.read(bb, rem, bb.length - rem);
            if (n < 0) return n;
            if (n == 0) throw new IOException("Underlying input stream returned zero bytes");
            filled = rem + n;
        } finally {
            bpos = 0;
            blim = filled;
        }
        return blim - bpos;
    }

    private boolean inReady() {
        try {
            return in != null && in.available() > 0;
        } catch (IOException x) {
            return false;
        }
    }

    private boolean implReady() {
        return bpos < blim || inReady();
    }

    private int implRead(char[] cbuf, int off, int end) throws IOException {
        dst = cbuf;
        dp = off;
        dl = end;
        boolean eof = false;
        try {
            for (;;) {
                int r = decode(eof);
                if (r == UNDER) {
                    if (eof) break;
                    if (dp >= dl) break;
                    if (dp > off && !inReady()) break;
                    int n = readBytes();
                    if (n < 0) {
                        eof = true;
                        if (dp == off && bpos >= blim) break;
                    }
                    continue;
                }
                break;
            }
            if (eof) order = expectedOrder;
            if (dp == off && eof) return -1;
            return dp - off;
        } finally {
            dst = null;
        }
    }

    private int read0() throws IOException {
        synchronized (lock) {
            if (haveLeftover) {
                haveLeftover = false;
                return leftover;
            }
            char[] two = new char[2];
            int n = read1(two, 0, 2);
            if (n == -1) return -1;
            if (n == 2) {
                leftover = two[1];
                haveLeftover = true;
            }
            return two[0];
        }
    }

    private int read1(char[] cbuf, int off, int len) throws IOException {
        synchronized (lock) {
            checkOpen();
            if (off < 0) throw new IndexOutOfBoundsException();
            if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
            if (off > cbuf.length || len < 0 || off + len > cbuf.length || off + len < 0)
                throw new IndexOutOfBoundsException();
            if (len == 0) return 0;
            int n = 0;
            if (haveLeftover) {
                cbuf[off] = leftover;
                off++;
                len--;
                haveLeftover = false;
                n = 1;
                if (len == 0 || !implReady()) return n;
            }
            if (len == 1) {
                int c = read0();
                if (c == -1) return n == 0 ? -1 : n;
                cbuf[off] = (char) c;
                return n + 1;
            }
            int nr = implRead(cbuf, off, off + len);
            if (nr < 0) return n == 1 ? 1 : nr;
            return n + nr;
        }
    }

    public int read(java.nio.CharBuffer target) throws IOException {
        throw ModelIo.unsupported("InputStreamReader.read(CharBuffer)");
    }

    public int read() throws IOException {
        return read0();
    }

    public int read(char[] cbuf, int off, int len) throws IOException {
        return read1(cbuf, off, len);
    }

    public boolean ready() throws IOException {
        synchronized (lock) {
            checkOpen();
            return haveLeftover || implReady();
        }
    }

    public void close() throws IOException {
        synchronized (lock) {
            if (closed) return;
            try {
                in.close();
            } finally {
                closed = true;
            }
        }
    }
}

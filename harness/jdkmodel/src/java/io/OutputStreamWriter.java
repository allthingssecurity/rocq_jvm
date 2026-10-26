/*
 * rocq-jvm model of java.io.OutputStreamWriter (clean-room, Apache-2.0) for the six standard
 * charsets, with the observable behaviour of JDK 21's sun.nio.cs.StreamEncoder and of the
 * charsets' encoders (malformed and unmappable input replaced by the charset's replacement:
 * '?' or, for UTF-16, U+FFFD's two bytes):
 * - a byte buffer of 512 bytes that grows (after writing out its bytes) to
 *   min(len * maxBytesPerChar, 8192) for a write of len chars (maxBytesPerChar: UTF-8 3,
 *   ISO-8859-1 / US-ASCII 1, UTF-16 4, UTF-16BE/LE 2); full buffers are written to the stream;
 * - a high surrogate at the end of a write is kept until the next write (or close, where it is
 *   malformed); UTF-16 writes its byte-order mark FE FF before the first char;
 * - flush writes the buffer and flushes the stream; close writes the rest and closes the
 *   stream (try-with-resources), getEncoding gives the historical name (null once closed).
 * The decisions where each encoder stops (output full, incomplete surrogate pair) follow the
 * JDK's encode loops, so the stream receives the same writes as in the JDK.
 * Not modelled (STUCK): other charsets, CharsetEncoder arguments, CharBuffer arguments.
 */
package java.io;

import java.nio.charset.Charset;
import java.nio.charset.CharsetEncoder;

public class OutputStreamWriter extends Writer {
    private static final int MAX_BB = 8192;
    private static final int UNDER = -1, OVER = -2;

    private final OutputStream out;
    private final int kind;
    private final byte[] repl;
    private final int maxBytesPerChar;
    private boolean needsMark;
    private byte[] bb = new byte[512];
    private int bpos = 0;
    // the ByteBuffer's limit: the capacity, except after a failed write of the stream, which
    // leaves the JDK's buffer flipped (position 0, limit the old position)
    private int blim = 512;
    private volatile boolean closed;
    private boolean haveLeftover = false;
    private char leftover;
    // the char source of the current encode step
    private char[] src;
    private int sp, sl;

    public OutputStreamWriter(OutputStream out, String charsetName) throws UnsupportedEncodingException {
        super(out);
        if (charsetName == null) throw new NullPointerException("charsetName");
        this.out = out;
        this.kind = ModelIo.kindOf(ModelIo.charsetFor(charsetName));
        this.repl = replacement(kind);
        this.maxBytesPerChar = maxBytes(kind);
        this.needsMark = kind == ModelIo.UTF16;
    }

    public OutputStreamWriter(OutputStream out) {
        super(out);
        this.out = out;
        this.kind = ModelIo.kindOf(out instanceof PrintStream ? ((PrintStream) out).charset() : Charset.defaultCharset());
        this.repl = replacement(kind);
        this.maxBytesPerChar = maxBytes(kind);
        this.needsMark = kind == ModelIo.UTF16;
    }

    public OutputStreamWriter(OutputStream out, Charset cs) {
        super(out);
        if (cs == null) throw new NullPointerException("charset");
        this.out = out;
        this.kind = ModelIo.kindOf(cs);
        this.repl = replacement(kind);
        this.maxBytesPerChar = maxBytes(kind);
        this.needsMark = kind == ModelIo.UTF16;
    }

    public OutputStreamWriter(OutputStream out, CharsetEncoder enc) {
        super(out);
        if (enc == null) throw new NullPointerException("charset encoder");
        throw ModelIo.unsupported("OutputStreamWriter with a CharsetEncoder");
    }

    private static byte[] replacement(int kind) {
        if (kind == ModelIo.UTF16LE) return new byte[] {(byte) 0xfd, (byte) 0xff};
        if (kind >= ModelIo.UTF16) return new byte[] {(byte) 0xff, (byte) 0xfd};
        return new byte[] {(byte) '?'};
    }

    private static int maxBytes(int kind) {
        switch (kind) {
            case ModelIo.UTF8: return 3;
            case ModelIo.UTF16: return 4;
            case ModelIo.UTF16BE:
            case ModelIo.UTF16LE: return 2;
            default: return 1;
        }
    }

    public String getEncoding() {
        return closed ? null : ModelIo.historicalName(kind);
    }

    // ---- the encoders ----------------------------------------------------------------------

    private int room() {
        return blim - bpos;
    }

    private void put(int b) {
        bb[bpos++] = (byte) b;
    }

    private void unit(char c) {
        if (kind == ModelIo.UTF16LE) {
            put(c & 0xff);
            put(c >> 8);
        } else {
            put(c >> 8);
            put(c & 0xff);
        }
    }

    private static boolean isHigh(char c) {
        return c >= '\uD800' && c <= '\uDBFF';
    }

    private static boolean isLow(char c) {
        return c >= '\uDC00' && c <= '\uDFFF';
    }

    /** Surrogate.Parser on src[sp]: UNDER for a high surrogate at the end, 1 for a malformed
     *  surrogate, 0 for a pair. */
    private int parsePair() {
        char c = src[sp];
        if (isHigh(c)) {
            if (sl - sp < 2) return UNDER;
            return isLow(src[sp + 1]) ? 0 : 1;
        }
        return 1;
    }

    /** One encodeLoop: UNDER, OVER, or the length (>= 1) of a malformed / unmappable input. */
    private int encodeLoop() {
        switch (kind) {
            case ModelIo.UTF8:
                while (sp < sl) {
                    char c = src[sp];
                    if (c < 0x80) {
                        if (room() < 1) return OVER;
                        put(c);
                    } else if (c < 0x800) {
                        if (room() < 2) return OVER;
                        put(0xc0 | (c >> 6));
                        put(0x80 | (c & 0x3f));
                    } else if (c >= '\uD800' && c <= '\uDFFF') {
                        int r = parsePair();
                        if (r != 0) return r;
                        if (room() < 4) return OVER;
                        int uc = ((c - 0xD800) << 10) + (src[sp + 1] - 0xDC00) + 0x10000;
                        put(0xf0 | (uc >> 18));
                        put(0x80 | ((uc >> 12) & 0x3f));
                        put(0x80 | ((uc >> 6) & 0x3f));
                        put(0x80 | (uc & 0x3f));
                        sp++;
                    } else {
                        if (room() < 3) return OVER;
                        put(0xe0 | (c >> 12));
                        put(0x80 | ((c >> 6) & 0x3f));
                        put(0x80 | (c & 0x3f));
                    }
                    sp++;
                }
                return UNDER;
            case ModelIo.LATIN1:
                while (sp < sl) {
                    if (room() < 1) return OVER;
                    char c = src[sp];
                    if (c > 0xff) {
                        int r = parsePair();
                        if (r == UNDER) return UNDER;
                        return r == 0 ? 2 : 1;
                    }
                    put(c);
                    sp++;
                }
                return UNDER;
            case ModelIo.ASCII:
                while (sp < sl) {
                    char c = src[sp];
                    if (c >= 0x80) {
                        int r = parsePair();
                        if (r == UNDER) return UNDER;
                        return r == 0 ? 2 : 1;
                    }
                    if (room() < 1) return OVER;
                    put(c);
                    sp++;
                }
                return UNDER;
            default:
                if (needsMark && sp < sl) {
                    if (room() < 2) return OVER;
                    unit('﻿');
                    needsMark = false;
                }
                while (sp < sl) {
                    char c = src[sp];
                    if (c < '\uD800' || c > '\uDFFF') {
                        if (room() < 2) return OVER;
                        unit(c);
                        sp++;
                        continue;
                    }
                    int r = parsePair();
                    if (r != 0) return r;
                    if (room() < 4) return OVER;
                    unit(c);
                    unit(src[sp + 1]);
                    sp += 2;
                }
                return UNDER;
        }
    }

    /** CharsetEncoder.encode(src, bb, endOfInput) with the REPLACE actions. */
    private int encode(boolean endOfInput) {
        for (;;) {
            int r = encodeLoop();
            if (r == OVER) return OVER;
            int len;
            if (r == UNDER) {
                if (endOfInput && sp < sl) len = sl - sp;
                else return UNDER;
            } else {
                len = r;
            }
            if (room() < repl.length) return OVER;
            for (byte b : repl) put(b);
            sp += len;
        }
    }

    // ---- StreamEncoder ---------------------------------------------------------------------

    private void writeBytes() throws IOException {
        blim = bpos;
        bpos = 0;
        if (blim > 0) out.write(bb, 0, blim);
        bpos = 0;
        blim = bb.length;
    }

    /** StreamEncoder.flushLeftoverChar(cb, endOfInput); cb is src[sp..sl) or none. */
    private void flushLeftoverChar(char[] cb, int[] cpos, int climit, boolean endOfInput) throws IOException {
        if (!haveLeftover && !endOfInput) return;
        char[] l = new char[2];
        int n = 0;
        if (haveLeftover) l[n++] = leftover;
        if (cb != null && cpos[0] < climit) l[n++] = cb[cpos[0]++];
        src = l;
        sp = 0;
        sl = n;
        while (sp < sl || endOfInput) {
            int r = encode(endOfInput);
            if (r == UNDER) {
                if (sp < sl) {
                    leftover = src[sp++];
                    if (cb != null && cpos[0] < climit) {
                        l = new char[] {leftover, cb[cpos[0]++]};
                        src = l;
                        sp = 0;
                        sl = 2;
                        continue;
                    }
                    return;
                }
                break;
            }
            writeBytes();
        }
        haveLeftover = false;
    }

    private void growIfNeeded(int len) throws IOException {
        int cap = bb.length;
        if (cap < MAX_BB) {
            int newCap = Math.min(len * maxBytesPerChar, MAX_BB);
            if (newCap > cap) {
                writeBytes();
                bb = new byte[newCap];
                bpos = 0;
                blim = newCap;
            }
        }
    }

    private void implWrite(char[] cbuf, int off, int len) throws IOException {
        int[] cpos = {off};
        int climit = off + len;
        if (haveLeftover) flushLeftoverChar(cbuf, cpos, climit, false);
        growIfNeeded(climit - cpos[0]);
        src = cbuf;
        sp = cpos[0];
        sl = climit;
        while (sp < sl) {
            int r = encode(false);
            if (r == UNDER) {
                if (sl - sp == 1) {
                    haveLeftover = true;
                    leftover = src[sp++];
                }
                break;
            }
            writeBytes();
        }
        src = null;
    }

    private void checkOpen() throws IOException {
        if (closed) throw new IOException("Stream closed");
    }

    /** Package-private in the JDK too (PrintStream calls it). */
    void flushBuffer() throws IOException {
        synchronized (lock) {
            if (closed) throw new IOException("Stream closed");
            if (bpos > 0) writeBytes();
        }
    }

    // StreamEncoder's own write methods (the OutputStreamWriter methods call these, never each
    // other, as the JDK's StreamEncoder does not dispatch back to the OutputStreamWriter)

    private void seWrite(char[] cbuf, int off, int len) throws IOException {
        synchronized (lock) {
            checkOpen();
            if (off < 0) throw new IndexOutOfBoundsException();
            if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
            if (off > cbuf.length || len < 0 || off + len > cbuf.length || off + len < 0)
                throw new IndexOutOfBoundsException();
            if (len == 0) return;
            implWrite(cbuf, off, len);
        }
    }

    private void seWrite(String str, int off, int len) throws IOException {
        if (len < 0) throw new IndexOutOfBoundsException();
        char[] cbuf = new char[len];
        if (str == null) throw ModelIo.invokeOnNull("String.getChars(int, int, char[], int)", "str");
        ModelIo.getChars(str, off, off + len, cbuf, 0);
        seWrite(cbuf, 0, len);
    }

    public void write(int c) throws IOException {
        seWrite(new char[] {(char) c}, 0, 1);
    }

    public void write(char[] cbuf, int off, int len) throws IOException {
        seWrite(cbuf, off, len);
    }

    public void write(String str, int off, int len) throws IOException {
        seWrite(str, off, len);
    }

    public Writer append(CharSequence csq, int start, int end) throws IOException {
        if (csq == null) csq = "null";
        return append(ModelIo.subSequence(csq, start, end));
    }

    public Writer append(CharSequence csq) throws IOException {
        String s = ModelIo.valueOf(csq);
        seWrite(s, 0, s.length());
        return this;
    }

    public void flush() throws IOException {
        synchronized (lock) {
            checkOpen();
            if (bpos > 0) writeBytes();
            out.flush();
        }
    }

    public void close() throws IOException {
        synchronized (lock) {
            if (closed) return;
            try {
                Throwable primary = null;
                try {
                    flushLeftoverChar(null, null, 0, true);
                    if (bpos > 0) writeBytes();
                    out.flush();
                } catch (Throwable x) {
                    primary = x;
                    throw x;
                } finally {
                    if (primary == null) {
                        out.close();
                    } else {
                        try {
                            out.close();
                        } catch (Throwable y) {
                            primary.addSuppressed(y);
                        }
                    }
                }
            } catch (IOException x) {
                needsMark = kind == ModelIo.UTF16;
                throw x;
            } finally {
                closed = true;
            }
        }
    }
}

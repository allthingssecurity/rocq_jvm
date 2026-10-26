package org.rocqjvm.jdkmodel;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.CharArrayReader;
import java.io.CharArrayWriter;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.FilterReader;
import java.io.FilterWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.PushbackInputStream;
import java.io.PushbackReader;
import java.io.Reader;
import java.io.SequenceInputStream;
import java.io.StringReader;
import java.io.StringWriter;
import java.io.UncheckedIOException;
import java.io.Writer;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.List;
import java.util.stream.Collectors;

/** Differential tests of the in-memory java.io model classes: byte and char streams, their
 *  default methods, buffering (call sequences seen by the wrapped streams), print streams,
 *  the charset coders (streaming decode / encode across buffer boundaries), data streams,
 *  pushback and sequence streams, with the JDK's exception messages. */
public final class IoOps {
    private IoOps() {
    }

    static int s;

    static int r(int n) {
        s = s * 1103515245 + 12345;
        return ((s >>> 8) & 0x7fffff) % n;
    }

    static final String HEX = "0123456789abcdef";

    static String hex(byte[] b, int off, int n) {
        StringBuilder sb = new StringBuilder();
        for (int i = off; i < off + n; i++) sb.append(HEX.charAt((b[i] >> 4) & 15)).append(HEX.charAt(b[i] & 15));
        return sb.toString();
    }

    static String hex(byte[] b) {
        return b == null ? "null" : hex(b, 0, b.length);
    }

    static String esc(String t) {
        if (t == null) return "null";
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < t.length(); i++) {
            char c = t.charAt(i);
            if (c >= 0x20 && c < 0x7f && c != '\\') sb.append(c);
            else sb.append('\\').append(Integer.toHexString(c)).append('.');
        }
        return sb.toString();
    }

    static String esc(char[] a, int off, int n) {
        return esc(new String(a, off, n));
    }

    static void exc(StringBuilder out, Throwable e) {
        out.append('!').append(e.getClass().getSimpleName()).append(':').append(esc(e.getMessage()));
        if (e.getCause() != null) out.append("<-").append(e.getCause().getClass().getSimpleName()).append(':').append(esc(e.getCause().getMessage()));
        for (Throwable x : e.getSuppressed()) out.append("+s:").append(esc(x.getMessage()));
    }

    static final String[] PIECES = {"a", "b", "xyz", " ", "\n", "\r", "\r\n", "é", "€", "😀", "\ud800", "\udc00", "\u0000", "Q", "12", "\t"};

    static String rstr(int max) {
        StringBuilder b = new StringBuilder();
        for (int i = r(max + 1); i > 0; i--) b.append(PIECES[r(PIECES.length)]);
        return b.toString();
    }

    static final int[] BYTE_POOL = {0x41, 0x62, 0x0a, 0x0d, 0x00, 0x7f, 0x80, 0xbf, 0xc2, 0xc3, 0xa9, 0xe0, 0xe2, 0x82, 0xac, 0xed, 0xa0,
        0xf0, 0x9f, 0x98, 0x80, 0xf4, 0x90, 0xf8, 0xff, 0xfe, 0xd8, 0xdc, 0x3d};

    static byte[] rbytes(int max) {
        int n = r(max + 1);
        byte[] b = new byte[n];
        for (int i = 0; i < n; i++) b[i] = (byte) (r(3) == 0 ? r(256) : BYTE_POOL[r(BYTE_POOL.length)]);
        return b;
    }

    static Charset rcs() {
        switch (r(6)) {
            case 0: return StandardCharsets.UTF_8;
            case 1: return StandardCharsets.ISO_8859_1;
            case 2: return StandardCharsets.US_ASCII;
            case 3: return StandardCharsets.UTF_16;
            case 4: return StandardCharsets.UTF_16BE;
            default: return StandardCharsets.UTF_16LE;
        }
    }

    /** An InputStream over bytes that returns short reads, reports random available() values and
     *  may fail at a given read call; it logs its calls. */
    static final class Trickle extends InputStream {
        final byte[] data;
        int pos;
        final int chunk;
        final int availMode;
        int calls;
        final int failAt;
        final StringBuilder log;

        Trickle(byte[] data, StringBuilder log) {
            this.data = data;
            this.chunk = 1 + r(5);
            this.availMode = r(3);
            this.failAt = r(4) == 0 ? r(6) : -1;
            this.log = log;
        }

        private void call(String what) throws IOException {
            if (log != null) log.append(what);
            if (calls++ == failAt) throw new IOException("trickle fails");
        }

        public int read() throws IOException {
            call("r");
            return pos < data.length ? data[pos++] & 0xff : -1;
        }

        public int read(byte[] b, int off, int len) throws IOException {
            call("R" + len);
            if (len < 0 || off < 0) throw new IndexOutOfBoundsException("trickle");
            if (len == 0) return 0;
            if (pos >= data.length) return -1;
            int n = Math.min(Math.min(len, chunk), data.length - pos);
            System.arraycopy(data, pos, b, off, n);
            pos += n;
            return n;
        }

        public int available() {
            if (availMode == 0) return data.length - pos;
            if (availMode == 1) return 0;
            return Math.min(1, data.length - pos);
        }

        public void close() throws IOException {
            if (log != null) log.append('C');
        }
    }

    /** An OutputStream that logs every call and keeps the bytes; may fail at a given call. */
    static final class Log extends OutputStream {
        final ByteArrayOutputStream bytes = new ByteArrayOutputStream();
        final StringBuilder log = new StringBuilder();
        int calls;
        final int failAt;

        Log(int failAt) {
            this.failAt = failAt;
        }

        private void call(String what) throws IOException {
            log.append(what);
            if (calls++ == failAt) throw new IOException("log fails");
        }

        public void write(int b) throws IOException {
            call("w");
            bytes.write(b);
        }

        public void write(byte[] b, int off, int len) throws IOException {
            call("W" + len);
            bytes.write(b, off, len);
        }

        public void flush() throws IOException {
            call("F");
        }

        public void close() throws IOException {
            call("C");
        }

        String show() {
            return log + "=" + hex(bytes.toByteArray());
        }
    }

    /** A Reader over a string with short reads and random ready(). */
    static final class TrickleReader extends Reader {
        final String data;
        int pos;
        final int chunk;
        final boolean readyAlways;
        final StringBuilder log;

        TrickleReader(String data, StringBuilder log) {
            this.data = data;
            this.chunk = 1 + r(6);
            this.readyAlways = r(2) == 0;
            this.log = log;
        }

        public int read(char[] b, int off, int len) {
            if (log != null) log.append('R').append(len);
            if (len < 0 || off < 0) throw new IndexOutOfBoundsException("trickle");
            if (len == 0) return 0;
            if (pos >= data.length()) return -1;
            int n = Math.min(Math.min(len, chunk), data.length() - pos);
            for (int i = 0; i < n; i++) b[off + i] = data.charAt(pos + i);
            pos += n;
            return n;
        }

        public boolean ready() {
            return readyAlways && pos < data.length();
        }

        public void close() {
            if (log != null) log.append('C');
        }
    }

    /** A Writer that logs its calls and keeps the chars. */
    static final class LogWriter extends Writer {
        final StringBuilder text = new StringBuilder();
        final StringBuilder log = new StringBuilder();

        public void write(char[] b, int off, int len) {
            log.append('W').append(len);
            for (int i = 0; i < len; i++) text.append(b[off + i]);
        }

        public void flush() {
            log.append('F');
        }

        public void close() {
            log.append('C');
        }

        String show() {
            return log + "=" + esc(text.toString());
        }
    }

    static int ri() {
        return r(8) - 2;
    }

    // ---------------------------------------------------------------------------------------

    /** ByteArrayInputStream / ByteArrayOutputStream and the InputStream / OutputStream defaults. */
    public static String bytes(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        byte[] data = rbytes(12);
        InputStream in = null;
        ByteArrayOutputStream bo = new ByteArrayOutputStream(r(3) == 0 ? r(4) : 32);
        int kind = r(5);
        try {
            switch (kind) {
                case 0: in = new ByteArrayInputStream(data); break;
                case 1: in = new ByteArrayInputStream(data, ri(), r(8) - 1); break;
                case 2: in = new Trickle(data, out); break;
                case 3: in = InputStream.nullInputStream(); break;
                default: in = new ByteArrayInputStream(r(5) == 0 ? null : data); break;
            }
        } catch (RuntimeException e) {
            exc(out, e);
            return out.toString();
        }
        OutputStream os = r(2) == 0 ? bo : r(2) == 0 ? OutputStream.nullOutputStream() : new Log(r(3) == 0 ? r(4) : -1);
        int ops = 6 + r(12);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(22)) {
                    case 0: case 1: out.append(in.read()); break;
                    case 2: { byte[] b = new byte[r(6)]; int n = in.read(b); out.append(n).append(':').append(hex(b)); break; }
                    case 3: { byte[] b = new byte[5]; int n = in.read(b, ri(), ri()); out.append(n).append(':').append(hex(b)); break; }
                    case 4: out.append(hex(in.readAllBytes())); break;
                    case 5: out.append(hex(in.readNBytes(r(6) - 1))); break;
                    case 6: { byte[] b = new byte[4]; out.append(in.readNBytes(b, ri(), ri())).append(':').append(hex(b)); break; }
                    case 7: out.append(in.skip(r(7) - 2)); break;
                    case 8: in.skipNBytes(r(6) - 1); out.append('k'); break;
                    case 9: out.append(in.available()); break;
                    case 10: out.append(in.markSupported()); in.mark(r(4)); break;
                    case 11: in.reset(); out.append('R'); break;
                    case 12: out.append(in.transferTo(r(6) == 0 ? null : os)); break;
                    case 13: in.close(); out.append('C'); break;
                    case 14: os.write(r(300) - 20); break;
                    case 15: { byte[] b = rbytes(5); os.write(b, ri(), ri()); break; }
                    case 16: os.write(r(5) == 0 ? null : rbytes(4)); break;
                    case 17: os.flush(); os.close(); out.append("fc"); break;
                    case 18: out.append(bo.size()).append(hex(bo.toByteArray())); break;
                    case 19: {
                        switch (r(5)) {
                            case 0: out.append(esc(bo.toString())); break;
                            case 1: out.append(esc(bo.toString(rcs()))); break;
                            case 2: out.append(esc(bo.toString(r(2) == 0 ? "UTF-16" : r(2) == 0 ? "latin1" : "x y"))); break;
                            case 3: bo.reset(); out.append('0'); break;
                            default: bo.writeTo(r(4) == 0 ? null : os); break;
                        }
                        break;
                    }
                    case 20: bo.writeBytes(rbytes(3)); break;
                    default: { byte[] b = rbytes(4); bo.write(b, ri(), ri()); break; }
                }
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        if (os instanceof Log) out.append(((Log) os).show());
        out.append('|').append(hex(bo.toByteArray()));
        return out.toString();
    }

    /** StringReader / StringWriter / CharArrayReader / CharArrayWriter and the Reader / Writer
     *  defaults (a Reader and a Writer subclass that only implement the abstract methods). */
    public static String chars(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        String text = rstr(6);
        Reader rd;
        try {
            switch (r(5)) {
                case 0: rd = new StringReader(r(8) == 0 ? null : text); break;
                case 1: rd = new CharArrayReader(text.toCharArray()); break;
                case 2: rd = new CharArrayReader(text.toCharArray(), ri(), r(8) - 1); break;
                case 3: rd = new TrickleReader(text, out); break;
                default: rd = Reader.nullReader(); break;
            }
        } catch (RuntimeException e) {
            exc(out, e);
            return out.toString();
        }
        StringWriter sw = r(4) == 0 ? new StringWriter(r(5) - 1) : new StringWriter();
        CharArrayWriter cw = new CharArrayWriter(r(3) == 0 ? r(3) : 32);
        LogWriter lw = new LogWriter();
        Writer nw = Writer.nullWriter();
        int ops = 6 + r(14);
        for (int k = 0; k < ops; k++) {
            Writer w = r(4) == 0 ? lw : r(3) == 0 ? cw : r(5) == 0 ? nw : sw;
            try {
                switch (r(24)) {
                    case 0: case 1: out.append(rd.read()); break;
                    case 2: { char[] b = new char[r(5)]; int n = rd.read(b); out.append(n).append(':').append(esc(new String(b))); break; }
                    case 3: { char[] b = new char[4]; int n = rd.read(b, ri(), ri()); out.append(n).append(':').append(esc(new String(b))); break; }
                    case 4: out.append(rd.skip(r(7) - 2)); break;
                    case 5: out.append(rd.ready()); break;
                    case 6: out.append(rd.markSupported()); rd.mark(r(5) - 1); break;
                    case 7: rd.reset(); out.append('R'); break;
                    case 8: out.append(rd.transferTo(r(6) == 0 ? null : w)); break;
                    case 9: rd.close(); out.append('C'); break;
                    case 10: w.write(r(3) == 0 ? 0x1f600 + r(3) : 'a' + r(26)); break;
                    case 11: { String t = rstr(3); w.write(r(5) == 0 ? null : t); break; }
                    case 12: { String t = rstr(3); w.write(r(5) == 0 ? null : t, ri(), ri()); break; }
                    case 13: { char[] c = rstr(3).toCharArray(); w.write(r(6) == 0 ? null : c, ri(), ri()); break; }
                    case 14: w.write(r(6) == 0 ? null : rstr(2).toCharArray()); break;
                    case 15: out.append(w.append(r(4) == 0 ? null : rstr(2)) == w); break;
                    case 16: {
                        CharSequence cs = r(3) == 0 ? new StringBuilder("sb" + rstr(2)) : r(4) == 0 ? null : rstr(3);
                        w.append(cs, ri(), ri());
                        break;
                    }
                    case 17: w.append((char) ('A' + r(26))); break;
                    case 18: w.flush(); out.append('f'); break;
                    case 19: w.close(); out.append('c'); break;
                    case 20: out.append(esc(sw.toString())).append('/').append(esc(cw.toString())).append(cw.size()); break;
                    case 21: {
                        if (r(2) == 0) cw.reset();
                        else cw.writeTo(r(5) == 0 ? null : sw);
                        out.append(esc(new String(cw.toCharArray())));
                        break;
                    }
                    case 22: {
                        Appendable a = w;
                        a.append("ap").append('p').append("xyz", 1, 2);
                        break;
                    }
                    default: { char[] b = new char[3]; out.append(rd.read(r(6) == 0 ? null : b, ri(), ri())).append(esc(new String(b))); break; }
                }
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        out.append(esc(sw.toString())).append('|').append(esc(cw.toString())).append('|').append(lw.show());
        return out.toString();
    }

    /** BufferedReader (readLine over all line ends, buffer boundaries, mark/reset, skip, ready,
     *  lines()) over StringReader and a short-reading Reader. */
    public static String bufReader(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        String text = rstr(10);
        StringBuilder log = new StringBuilder();
        Reader base = r(2) == 0 ? new StringReader(text) : new TrickleReader(text, log);
        BufferedReader br;
        try {
            br = r(3) == 0 ? new BufferedReader(r(8) == 0 ? null : base) : new BufferedReader(base, r(7) - 1);
        } catch (RuntimeException e) {
            exc(out, e);
            return out.toString();
        }
        int ops = 5 + r(12);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(14)) {
                    case 0: case 1: case 2: out.append('[').append(esc(br.readLine())).append(']'); break;
                    case 3: case 4: out.append(br.read()); break;
                    case 5: { char[] b = new char[r(8) + 1]; int n = br.read(b, r(2), r(b.length)); out.append(n).append(':').append(esc(new String(b))); break; }
                    case 6: out.append(br.skip(r(6) - 1)); break;
                    case 7: out.append(br.ready()); break;
                    case 8: br.mark(r(6) - 1); out.append('m'); break;
                    case 9: br.reset(); out.append('R'); break;
                    case 10: br.close(); out.append('C'); break;
                    case 11: {
                        int how = r(3);
                        if (how == 0) out.append(br.lines().map(IoOps::esc).collect(Collectors.joining(",", "<", ">")));
                        else if (how == 1) out.append(br.lines().limit(r(3)).count());
                        else out.append(br.lines().filter(l -> l.length() > 1).findFirst().map(IoOps::esc).orElse("-"));
                        break;
                    }
                    case 12: { char[] b = new char[2]; out.append(br.read(b)).append(esc(new String(b))); break; }
                    default: out.append(br.markSupported()); break;
                }
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        out.append(log.toString());
        return out.toString();
    }

    /** BufferedWriter, BufferedOutputStream and BufferedInputStream: the writes / reads the
     *  wrapped stream sees. */
    public static String buffered(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        LogWriter lw = new LogWriter();
        Log lo = new Log(r(4) == 0 ? r(8) : -1);
        BufferedWriter bw;
        BufferedOutputStream bos;
        BufferedInputStream bis;
        StringBuilder ilog = new StringBuilder();
        try {
            bw = r(3) == 0 ? new BufferedWriter(lw) : new BufferedWriter(lw, r(6));
            bos = r(3) == 0 ? new BufferedOutputStream(lo) : new BufferedOutputStream(lo, r(6));
            byte[] data = rbytes(14);
            bis = r(3) == 0 ? new BufferedInputStream(new Trickle(data, ilog)) : new BufferedInputStream(new Trickle(data, ilog), r(6));
        } catch (RuntimeException e) {
            exc(out, e);
            return out.toString();
        }
        int ops = 6 + r(14);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(20)) {
                    case 0: bw.write('a' + r(26)); break;
                    case 1: bw.write(rstr(3)); break;
                    case 2: { String t = rstr(4); bw.write(r(8) == 0 ? null : t, ri(), ri()); break; }
                    case 3: { char[] c = rstr(4).toCharArray(); bw.write(c, r(2), r(c.length + 1)); break; }
                    case 4: bw.newLine(); break;
                    case 5: bw.flush(); out.append('f'); break;
                    case 6: bw.close(); out.append('c'); break;
                    case 7: bw.append(rstr(2)).append('x'); break;
                    case 8: bos.write(r(256)); break;
                    case 9: { byte[] b = rbytes(9); bos.write(b, r(2), r(b.length + 1)); break; }
                    case 10: bos.write(rbytes(5)); break;
                    case 11: bos.flush(); out.append('F'); break;
                    case 12: bos.close(); out.append('C'); break;
                    case 13: case 14: out.append(bis.read()); break;
                    case 15: { byte[] b = new byte[r(9) + 1]; int n = bis.read(b, r(2), r(b.length)); out.append(n).append(':').append(hex(b)); break; }
                    case 16: out.append(bis.skip(r(6) - 1)).append('/').append(bis.available()); break;
                    case 17: bis.mark(r(5)); out.append('m'); break;
                    case 18: bis.reset(); out.append('r'); break;
                    default: { if (r(3) == 0) bis.close(); else out.append(bis.transferTo(lo)); break; }
                }
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        out.append(lw.show()).append('|').append(lo.show()).append('|').append(ilog.toString());
        return out.toString();
    }

    static final class Pt {
        final int x;

        Pt(int x) {
            this.x = x;
        }

        public String toString() {
            if (x == 3) throw new IllegalStateException("bad toString");
            return "Pt" + x;
        }

        public int hashCode() {
            return 31 * x;
        }
    }

    static Object robj() {
        switch (r(7)) {
            case 0: return null;
            case 1: return new Pt(r(5));
            case 2: return Integer.valueOf(r(100) - 50);
            case 3: return rstr(2);
            case 4: return Long.valueOf(r(1000) * 1000003L);
            case 5: return Double.valueOf(r(100) / 8.0 - 3);
            default: return Boolean.valueOf(r(2) == 0);
        }
    }

    static final String[] FORMATS = {"%d", "%s|%s", "%5.2f", "x%ny", "%-6s!", "%c%c", "%b %h", "%x", "%e", "%q", "%3$s", "%.1s", "%08.3f", "%,d", "a\nb%sc"};

    /** PrintWriter and PrintStream: print / println of every type, printf / format (also
     *  failing), append, checkError, autoflush, charsets. */
    public static String print(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        StringWriter sw = new StringWriter();
        ByteArrayOutputStream bo = new ByteArrayOutputStream();
        Log lo = new Log(r(4) == 0 ? r(10) : -1);
        boolean auto = r(2) == 0;
        PrintWriter pw;
        PrintStream ps;
        boolean psSeesPieces = false;
        try {
            switch (r(4)) {
                case 0: pw = new PrintWriter(sw, auto); break;
                case 1: pw = new PrintWriter(new BufferedWriter(sw, 4 + r(30)), auto); break;
                case 2: pw = new PrintWriter(bo, auto); break;
                default: pw = new PrintWriter(r(6) == 0 ? (Writer) null : sw); break;
            }
            switch (r(5)) {
                case 0: ps = new PrintStream(bo, auto); break;
                case 1: ps = new PrintStream(bo, auto, rcs()); break;
                case 2: ps = new PrintStream(lo, auto); psSeesPieces = true; break;
                case 3: ps = new PrintStream(bo, auto, r(3) == 0 ? "x y" : "UTF-16LE"); break;
                default: ps = new PrintStream(r(6) == 0 ? null : bo); break;
            }
        } catch (Exception e) {
            exc(out, e);
            return out.toString();
        }
        int ops = 6 + r(14);
        for (int k = 0; k < ops; k++) {
            boolean w = r(2) == 0;
            try {
                switch (r(22)) {
                    case 0: if (w) pw.print(r(200) - 100); else ps.print(r(200) - 100); break;
                    case 1: { long v = (r(100000) - 50000) * 99991L; if (w) pw.println(v); else ps.println(v); break; }
                    case 2: { float f = (r(2000) - 1000) / (1 + r(16)) * 1.5f; if (w) pw.print(f); else ps.println(f); break; }
                    case 3: { double d = (r(2000) - 1000) / (1.0 + r(32)); if (w) pw.println(d); else ps.print(d); break; }
                    case 4: { boolean b = r(2) == 0; char c = PIECES[r(PIECES.length)].charAt(0); if (w) { pw.print(b); pw.println(c); } else { ps.println(b); ps.print(c); } break; }
                    case 5: { String t = r(5) == 0 ? null : rstr(3); if (w) pw.println(t); else ps.print(t); break; }
                    case 6: { char[] c = r(6) == 0 ? null : rstr(3).toCharArray(); if (w) pw.print(c); else ps.println(c); break; }
                    case 7: { Object o = robj(); if (w) pw.print(o); else ps.println(o); break; }
                    case 8: if (w) pw.println(); else ps.println(); break;
                    case 9: case 10: {
                        // (the model Formatter makes no claim for a Double under %d / %x; the model
                        // PrintStream makes none for format onto a stream that sees the pieces)
                        String f = FORMATS[r(FORMATS.length)];
                        Object a1 = robj(), a2 = robj();
                        boolean integral = f.indexOf('d') >= 0 || f.indexOf('x') >= 0;
                        if (integral && a1 instanceof Double) a1 = 7;
                        if (integral && a2 instanceof Double) a2 = -7;
                        if (w || psSeesPieces) pw.printf(f, a1, a2); else ps.printf(f, a1, a2);
                        break;
                    }
                    case 11: { int v = r(1000); if (w || psSeesPieces) pw.format("<%d:%s>", v, rstr(2)); else ps.format("<%d:%s>", v, rstr(2)); break; }
                    case 12: { if (w) pw.append(rstr(2)).append('z').append("abcd", r(3), 2 + r(3)); else ps.append(rstr(2)).append('z').append("abcd", r(3), 2 + r(3)); break; }
                    case 13: { if (w) pw.write(r(3) == 0 ? 0x1f600 : 'q'); else ps.write(r(3) == 0 ? '\n' : 'q'); break; }
                    case 14: { if (w) { String t = rstr(3); pw.write(t, ri(), ri()); } else { byte[] b = rbytes(4); ps.write(b, ri(), ri()); } break; }
                    case 15: { if (w) pw.write(rstr(2).toCharArray(), ri(), ri()); else ps.write(rbytes(3)); break; }
                    case 16: { if (w) pw.flush(); else ps.flush(); out.append('f'); break; }
                    case 17: { if (w) pw.close(); else ps.close(); out.append('c'); break; }
                    case 18: out.append(w ? pw.checkError() : ps.checkError()); break;
                    case 19: out.append(esc(sw.toString())).append('/').append(hex(bo.toByteArray())); break;
                    case 20: { Appendable a = w ? pw : ps; a.append("A").append(r(2) == 0 ? null : "bc", 0, 1).append((char) (0xd800 + r(2) * 0x400)); break; }
                    default: { if (w) pw.write(rstr(2)); else ps.writeBytes(rbytes(3)); break; }
                }
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        out.append(esc(sw.toString())).append('|').append(hex(bo.toByteArray())).append('|').append(lo.show());
        return out.toString();
    }

    /** InputStreamReader / OutputStreamWriter with the six charsets: streaming decode over short
     *  reads (malformed input, surrogates and byte-order marks across buffer boundaries),
     *  encoding of strings with lone surrogates split across writes, the writes the stream
     *  sees, getEncoding, ready, close. */
    public static String codecs(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        Charset cs = rcs();
        out.append(cs).append(':');
        try {
            if (r(2) == 0) {
                byte[] data = rbytes(16);
                if (r(4) == 0 && cs == StandardCharsets.UTF_16 && data.length > 1) {
                    data[0] = (byte) 0xff;
                    data[1] = (byte) 0xfe;
                }
                StringBuilder log = new StringBuilder();
                InputStream in = r(3) == 0 ? new ByteArrayInputStream(data) : new Trickle(data, log);
                InputStreamReader isr;
                switch (r(4)) {
                    case 0: isr = new InputStreamReader(in, cs.name()); break;
                    case 1: isr = new InputStreamReader(in, r(5) == 0 ? (Charset) null : cs); break;
                    case 2: isr = new InputStreamReader(in, r(4) == 0 ? "bad name" : r(3) == 0 ? null : cs.aliases().contains("utf16") ? "utf16" : cs.name()); break;
                    default: isr = new InputStreamReader(in); out.append("dflt"); break;
                }
                out.append(isr.getEncoding()).append(':');
                int ops = 4 + r(12);
                for (int k = 0; k < ops; k++) {
                    try {
                        switch (r(7)) {
                            case 0: case 1: out.append(isr.read()); break;
                            case 2: case 3: { char[] b = new char[r(6) + 1]; int n = isr.read(b, r(2), r(b.length)); out.append(n).append(':').append(esc(new String(b))); break; }
                            case 4: out.append(isr.ready()); break;
                            case 5: out.append(isr.skip(r(4))); break;
                            default: { if (r(3) == 0) { isr.close(); out.append('C').append(isr.getEncoding()); } else { char[] b = new char[8]; out.append(isr.read(b)).append(esc(new String(b))); } break; }
                        }
                    } catch (Exception e) {
                        exc(out, e);
                    }
                    out.append(';');
                }
                out.append(log.toString());
            } else {
                Log lo = new Log(r(5) == 0 ? r(6) : -1);
                ByteArrayOutputStream bo = new ByteArrayOutputStream();
                OutputStream os = r(2) == 0 ? lo : bo;
                OutputStreamWriter osw;
                switch (r(3)) {
                    case 0: osw = new OutputStreamWriter(os, cs.name()); break;
                    case 1: osw = new OutputStreamWriter(os, cs); break;
                    default: osw = new OutputStreamWriter(os); break;
                }
                out.append(osw.getEncoding()).append(':');
                int ops = 4 + r(12);
                for (int k = 0; k < ops; k++) {
                    try {
                        switch (r(9)) {
                            case 0: case 1: osw.write(rstr(4)); break;
                            case 2: osw.write(PIECES[r(PIECES.length)].charAt(0)); break;
                            case 3: { char[] c = rstr(4).toCharArray(); osw.write(c, ri(), ri()); break; }
                            case 4: { String t = rstr(4); osw.write(t, ri(), ri()); break; }
                            case 5: osw.append(rstr(3)).append('k').append("ab\ud800", r(2), 3); break;
                            case 6: osw.flush(); out.append('f'); break;
                            case 7: { if (r(4) == 0) { osw.close(); out.append('c').append(osw.getEncoding()); } else { StringBuilder big = new StringBuilder(); for (int i = r(300); i > 0; i--) big.append(PIECES[r(PIECES.length)]); osw.write(big.toString()); } break; }
                            default: out.append(lo.show()).append('/').append(hex(bo.toByteArray())); break;
                        }
                    } catch (Exception e) {
                        exc(out, e);
                    }
                    out.append(';');
                }
                try {
                    if (r(2) == 0) osw.close();
                } catch (Exception e) {
                    exc(out, e);
                }
                out.append(lo.show()).append('|').append(hex(bo.toByteArray()));
            }
        } catch (Exception e) {
            exc(out, e);
        }
        return out.toString();
    }

    /** The coders on long texts: an encoded text of 400-1100 chars decoded with large reads,
     *  and written in two writes onto a logging stream (the encoder's byte buffer grows from
     *  512 bytes; text cut at a random point, possibly inside a surrogate pair). */
    public static String codecsBig(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        Charset cs = rcs();
        out.append(cs).append(':');
        StringBuilder big = new StringBuilder();
        // (longer texts make the machine run out of memory)
        int want = 400 + r(700);
        while (big.length() < want) big.append(PIECES[r(PIECES.length)]);
        String text = big.toString();
        try {
            byte[] data = text.getBytes(cs);
            if (r(3) == 0 && data.length > 10) data[r(data.length)] = (byte) BYTE_POOL[r(BYTE_POOL.length)];
            out.append(data.length).append(':');
            InputStreamReader isr = new InputStreamReader(new ByteArrayInputStream(data), cs);
            char[] buf = new char[3000 + r(6000)];
            int total = 0;
            for (int k = 0; k < 6; k++) {
                int n = r(3) == 0 ? isr.read() : isr.read(buf, r(3), buf.length - 3);
                out.append(n).append(',');
                if (n > 0 && n < buf.length) out.append(esc(buf, Math.max(0, n - 4) + 0, 3)).append(',');
                if (n > 0) total += n;
            }
            out.append(total).append(';');
            Log lo = new Log(r(4) == 0 ? r(4) : -1);
            OutputStreamWriter osw = new OutputStreamWriter(lo, cs);
            int cut = r(text.length());
            osw.write(text, 0, cut);
            osw.write(text.substring(cut));
            if (r(2) == 0) osw.flush();
            else osw.close();
            out.append(lo.log.toString()).append(':').append(lo.bytes.size()).append(lo.bytes.size() == data.length);
        } catch (Exception e) {
            exc(out, e);
        }
        return out.toString();
    }

    /** DataOutputStream / DataInputStream: big-endian primitives, writeUTF / readUTF (also
     *  malformed input), readLine, EOF, size(). */
    public static String data(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        ByteArrayOutputStream bo = new ByteArrayOutputStream();
        DataOutputStream dos = new DataOutputStream(bo);
        int writes = r(8);
        try {
            for (int k = 0; k < writes; k++) {
                switch (r(12)) {
                    case 0: dos.writeInt(r(2) == 0 ? r(1000) - 500 : s); break;
                    case 1: dos.writeLong((long) s * (r(1000) - 500)); break;
                    case 2: dos.writeShort(r(70000) - 1000); break;
                    case 3: dos.writeChar(r(70000)); break;
                    case 4: dos.writeByte(r(512)); break;
                    case 5: dos.writeBoolean(r(2) == 0); break;
                    case 6: dos.writeFloat((r(2000) - 1000) / 7.0f); break;
                    case 7: dos.writeDouble(r(3) == 0 ? Double.NaN : (r(2000) - 1000) / 3.0); break;
                    case 8: case 9: dos.writeUTF(r(8) == 0 ? null : r(10) == 0 ? "\u0800".repeat(21846 + r(2)) : rstr(4)); break;
                    case 10: dos.writeBytes(rstr(3)); break;
                    default: dos.writeChars(rstr(2)); break;
                }
            }
            dos.flush();
        } catch (Exception e) {
            exc(out, e);
        }
        out.append(dos.size()).append(':');
        byte[] bytes = bo.toByteArray();
        if (r(4) == 0) {
            byte[] junk = rbytes(10);
            byte[] all = new byte[bytes.length + junk.length + 2];
            System.arraycopy(bytes, 0, all, 0, bytes.length);
            all[bytes.length] = 0;
            all[bytes.length + 1] = (byte) r(12);
            System.arraycopy(junk, 0, all, bytes.length + 2, junk.length);
            bytes = all;
        }
        out.append(hex(bytes)).append(':');
        DataInputStream dis = new DataInputStream(r(3) == 0 ? new Trickle(bytes, null) : new ByteArrayInputStream(bytes));
        int reads = 3 + r(10);
        for (int k = 0; k < reads; k++) {
            try {
                switch (r(16)) {
                    case 0: out.append(dis.readInt()); break;
                    case 1: out.append(dis.readLong()); break;
                    case 2: out.append(dis.readShort()).append('/').append(dis.readUnsignedShort()); break;
                    case 3: out.append((int) dis.readChar()); break;
                    case 4: out.append(dis.readByte()).append('/').append(dis.readUnsignedByte()); break;
                    case 5: out.append(dis.readBoolean()); break;
                    case 6: out.append(dis.readFloat()); break;
                    case 7: out.append(dis.readDouble()); break;
                    case 8: case 9: out.append(esc(dis.readUTF())); break;
                    case 10: { byte[] b = new byte[r(5)]; dis.readFully(b); out.append(hex(b)); break; }
                    case 11: { byte[] b = new byte[4]; dis.readFully(b, ri(), ri()); out.append(hex(b)); break; }
                    case 12: out.append(dis.skipBytes(r(5) - 1)); break;
                    case 13: { @SuppressWarnings("deprecation") String l = dis.readLine(); out.append(esc(l)); break; }
                    case 14: { byte[] b = new byte[3]; out.append(dis.read(b)).append(hex(b)); break; }
                    default: out.append(dis.available()); break;
                }
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    static final class Enum2 implements Enumeration<InputStream> {
        final List<InputStream> l;
        int i;

        Enum2(List<InputStream> l) {
            this.l = l;
        }

        public boolean hasMoreElements() {
            return i < l.size();
        }

        public InputStream nextElement() {
            return l.get(i++);
        }
    }

    static final class Upper extends FilterReader {
        Upper(Reader in) {
            super(in);
        }

        public int read() throws IOException {
            int c = super.read();
            return c >= 'a' && c <= 'z' ? c - 32 : c;
        }
    }

    static final class Dup extends FilterWriter {
        Dup(Writer out) {
            super(out);
        }

        public void write(int c) throws IOException {
            super.write(c);
            super.write(c);
        }
    }

    /** PushbackInputStream / PushbackReader / SequenceInputStream / FilterReader / FilterWriter. */
    public static String pushback(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        StringBuilder log = new StringBuilder();
        PushbackInputStream pis;
        PushbackReader prd;
        SequenceInputStream seq;
        try {
            byte[] data = rbytes(8);
            pis = r(2) == 0 ? new PushbackInputStream(new Trickle(data, log)) : new PushbackInputStream(new ByteArrayInputStream(data), r(5) - 1);
            String text = rstr(5);
            Reader base = r(2) == 0 ? new StringReader(text) : new Upper(new StringReader(text));
            prd = r(2) == 0 ? new PushbackReader(base) : new PushbackReader(base, r(5) - 1);
            List<InputStream> parts = new ArrayList<>();
            for (int i = r(4); i > 0; i--) parts.add(r(6) == 0 ? null : r(2) == 0 ? new ByteArrayInputStream(rbytes(3)) : new Trickle(rbytes(4), log));
            seq = parts.size() == 2 && r(2) == 0 ? new SequenceInputStream(parts.get(0), parts.get(1)) : new SequenceInputStream(new Enum2(parts));
        } catch (RuntimeException e) {
            exc(out, e);
            return out.toString() + log.toString();
        }
        StringWriter sw = new StringWriter();
        Writer dup = new Dup(sw);
        int ops = 6 + r(14);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(21)) {
                    case 0: case 1: out.append(pis.read()); break;
                    case 2: pis.unread(r(256)); out.append('u'); break;
                    case 3: { byte[] b = rbytes(3); pis.unread(b, r(2), r(2)); out.append('U'); break; }
                    case 4: { byte[] b = new byte[r(5) + 1]; int n = pis.read(b, r(2), r(b.length)); out.append(n).append(':').append(hex(b)); break; }
                    case 5: out.append(pis.skip(r(5) - 1)).append('/').append(pis.available()); break;
                    case 6: { if (r(3) == 0) pis.close(); else { ByteArrayOutputStream t = new ByteArrayOutputStream(); out.append(pis.transferTo(t)).append(hex(t.toByteArray())); } break; }
                    case 7: case 8: out.append(prd.read()); break;
                    case 9: prd.unread('a' + r(26)); out.append('u'); break;
                    case 10: prd.unread("xyz".toCharArray(), r(2), r(3)); out.append('U'); break;
                    case 11: { char[] b = new char[r(5) + 1]; int n = prd.read(b, r(2), r(b.length)); out.append(n).append(':').append(esc(new String(b))); break; }
                    case 12: out.append(prd.skip(r(5) - 1)).append(prd.ready()); break;
                    case 13: { if (r(3) == 0) prd.close(); else prd.mark(1); break; }
                    case 14: case 15: out.append(seq.read()); break;
                    case 16: { byte[] b = new byte[r(5) + 1]; int n = seq.read(b, r(2), r(b.length)); out.append(n).append(':').append(hex(b)); break; }
                    case 17: out.append(seq.available()); break;
                    case 18: { if (r(2) == 0) seq.close(); else { ByteArrayOutputStream t = new ByteArrayOutputStream(); out.append(seq.transferTo(t)).append(hex(t.toByteArray())); } break; }
                    case 19: dup.write('a' + r(3)); dup.write(rstr(2)); break;
                    default: dup.append("pq", r(2), 2); dup.flush(); break;
                }
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        out.append(esc(sw.toString())).append('|').append(log.toString());
        return out.toString();
    }

    /** Misc: lines() failures, try-with-resources over the closeables, UncheckedIOException. */
    public static String misc(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        StringBuilder log = new StringBuilder();
        byte[] data = rbytes(10);
        try (InputStream in = new Trickle(data, log); Reader rd = new InputStreamReader(in, rcs()); BufferedReader br = new BufferedReader(rd, 1 + r(4))) {
            out.append(br.lines().map(IoOps::esc).collect(Collectors.toList()));
        } catch (UncheckedIOException e) {
            exc(out, e);
        } catch (Exception e) {
            exc(out, e);
        }
        out.append(';').append(log.toString()).append(';');
        Log lo = new Log(r(3) == 0 ? r(5) : -1);
        try (Writer w = new BufferedWriter(new OutputStreamWriter(lo, rcs()), 2 + r(5))) {
            w.write(rstr(5));
            w.append(rstr(3));
            out.append(lo.show()).append('/');
        } catch (Exception e) {
            exc(out, e);
        }
        out.append(lo.show());
        return out.toString();
    }
}

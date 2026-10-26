package org.rocqjvm.jdkmodel;

import java.io.ByteArrayInputStream;
import java.io.Reader;
import java.io.StringReader;
import java.util.Properties;
import java.util.TreeMap;

/** Differential tests of Properties.load (Reader and InputStream): separators, white space,
 *  comments, continuation lines, escapes and their errors, chunked reads. */
public final class PropsOps {
    private PropsOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static final String[] PIECES = {"a", "key", "k\\ey", "x y", "=", ":", " ", "\t", "\f", "\n", "\r", "\r\n", "\\\n", "\\\r\n   ",
        "#c", "!c", "\\u0041", "\\u00e9", "\\uzz12", "\\u12", "\\t", "\\n", "\\\\", "\\=", "\\:", "\\ ", "é", "€", "v1", "=v=", "  ", "\\"};

    static String text() {
        StringBuilder b = new StringBuilder();
        for (int i = r(25); i > 0; i--) b.append(PIECES[r(PIECES.length)]);
        return b.toString();
    }

    /** A Reader that returns short chunks, so the JDK's refill paths run. */
    static final class Chunky extends Reader {
        final String t;
        int pos;
        final int max;
        final StringBuilder log;

        Chunky(String t, int max, StringBuilder log) {
            this.t = t;
            this.max = max;
            this.log = log;
        }

        public int read(char[] buf, int off, int len) {
            log.append('r').append(len);
            if (pos >= t.length()) return -1;
            int n = Math.min(Math.min(len, max), t.length() - pos);
            t.getChars(pos, pos + n, buf, off);
            pos += n;
            return n;
        }

        public void close() {
        }
    }

    public static String load(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 5; k++) {
            String t = text();
            Properties p = new Properties();
            StringBuilder log = new StringBuilder();
            try {
                switch (r(4)) {
                    case 0: p.load(new StringReader(t)); break;
                    case 1: p.load(new Chunky(t, 1 + r(5), log)); break;
                    case 2: { byte[] bs = new byte[t.length()]; for (int i = 0; i < bs.length; i++) bs[i] = (byte) t.charAt(i); p.load(new ByteArrayInputStream(bs)); break; }
                    default: p.load(r(2) == 0 ? (Reader) null : new StringReader(t)); break;
                }
                out.append(new TreeMap<>(p)).append(p.size());
            } catch (Exception x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(log).append(';');
        }
        try {
            new Properties().load((java.io.InputStream) null);
        } catch (Exception x) {
            out.append(x.getMessage());
        }
        return out.toString();
    }
}

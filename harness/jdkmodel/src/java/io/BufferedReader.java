/*
 * rocq-jvm model of java.io.BufferedReader (clean-room, Apache-2.0), JDK 21 behaviour: an
 * 8192-char buffer (or the given size) refilled with one read of the wrapped reader (repeated
 * while it returns 0); mark with a read-ahead limit (a limit above the buffer size reallocates
 * the buffer; reading past the limit invalidates the mark: "Mark invalid"); readLine ends a line
 * at '\n', '\r' or "\r\n" (a '\r' at the end of a buffer skips a following '\n' in the next
 * read, readLine, skip or ready); read(char[], ..) reads directly from the wrapped reader when
 * its request is at least the buffer size and nothing is buffered or marked, and keeps reading
 * while the wrapped reader is ready(); lines() is a lazy ordered stream of unknown size over
 * readLine (IOException wrapped in UncheckedIOException).
 * Not modelled (STUCK): read(CharBuffer).
 */
package java.io;

import java.util.Iterator;
import java.util.NoSuchElementException;
import java.util.stream.Stream;

public class BufferedReader extends Reader {
    private static final int INVALIDATED = -2;
    private static final int UNMARKED = -1;

    private Reader in;
    private char[] cb;
    private int nChars, nextChar;
    private int markedChar = UNMARKED;
    private int readAheadLimit = 0;
    private boolean skipLF = false;
    private boolean markedSkipLF = false;

    public BufferedReader(Reader in, int sz) {
        super(in);
        if (sz <= 0) throw new IllegalArgumentException("Buffer size <= 0");
        this.in = in;
        cb = new char[sz];
        nextChar = nChars = 0;
    }

    public BufferedReader(Reader in) {
        this(in, 8192);
    }

    private void checkOpen() throws IOException {
        if (in == null) throw new IOException("Stream closed");
    }

    /** Refill the buffer, keeping the marked chars (if the mark is still valid). */
    private void fill() throws IOException {
        int dst = 0;
        if (markedChar > UNMARKED) {
            int kept = nextChar - markedChar;
            if (kept >= readAheadLimit) {
                markedChar = INVALIDATED;
                readAheadLimit = 0;
            } else {
                if (readAheadLimit <= cb.length) {
                    System.arraycopy(cb, markedChar, cb, 0, kept);
                } else {
                    char[] bigger = new char[readAheadLimit];
                    System.arraycopy(cb, markedChar, bigger, 0, kept);
                    cb = bigger;
                }
                markedChar = 0;
                dst = kept;
                nextChar = nChars = kept;
            }
        }
        int n;
        do {
            n = in.read(cb, dst, cb.length - dst);
        } while (n == 0);
        if (n > 0) {
            nChars = dst + n;
            nextChar = dst;
        }
    }

    public int read() throws IOException {
        synchronized (lock) {
            checkOpen();
            for (;;) {
                if (nextChar >= nChars) {
                    fill();
                    if (nextChar >= nChars) return -1;
                }
                if (skipLF) {
                    skipLF = false;
                    if (cb[nextChar] == '\n') {
                        nextChar++;
                        continue;
                    }
                }
                return cb[nextChar++];
            }
        }
    }

    private int readSome(char[] cbuf, int off, int len) throws IOException {
        if (nextChar >= nChars) {
            if (len >= cb.length && markedChar <= UNMARKED && !skipLF) return in.read(cbuf, off, len);
            fill();
        }
        if (nextChar >= nChars) return -1;
        if (skipLF) {
            skipLF = false;
            if (cb[nextChar] == '\n') {
                nextChar++;
                if (nextChar >= nChars) fill();
                if (nextChar >= nChars) return -1;
            }
        }
        int n = Math.min(len, nChars - nextChar);
        System.arraycopy(cb, nextChar, cbuf, off, n);
        nextChar += n;
        return n;
    }

    public int read(char[] cbuf, int off, int len) throws IOException {
        synchronized (lock) {
            checkOpen();
            if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
            ModelIo.checkFromIndexSize(off, len, cbuf.length);
            if (len == 0) return 0;
            int n = readSome(cbuf, off, len);
            if (n <= 0) return n;
            while (n < len && in.ready()) {
                int k = readSome(cbuf, off + n, len - n);
                if (k <= 0) break;
                n += k;
            }
            return n;
        }
    }

    public int read(java.nio.CharBuffer target) throws IOException {
        throw ModelIo.unsupported("BufferedReader.read(CharBuffer)");
    }

    public String readLine() throws IOException {
        synchronized (lock) {
            StringBuilder acc = null;
            checkOpen();
            boolean omitLF = skipLF;
            for (;;) {
                if (nextChar >= nChars) fill();
                if (nextChar >= nChars) {
                    if (acc != null && acc.length() > 0) return acc.toString();
                    return null;
                }
                if (omitLF && cb[nextChar] == '\n') nextChar++;
                skipLF = false;
                omitLF = false;
                int i = nextChar;
                char c = 0;
                boolean eol = false;
                while (i < nChars) {
                    c = cb[i];
                    if (c == '\n' || c == '\r') {
                        eol = true;
                        break;
                    }
                    i++;
                }
                int start = nextChar;
                nextChar = i;
                if (eol) {
                    String line;
                    if (acc == null) {
                        line = new String(cb, start, i - start);
                    } else {
                        for (int k = start; k < i; k++) acc.append(cb[k]);
                        line = acc.toString();
                    }
                    nextChar++;
                    if (c == '\r') skipLF = true;
                    return line;
                }
                if (acc == null) acc = new StringBuilder(80);
                for (int k = start; k < i; k++) acc.append(cb[k]);
            }
        }
    }

    public long skip(long n) throws IOException {
        if (n < 0L) throw new IllegalArgumentException("skip value is negative");
        synchronized (lock) {
            checkOpen();
            long left = n;
            while (left > 0) {
                if (nextChar >= nChars) fill();
                if (nextChar >= nChars) break;
                if (skipLF) {
                    skipLF = false;
                    if (cb[nextChar] == '\n') nextChar++;
                }
                long have = nChars - nextChar;
                if (left <= have) {
                    nextChar += (int) left;
                    left = 0;
                    break;
                }
                left -= have;
                nextChar = nChars;
            }
            return n - left;
        }
    }

    public boolean ready() throws IOException {
        synchronized (lock) {
            checkOpen();
            if (skipLF) {
                if (nextChar >= nChars && in.ready()) fill();
                if (nextChar < nChars) {
                    if (cb[nextChar] == '\n') nextChar++;
                    skipLF = false;
                }
            }
            return nextChar < nChars || in.ready();
        }
    }

    public boolean markSupported() {
        return true;
    }

    public void mark(int readAheadLimit) throws IOException {
        if (readAheadLimit < 0) throw new IllegalArgumentException("Read-ahead limit < 0");
        synchronized (lock) {
            checkOpen();
            this.readAheadLimit = readAheadLimit;
            markedChar = nextChar;
            markedSkipLF = skipLF;
        }
    }

    public void reset() throws IOException {
        synchronized (lock) {
            checkOpen();
            if (markedChar < 0) throw new IOException(markedChar == INVALIDATED ? "Mark invalid" : "Stream not marked");
            nextChar = markedChar;
            skipLF = markedSkipLF;
        }
    }

    public void close() throws IOException {
        synchronized (lock) {
            if (in == null) return;
            try {
                in.close();
            } finally {
                in = null;
                cb = null;
            }
        }
    }

    public Stream<String> lines() {
        Iterator<String> it = new Iterator<String>() {
            String pending = null;

            public boolean hasNext() {
                if (pending != null) return true;
                try {
                    pending = readLine();
                    return pending != null;
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            }

            public String next() {
                if (pending != null || hasNext()) {
                    String line = pending;
                    pending = null;
                    return line;
                }
                throw new NoSuchElementException();
            }
        };
        return java.util.stream.ModelIterStreams.orderedUnknownSize(it);
    }
}

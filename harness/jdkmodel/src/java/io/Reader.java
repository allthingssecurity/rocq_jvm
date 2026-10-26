/*
 * rocq-jvm model of java.io.Reader (clean-room, Apache-2.0): the JDK 21 lock rules (the
 * Reader(Reader) constructor locks on the wrapped reader; JDK 21's InternalLock for a
 * BufferedReader over an InputStreamReader is not observable on one thread), read() and
 * read(char[]) through read(char[], int, int), skip with an 8192-char buffer, transferTo with
 * 8192-char chunks, mark/reset unsupported, nullReader(), and the JDK's messages.
 * Not modelled (STUCK): read(CharBuffer) (no java.nio buffers).
 */
package java.io;

public abstract class Reader implements Readable, Closeable {
    private static final int TRANSFER_CHUNK = 8192;
    private static final int SKIP_MAX = 8192;

    public static Reader nullReader() {
        return new NullReader();
    }

    private static final class NullReader extends Reader {
        private volatile boolean closed;

        private void checkOpen() throws IOException {
            if (closed) throw new IOException("Stream closed");
        }

        public int read() throws IOException {
            checkOpen();
            return -1;
        }

        public int read(char[] cbuf, int off, int len) throws IOException {
            if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
            ModelIo.checkFromIndexSize(off, len, cbuf.length);
            checkOpen();
            return len == 0 ? 0 : -1;
        }

        public int read(java.nio.CharBuffer target) throws IOException {
            throw ModelIo.unsupported("Reader.read(CharBuffer)");
        }

        public boolean ready() throws IOException {
            checkOpen();
            return false;
        }

        public long skip(long n) throws IOException {
            checkOpen();
            return 0L;
        }

        public long transferTo(Writer out) throws IOException {
            if (out == null) throw new NullPointerException();
            checkOpen();
            return 0L;
        }

        public void close() {
            closed = true;
        }
    }

    protected Object lock;

    protected Reader() {
        this.lock = this;
    }

    protected Reader(Object lock) {
        if (lock == null) throw new NullPointerException();
        this.lock = lock;
    }

    /** The JDK's package-private Reader(Reader): in.getClass() is the null check. */
    Reader(Reader in) {
        if (in == null) throw ModelIo.invokeOnNull("Object.getClass()", "in");
        this.lock = in;
    }

    public int read(java.nio.CharBuffer target) throws IOException {
        throw ModelIo.unsupported("Reader.read(CharBuffer)");
    }

    public int read() throws IOException {
        char[] one = new char[1];
        if (read(one, 0, 1) == -1) return -1;
        return one[0];
    }

    public int read(char[] cbuf) throws IOException {
        if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
        return read(cbuf, 0, cbuf.length);
    }

    public abstract int read(char[] cbuf, int off, int len) throws IOException;

    private char[] skipBuf;

    public long skip(long n) throws IOException {
        if (n < 0L) throw new IllegalArgumentException("skip value is negative");
        synchronized (lock) {
            int size = (int) Math.min(n, SKIP_MAX);
            if (skipBuf == null || skipBuf.length < size) skipBuf = new char[size];
            long left = n;
            while (left > 0) {
                int k = read(skipBuf, 0, (int) Math.min(left, size));
                if (k == -1) break;
                left -= k;
            }
            return n - left;
        }
    }

    public boolean ready() throws IOException {
        return false;
    }

    public boolean markSupported() {
        return false;
    }

    public void mark(int readAheadLimit) throws IOException {
        throw new IOException("mark() not supported");
    }

    public void reset() throws IOException {
        throw new IOException("reset() not supported");
    }

    public abstract void close() throws IOException;

    public long transferTo(Writer out) throws IOException {
        if (out == null) throw new NullPointerException("out");
        long moved = 0;
        char[] chunk = new char[TRANSFER_CHUNK];
        int k;
        while ((k = read(chunk, 0, TRANSFER_CHUNK)) >= 0) {
            out.write(chunk, 0, k);
            if (moved < Long.MAX_VALUE) {
                long t = moved + k;
                moved = t < moved ? Long.MAX_VALUE : t;
            }
        }
        return moved;
    }
}

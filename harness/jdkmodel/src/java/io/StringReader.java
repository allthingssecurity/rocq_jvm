/*
 * rocq-jvm model of java.io.StringReader (clean-room, Apache-2.0): JDK 21 behaviour (skip may
 * go backwards to the start of the string, mark ignores the read-ahead limit, close drops the
 * string).
 */
package java.io;

public class StringReader extends Reader {
    private final int length;
    private String str;
    private int next = 0;
    private int mark = 0;

    public StringReader(String s) {
        if (s == null) throw ModelIo.invokeOnNull("String.length()", "s");
        this.length = s.length();
        this.str = s;
    }

    private void checkOpen() throws IOException {
        if (str == null) throw new IOException("Stream closed");
    }

    public int read() throws IOException {
        synchronized (lock) {
            checkOpen();
            if (next >= length) return -1;
            return str.charAt(next++);
        }
    }

    public int read(char[] cbuf, int off, int len) throws IOException {
        synchronized (lock) {
            checkOpen();
            if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
            ModelIo.checkFromIndexSize(off, len, cbuf.length);
            if (len == 0) return 0;
            if (next >= length) return -1;
            int n = Math.min(length - next, len);
            for (int i = 0; i < n; i++) cbuf[off + i] = str.charAt(next + i);
            next += n;
            return n;
        }
    }

    public long skip(long n) throws IOException {
        synchronized (lock) {
            checkOpen();
            if (next >= length) return 0;
            long r = Math.min(length - next, n);
            r = Math.max(-next, r);
            next += (int) r;
            return r;
        }
    }

    public boolean ready() throws IOException {
        synchronized (lock) {
            checkOpen();
            return true;
        }
    }

    public boolean markSupported() {
        return true;
    }

    public void mark(int readAheadLimit) throws IOException {
        if (readAheadLimit < 0) throw new IllegalArgumentException("Read-ahead limit < 0");
        synchronized (lock) {
            checkOpen();
            mark = next;
        }
    }

    public void reset() throws IOException {
        synchronized (lock) {
            checkOpen();
            next = mark;
        }
    }

    public void close() {
        synchronized (lock) {
            str = null;
        }
    }
}

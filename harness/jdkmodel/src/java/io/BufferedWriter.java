/*
 * rocq-jvm model of java.io.BufferedWriter (clean-room, Apache-2.0), JDK 21 behaviour: the buffer
 * is 8192 chars (the JDK starts at 512 and grows to 8192 only on a virtual thread, which the
 * model does not have) or the given size; the buffer is written out whenever it is full; a
 * char[] write of at least the buffer size goes directly to the wrapped writer after the buffer;
 * newLine writes the line separator "\n"; close flushes the buffer and closes the wrapped writer
 * (also when the flush fails, as try-with-resources).
 */
package java.io;

public class BufferedWriter extends Writer {
    private Writer out;
    private char[] cb;
    private int nChars;
    private int nextChar;
    private final int maxChars;

    private BufferedWriter(Writer out, int initialSize, int maxSize) {
        super(out);
        if (initialSize <= 0) throw new IllegalArgumentException("Buffer size <= 0");
        this.out = out;
        this.cb = new char[initialSize];
        this.nChars = initialSize;
        this.maxChars = maxSize;
    }

    public BufferedWriter(Writer out) {
        this(out, 8192, 8192);
    }

    public BufferedWriter(Writer out, int sz) {
        this(out, sz, sz);
    }

    private void checkOpen() throws IOException {
        if (out == null) throw new IOException("Stream closed");
    }

    private void growIfNeeded(int len) {
        int need = nextChar + len + 1;
        if (need < 0) need = Integer.MAX_VALUE;
        if (need > nChars && nChars < maxChars) {
            int size = Math.min(need, maxChars);
            char[] b = new char[size];
            System.arraycopy(cb, 0, b, 0, Math.min(cb.length, size));
            cb = b;
            nChars = size;
        }
    }

    /** Package-private in the JDK too (PrintStream calls it). */
    void flushBuffer() throws IOException {
        synchronized (lock) {
            checkOpen();
            if (nextChar == 0) return;
            out.write(cb, 0, nextChar);
            nextChar = 0;
        }
    }

    public void write(int c) throws IOException {
        synchronized (lock) {
            checkOpen();
            growIfNeeded(1);
            if (nextChar >= nChars) flushBuffer();
            cb[nextChar++] = (char) c;
        }
    }

    public void write(char[] cbuf, int off, int len) throws IOException {
        synchronized (lock) {
            checkOpen();
            if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
            ModelIo.checkFromIndexSize(off, len, cbuf.length);
            if (len == 0) return;
            if (len >= maxChars) {
                flushBuffer();
                out.write(cbuf, off, len);
                return;
            }
            growIfNeeded(len);
            int b = off, t = off + len;
            while (b < t) {
                int d = Math.min(nChars - nextChar, t - b);
                System.arraycopy(cbuf, b, cb, nextChar, d);
                b += d;
                nextChar += d;
                if (nextChar >= nChars) flushBuffer();
            }
        }
    }

    public void write(String s, int off, int len) throws IOException {
        synchronized (lock) {
            checkOpen();
            growIfNeeded(len);
            int b = off, t = off + len;
            while (b < t) {
                int d = Math.min(nChars - nextChar, t - b);
                if (s == null) throw ModelIo.invokeOnNull("String.getChars(int, int, char[], int)", "s");
                ModelIo.getChars(s, b, b + d, cb, nextChar);
                b += d;
                nextChar += d;
                if (nextChar >= nChars) flushBuffer();
            }
        }
    }

    /** rocq-jvm helper (PrintWriter.format): n more chars fit without writing the buffer out
     *  (or this writer is closed, so that every write fails alike). */
    boolean holds$(int n) {
        return out == null || nextChar + n < nChars;
    }

    /** rocq-jvm helper (PrintWriter.format): the wrapped writer is a StringWriter or a
     *  CharArrayWriter (exact class), which never fails and does not see call boundaries. */
    boolean intoTextSink$() {
        Writer o = out;
        return o != null && (o.getClass() == StringWriter.class || o.getClass() == CharArrayWriter.class);
    }

    public void newLine() throws IOException {
        write(ModelIo.LINE_SEPARATOR);
    }

    public void flush() throws IOException {
        synchronized (lock) {
            flushBuffer();
            out.flush();
        }
    }

    public void close() throws IOException {
        synchronized (lock) {
            if (out == null) return;
            Writer w = out;
            Throwable primary = null;
            try {
                flushBuffer();
                out = null;
                cb = null;
            } catch (Throwable x) {
                primary = x;
                throw x;
            } finally {
                if (primary == null) {
                    w.close();
                } else {
                    try {
                        w.close();
                    } catch (Throwable y) {
                        primary.addSuppressed(y);
                    }
                }
            }
        }
    }
}

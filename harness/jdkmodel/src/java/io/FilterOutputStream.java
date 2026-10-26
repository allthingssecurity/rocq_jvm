/*
 * rocq-jvm model of java.io.FilterOutputStream (clean-room, Apache-2.0): JDK 21 behaviour
 * (write(byte[], ..) byte by byte through write(int) after the index check; close once: flush,
 * then close the wrapped stream also when the flush failed, the close exception carrying the
 * flush exception as suppressed).
 */
package java.io;

public class FilterOutputStream extends OutputStream {
    protected OutputStream out;
    private volatile boolean closed;
    private final Object closeLock = new Object();

    public FilterOutputStream(OutputStream out) {
        this.out = out;
    }

    final OutputStream outOrNpe(String method) {
        OutputStream o = out;
        if (o == null) throw ModelIo.invokeOnNull("java.io.OutputStream." + method, "this.out");
        return o;
    }

    public void write(int b) throws IOException {
        outOrNpe("write(int)").write(b);
    }

    public void write(byte[] b) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        write(b, 0, b.length);
    }

    public void write(byte[] b, int off, int len) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        ModelIo.checkFromIndexSize(off, len, b.length);
        for (int i = 0; i < len; i++) write(b[off + i]);
    }

    public void flush() throws IOException {
        outOrNpe("flush()").flush();
    }

    public void close() throws IOException {
        if (closed) return;
        synchronized (closeLock) {
            if (closed) return;
            closed = true;
        }
        Throwable flushFailure = null;
        try {
            flush();
        } catch (Throwable e) {
            flushFailure = e;
            throw e;
        } finally {
            if (flushFailure == null) {
                outOrNpe("close()").close();
            } else {
                try {
                    outOrNpe("close()").close();
                } catch (Throwable closeFailure) {
                    if (flushFailure != closeFailure) closeFailure.addSuppressed(flushFailure);
                    throw closeFailure;
                }
            }
        }
    }
}

/*
 * rocq-jvm model of java.io.OutputStream (clean-room, Apache-2.0): write(byte[]) and
 * write(byte[], int, int) byte by byte through write(int) after the JDK 21 index check, empty
 * flush/close, and nullOutputStream().
 */
package java.io;

public abstract class OutputStream implements Closeable, Flushable {
    public OutputStream() {
    }

    public static OutputStream nullOutputStream() {
        return new NullOutput();
    }

    private static final class NullOutput extends OutputStream {
        private volatile boolean closed;

        public void write(int b) throws IOException {
            if (closed) throw new IOException("Stream closed");
        }

        public void write(byte[] b, int off, int len) throws IOException {
            if (b == null) throw ModelIo.arrayLengthOfNull("b");
            ModelIo.checkFromIndexSize(off, len, b.length);
            if (closed) throw new IOException("Stream closed");
        }

        public void close() {
            closed = true;
        }
    }

    public abstract void write(int b) throws IOException;

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
    }

    public void close() throws IOException {
    }
}

/*
 * rocq-jvm model of java.io.BufferedOutputStream (clean-room, Apache-2.0), JDK 21 behaviour: an
 * 8192-byte buffer (the JDK starts at 512 only on a virtual thread, which the model does not
 * have) or the given size; a write that does not fit flushes the buffer first; a write of at
 * least the buffer size goes directly to the wrapped stream; write(byte[], ..) has no index
 * check of its own (System.arraycopy's or the wrapped stream's errors).
 */
package java.io;

public class BufferedOutputStream extends FilterOutputStream {
    protected byte[] buf;
    protected int count;
    private final int maxBufSize;

    private BufferedOutputStream(OutputStream out, int initialSize, int maxSize) {
        super(out);
        if (initialSize <= 0) throw new IllegalArgumentException("Buffer size <= 0");
        this.buf = new byte[getClass() == BufferedOutputStream.class ? initialSize : maxSize];
        this.maxBufSize = maxSize;
    }

    public BufferedOutputStream(OutputStream out) {
        this(out, 8192, 8192);
    }

    public BufferedOutputStream(OutputStream out, int size) {
        this(out, size, size);
    }

    private void flushBuffer() throws IOException {
        if (count > 0) {
            outOrNpe("write(byte[], int, int)").write(buf, 0, count);
            count = 0;
        }
    }

    private void growIfNeeded(int len) {
        int need = count + len + 1;
        if (need < 0) need = Integer.MAX_VALUE;
        int size = buf.length;
        if (need > size && size < maxBufSize) {
            int ns = Math.min(need, maxBufSize);
            byte[] b = new byte[ns];
            System.arraycopy(buf, 0, b, 0, Math.min(size, ns));
            buf = b;
        }
    }

    public synchronized void write(int b) throws IOException {
        growIfNeeded(1);
        if (count >= buf.length) flushBuffer();
        buf[count++] = (byte) b;
    }

    public synchronized void write(byte[] b, int off, int len) throws IOException {
        if (len >= maxBufSize) {
            flushBuffer();
            outOrNpe("write(byte[], int, int)").write(b, off, len);
            return;
        }
        growIfNeeded(len);
        if (len > buf.length - count) flushBuffer();
        System.arraycopy(b, off, buf, count, len);
        count += len;
    }

    public synchronized void flush() throws IOException {
        flushBuffer();
        outOrNpe("flush()").flush();
    }
}

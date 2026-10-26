/*
 * rocq-jvm model of java.io.ByteArrayInputStream (clean-room, Apache-2.0): JDK 21 behaviour
 * (the constructors do not check offset/length: a negative offset fails at the first read with
 * the machine's array index error, as in the JDK; readAllBytes / transferTo in chunks of
 * 128 KiB; mark ignores the read-ahead limit).
 */
package java.io;

public class ByteArrayInputStream extends InputStream {
    private static final int TRANSFER_CHUNK = 128 * 1024;

    protected byte[] buf;
    protected int pos;
    protected int mark = 0;
    protected int count;

    public ByteArrayInputStream(byte[] buf) {
        if (buf == null) throw ModelIo.arrayLengthOfNull("buf");
        this.buf = buf;
        this.pos = 0;
        this.count = buf.length;
    }

    public ByteArrayInputStream(byte[] buf, int offset, int length) {
        this.buf = buf;
        this.pos = offset;
        if (buf == null) throw ModelIo.arrayLengthOfNull("buf");
        this.count = Math.min(offset + length, buf.length);
        this.mark = offset;
    }

    public synchronized int read() {
        if (pos < count) return buf[pos++] & 0xff;
        return -1;
    }

    public synchronized int read(byte[] b, int off, int len) {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        ModelIo.checkFromIndexSize(off, len, b.length);
        if (pos >= count) return -1;
        int n = Math.min(len, count - pos);
        if (n <= 0) return 0;
        System.arraycopy(buf, pos, b, off, n);
        pos += n;
        return n;
    }

    public synchronized byte[] readAllBytes() {
        // Arrays.copyOfRange(buf, pos, count)
        int from = pos, to = count;
        if (from > to) throw new IllegalArgumentException(from + " > " + to);
        byte[] r = new byte[to - from];
        System.arraycopy(buf, from, r, 0, Math.min(buf.length - from, to - from));
        pos = count;
        return r;
    }

    public int readNBytes(byte[] b, int off, int len) {
        int n = read(b, off, len);
        return n == -1 ? 0 : n;
    }

    public synchronized long transferTo(OutputStream out) throws IOException {
        int len = count - pos;
        if (len > 0) {
            if (out == null) throw ModelIo.invokeOnNull("java.io.OutputStream.write(byte[], int, int)", "out");
            int done = 0;
            while (done < len) {
                int k = Math.min(len - done, TRANSFER_CHUNK);
                out.write(buf, pos, k);
                pos += k;
                done += k;
            }
        }
        return len;
    }

    public synchronized long skip(long n) {
        long k = count - pos;
        if (n < k) k = n < 0 ? 0 : n;
        pos += (int) k;
        return k;
    }

    public synchronized int available() {
        return count - pos;
    }

    public boolean markSupported() {
        return true;
    }

    public void mark(int readAheadLimit) {
        mark = pos;
    }

    public synchronized void reset() {
        pos = mark;
    }

    public void close() throws IOException {
    }
}

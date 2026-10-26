/*
 * rocq-jvm model of java.io.BufferedInputStream (clean-room, Apache-2.0), JDK 21 behaviour: an
 * 8192-byte buffer (or the given size; allocated lazily for the class itself, at construction
 * for subclasses) refilled with one read of the wrapped stream; mark keeps up to marklimit bytes
 * (growing the buffer by doubling up to marklimit); read(byte[], ..) reads directly from the
 * wrapped stream for requests of at least the buffer size when nothing is buffered or marked,
 * and keeps reading while the wrapped stream has bytes available(); transferTo writes the
 * buffered bytes and then delegates (for the class itself, without a mark).
 */
package java.io;

public class BufferedInputStream extends FilterInputStream {
    private static final byte[] EMPTY = new byte[0];

    private final int initialSize;
    protected volatile byte[] buf;
    protected int count;
    protected int pos;
    protected int markpos = -1;
    protected int marklimit;

    private InputStream inIfOpen() throws IOException {
        InputStream i = in;
        if (i == null) throw new IOException("Stream closed");
        return i;
    }

    private byte[] bufIfOpen(boolean allocate) throws IOException {
        byte[] b = buf;
        if (allocate && b == EMPTY) {
            b = new byte[initialSize];
            buf = b;
        }
        if (b == null) throw new IOException("Stream closed");
        return b;
    }

    private void checkOpen() throws IOException {
        if (buf == null) throw new IOException("Stream closed");
    }

    public BufferedInputStream(InputStream in) {
        this(in, 8192);
    }

    public BufferedInputStream(InputStream in, int size) {
        super(in);
        if (size <= 0) throw new IllegalArgumentException("Buffer size <= 0");
        initialSize = size;
        buf = getClass() == BufferedInputStream.class ? EMPTY : new byte[size];
    }

    private void fill() throws IOException {
        byte[] b = bufIfOpen(true);
        if (markpos == -1) {
            pos = 0;
        } else if (pos >= b.length) {
            if (markpos > 0) {
                int keep = pos - markpos;
                System.arraycopy(b, markpos, b, 0, keep);
                pos = keep;
                markpos = 0;
            } else if (b.length >= marklimit) {
                markpos = -1;
                pos = 0;
            } else {
                int nsz = pos + Math.max(1, pos);
                if (nsz < 0 || nsz > Integer.MAX_VALUE - 8) throw ModelIo.unsupported("BufferedInputStream: huge mark limit");
                if (nsz > marklimit) nsz = marklimit;
                byte[] nb = new byte[nsz];
                System.arraycopy(b, 0, nb, 0, pos);
                if (buf != b) throw new IOException("Stream closed");
                buf = nb;
                b = nb;
            }
        }
        count = pos;
        int n = inIfOpen().read(b, pos, b.length - pos);
        if (n > 0) count = n + pos;
    }

    public synchronized int read() throws IOException {
        if (pos >= count) {
            fill();
            if (pos >= count) return -1;
        }
        return bufIfOpen(true)[pos++] & 0xff;
    }

    private int readSome(byte[] b, int off, int len) throws IOException {
        int avail = count - pos;
        if (avail <= 0) {
            int size = Math.max(bufIfOpen(false).length, initialSize);
            if (len >= size && markpos == -1) return inIfOpen().read(b, off, len);
            fill();
            avail = count - pos;
            if (avail <= 0) return -1;
        }
        int cnt = Math.min(avail, len);
        System.arraycopy(bufIfOpen(true), pos, b, off, cnt);
        pos += cnt;
        return cnt;
    }

    public synchronized int read(byte[] b, int off, int len) throws IOException {
        checkOpen();
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        if ((off | len | (off + len) | (b.length - (off + len))) < 0) throw new IndexOutOfBoundsException();
        if (len == 0) return 0;
        int n = 0;
        for (;;) {
            int k = readSome(b, off + n, len - n);
            if (k <= 0) return n == 0 ? k : n;
            n += k;
            if (n >= len) return n;
            InputStream i = in;
            if (i != null && i.available() <= 0) return n;
        }
    }

    public synchronized long skip(long n) throws IOException {
        checkOpen();
        if (n <= 0) return 0;
        long avail = count - pos;
        if (avail <= 0) {
            if (markpos == -1) return inIfOpen().skip(n);
            fill();
            avail = count - pos;
            if (avail <= 0) return 0;
        }
        long k = Math.min(avail, n);
        pos += (int) k;
        return k;
    }

    public synchronized int available() throws IOException {
        int n = count - pos;
        int avail = inIfOpen().available();
        return n > Integer.MAX_VALUE - avail ? Integer.MAX_VALUE : n + avail;
    }

    public synchronized void mark(int readlimit) {
        marklimit = readlimit;
        markpos = pos;
    }

    public synchronized void reset() throws IOException {
        checkOpen();
        if (markpos < 0) throw new IOException("Resetting to invalid mark");
        pos = markpos;
    }

    public boolean markSupported() {
        return true;
    }

    public void close() throws IOException {
        if (buf == null) return;
        buf = null;
        InputStream i = in;
        in = null;
        if (i != null) i.close();
    }

    public synchronized long transferTo(OutputStream out) throws IOException {
        if (out == null) throw new NullPointerException("out");
        if (getClass() == BufferedInputStream.class && markpos == -1) {
            int avail = count - pos;
            if (avail > 0) {
                byte[] b = bufIfOpen(true);
                byte[] rest = new byte[avail];
                System.arraycopy(b, pos, rest, 0, avail);
                out.write(rest);
                pos = count;
            }
            long more = inIfOpen().transferTo(out);
            long t = avail + more;
            if (((avail ^ t) & (more ^ t)) < 0) return Long.MAX_VALUE;
            return t;
        }
        return super.transferTo(out);
    }
}

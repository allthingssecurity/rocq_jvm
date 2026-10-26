/*
 * rocq-jvm model of java.io.PushbackInputStream (clean-room, Apache-2.0), JDK 21 behaviour and
 * messages: pushed-back bytes are read first (the last one pushed back comes first), then the
 * wrapped stream; mark/reset unsupported; transferTo writes the pushed-back bytes and then
 * delegates (for the class itself).
 */
package java.io;

public class PushbackInputStream extends FilterInputStream {
    protected byte[] buf;
    protected int pos;

    private void checkOpen() throws IOException {
        if (in == null) throw new IOException("Stream closed");
    }

    public PushbackInputStream(InputStream in, int size) {
        super(in);
        if (size <= 0) throw new IllegalArgumentException("size <= 0");
        this.buf = new byte[size];
        this.pos = size;
    }

    public PushbackInputStream(InputStream in) {
        this(in, 1);
    }

    public int read() throws IOException {
        checkOpen();
        if (pos < buf.length) return buf[pos++] & 0xff;
        return super.read();
    }

    public int read(byte[] b, int off, int len) throws IOException {
        checkOpen();
        if (b == null) throw new NullPointerException();
        ModelIo.checkFromIndexSize(off, len, b.length);
        if (len == 0) return 0;
        int avail = buf.length - pos;
        if (avail > 0) {
            if (len < avail) avail = len;
            System.arraycopy(buf, pos, b, off, avail);
            pos += avail;
            off += avail;
            len -= avail;
        }
        if (len > 0) {
            len = super.read(b, off, len);
            if (len == -1) return avail == 0 ? -1 : avail;
            return avail + len;
        }
        return avail;
    }

    public void unread(int b) throws IOException {
        checkOpen();
        if (pos == 0) throw new IOException("Push back buffer is full");
        buf[--pos] = (byte) b;
    }

    public void unread(byte[] b, int off, int len) throws IOException {
        checkOpen();
        if (len > pos) throw new IOException("Push back buffer is full");
        pos -= len;
        System.arraycopy(b, off, buf, pos, len);
    }

    public void unread(byte[] b) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        unread(b, 0, b.length);
    }

    public int available() throws IOException {
        checkOpen();
        int n = buf.length - pos;
        int avail = super.available();
        return n > Integer.MAX_VALUE - avail ? Integer.MAX_VALUE : n + avail;
    }

    public long skip(long n) throws IOException {
        checkOpen();
        if (n <= 0) return 0;
        long pskip = buf.length - pos;
        if (pskip > 0) {
            if (n < pskip) pskip = n;
            pos += (int) pskip;
            n -= pskip;
        }
        if (n > 0) pskip += super.skip(n);
        return pskip;
    }

    public boolean markSupported() {
        return false;
    }

    public void mark(int readlimit) {
    }

    public void reset() throws IOException {
        throw new IOException("mark/reset not supported");
    }

    public synchronized void close() throws IOException {
        if (in != null) {
            in.close();
            in = null;
            buf = null;
        }
    }

    public long transferTo(OutputStream out) throws IOException {
        if (out == null) throw new NullPointerException("out");
        checkOpen();
        if (getClass() == PushbackInputStream.class) {
            int avail = buf.length - pos;
            if (avail > 0) {
                byte[] rest = new byte[avail];
                System.arraycopy(buf, pos, rest, 0, avail);
                out.write(rest);
                pos = rest.length;
            }
            long more = in.transferTo(out);
            long t = avail + more;
            if (((avail ^ t) & (more ^ t)) < 0) return Long.MAX_VALUE;
            return t;
        }
        return super.transferTo(out);
    }
}

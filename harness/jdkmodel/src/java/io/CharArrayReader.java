/*
 * rocq-jvm model of java.io.CharArrayReader (clean-room, Apache-2.0): JDK 21 behaviour and
 * messages. Not modelled (STUCK): read(CharBuffer).
 */
package java.io;

public class CharArrayReader extends Reader {
    protected char[] buf;
    protected int pos;
    protected int markedPos = 0;
    protected int count;

    public CharArrayReader(char[] buf) {
        if (buf == null) throw ModelIo.arrayLengthOfNull("buf");
        this.buf = buf;
        this.pos = 0;
        this.count = buf.length;
    }

    public CharArrayReader(char[] buf, int offset, int length) {
        if (offset < 0) throw new IllegalArgumentException();
        if (buf == null) throw ModelIo.arrayLengthOfNull("buf");
        if (offset > buf.length || length < 0 || offset + length < 0) throw new IllegalArgumentException();
        this.buf = buf;
        this.pos = offset;
        this.count = Math.min(offset + length, buf.length);
        this.markedPos = offset;
    }

    private void checkOpen() throws IOException {
        if (buf == null) throw new IOException("Stream closed");
    }

    public int read() throws IOException {
        synchronized (lock) {
            checkOpen();
            if (pos >= count) return -1;
            return buf[pos++];
        }
    }

    public int read(char[] cbuf, int off, int len) throws IOException {
        synchronized (lock) {
            checkOpen();
            if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
            ModelIo.checkFromIndexSize(off, len, cbuf.length);
            if (len == 0) return 0;
            if (pos >= count) return -1;
            int n = Math.min(len, count - pos);
            if (n <= 0) return 0;
            System.arraycopy(buf, pos, cbuf, off, n);
            pos += n;
            return n;
        }
    }

    public int read(java.nio.CharBuffer target) throws IOException {
        throw ModelIo.unsupported("CharArrayReader.read(CharBuffer)");
    }

    public long skip(long n) throws IOException {
        synchronized (lock) {
            checkOpen();
            long avail = count - pos;
            if (n > avail) n = avail;
            if (n < 0) return 0;
            pos += (int) n;
            return n;
        }
    }

    public boolean ready() throws IOException {
        synchronized (lock) {
            checkOpen();
            return count - pos > 0;
        }
    }

    public boolean markSupported() {
        return true;
    }

    public void mark(int readAheadLimit) throws IOException {
        synchronized (lock) {
            checkOpen();
            markedPos = pos;
        }
    }

    public void reset() throws IOException {
        synchronized (lock) {
            checkOpen();
            pos = markedPos;
        }
    }

    public void close() {
        synchronized (lock) {
            buf = null;
        }
    }
}

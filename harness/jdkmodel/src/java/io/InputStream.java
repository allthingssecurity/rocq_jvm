/*
 * rocq-jvm model of java.io.InputStream (clean-room, Apache-2.0): the JDK 21 default methods
 * (read(byte[]) / read(byte[], int, int) through read(), readAllBytes / readNBytes with the JDK's
 * 16384-byte chunks, skip through read with a 2048-byte buffer, skipNBytes, transferTo with
 * 16384-byte chunks, mark/reset unsupported) and nullInputStream(), with the JDK's exception
 * messages. Arrays above the machine's bound (2^20 elements) are STUCK, so readNBytes never
 * reaches the JDK's OutOfMemoryError cases.
 */
package java.io;

public abstract class InputStream implements Closeable {
    private static final int SKIP_CHUNK = 2048;
    private static final int CHUNK = 16384;

    public InputStream() {
    }

    public static InputStream nullInputStream() {
        return new NullInput();
    }

    private static final class NullInput extends InputStream {
        private volatile boolean closed;

        private void checkOpen() throws IOException {
            if (closed) throw new IOException("Stream closed");
        }

        public int available() throws IOException {
            checkOpen();
            return 0;
        }

        public int read() throws IOException {
            checkOpen();
            return -1;
        }

        public int read(byte[] b, int off, int len) throws IOException {
            if (b == null) throw ModelIo.arrayLengthOfNull("b");
            ModelIo.checkFromIndexSize(off, len, b.length);
            if (len == 0) return 0;
            checkOpen();
            return -1;
        }

        public byte[] readAllBytes() throws IOException {
            checkOpen();
            return new byte[0];
        }

        public int readNBytes(byte[] b, int off, int len) throws IOException {
            if (b == null) throw ModelIo.arrayLengthOfNull("b");
            ModelIo.checkFromIndexSize(off, len, b.length);
            checkOpen();
            return 0;
        }

        public byte[] readNBytes(int len) throws IOException {
            if (len < 0) throw new IllegalArgumentException("len < 0");
            checkOpen();
            return new byte[0];
        }

        public long skip(long n) throws IOException {
            checkOpen();
            return 0L;
        }

        public void skipNBytes(long n) throws IOException {
            checkOpen();
            if (n > 0) throw new EOFException();
        }

        public long transferTo(OutputStream out) throws IOException {
            if (out == null) throw new NullPointerException();
            checkOpen();
            return 0L;
        }

        public void close() throws IOException {
            closed = true;
        }
    }

    public abstract int read() throws IOException;

    public int read(byte[] b) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        return read(b, 0, b.length);
    }

    public int read(byte[] b, int off, int len) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        ModelIo.checkFromIndexSize(off, len, b.length);
        if (len == 0) return 0;
        int c = read();
        if (c == -1) return -1;
        b[off] = (byte) c;
        int got = 1;
        try {
            while (got < len) {
                c = read();
                if (c == -1) break;
                b[off + got] = (byte) c;
                got++;
            }
        } catch (IOException ignored) {
            // the Javadoc: an IOException after the first byte ends the read
        }
        return got;
    }

    public byte[] readAllBytes() throws IOException {
        return readNBytes(Integer.MAX_VALUE);
    }

    public byte[] readNBytes(int len) throws IOException {
        if (len < 0) throw new IllegalArgumentException("len < 0");
        java.util.ArrayList<byte[]> chunks = null;
        byte[] first = null;
        int total = 0;
        int left = len;
        int n;
        do {
            byte[] chunk = new byte[Math.min(left, CHUNK)];
            int filled = 0;
            while ((n = read(chunk, filled, Math.min(chunk.length - filled, left))) > 0) {
                filled += n;
                left -= n;
            }
            if (filled > 0) {
                if (filled < chunk.length) chunk = copy(chunk, filled);
                total += filled;
                if (first == null) {
                    first = chunk;
                } else {
                    if (chunks == null) {
                        chunks = new java.util.ArrayList<>();
                        chunks.add(first);
                    }
                    chunks.add(chunk);
                }
            }
        } while (n >= 0 && left > 0);
        if (chunks == null) {
            if (first == null) return new byte[0];
            return first.length == total ? first : copy(first, total);
        }
        byte[] all = new byte[total];
        int at = 0;
        for (byte[] c : chunks) {
            System.arraycopy(c, 0, all, at, c.length);
            at += c.length;
        }
        return all;
    }

    private static byte[] copy(byte[] a, int n) {
        byte[] r = new byte[n];
        System.arraycopy(a, 0, r, 0, n);
        return r;
    }

    public int readNBytes(byte[] b, int off, int len) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        ModelIo.checkFromIndexSize(off, len, b.length);
        int got = 0;
        while (got < len) {
            int k = read(b, off + got, len - got);
            if (k < 0) break;
            got += k;
        }
        return got;
    }

    public long skip(long n) throws IOException {
        if (n <= 0) return 0;
        long left = n;
        int size = (int) Math.min(SKIP_CHUNK, left);
        byte[] scratch = new byte[size];
        while (left > 0) {
            int k = read(scratch, 0, (int) Math.min(size, left));
            if (k < 0) break;
            left -= k;
        }
        return n - left;
    }

    public void skipNBytes(long n) throws IOException {
        while (n > 0) {
            long k = skip(n);
            if (k > 0 && k <= n) {
                n -= k;
            } else if (k == 0) {
                if (read() == -1) throw new EOFException();
                n--;
            } else {
                throw new IOException("Unable to skip exactly");
            }
        }
    }

    public int available() throws IOException {
        return 0;
    }

    public void close() throws IOException {
    }

    public void mark(int readlimit) {
    }

    public void reset() throws IOException {
        throw new IOException("mark/reset not supported");
    }

    public boolean markSupported() {
        return false;
    }

    public long transferTo(OutputStream out) throws IOException {
        if (out == null) throw new NullPointerException("out");
        long moved = 0;
        byte[] chunk = new byte[CHUNK];
        int k;
        while ((k = read(chunk, 0, CHUNK)) >= 0) {
            out.write(chunk, 0, k);
            if (moved < Long.MAX_VALUE) {
                long t = moved + k;
                moved = t < moved ? Long.MAX_VALUE : t;
            }
        }
        return moved;
    }
}

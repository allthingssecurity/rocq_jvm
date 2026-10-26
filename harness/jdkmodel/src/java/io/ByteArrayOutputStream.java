/*
 * rocq-jvm model of java.io.ByteArrayOutputStream (clean-room, Apache-2.0): JDK 21 behaviour
 * (initial capacity 32, growth to max(needed, 2 * capacity) as ArraysSupport.newLength,
 * toString() in the default charset UTF-8 and toString(charset) through the String
 * constructors, i.e. the model Charset's decoders; writeTo writes the whole buffer in one call
 * (the JDK copies it first on a virtual thread, which the model does not have)).
 */
package java.io;

import java.nio.charset.Charset;

public class ByteArrayOutputStream extends OutputStream {
    protected byte[] buf;
    protected int count;

    public ByteArrayOutputStream() {
        this(32);
    }

    public ByteArrayOutputStream(int size) {
        if (size < 0) throw new IllegalArgumentException("Negative initial size: " + size);
        buf = new byte[size];
    }

    private void grow(int needed) {
        int cap = buf.length;
        int extra = needed - cap;
        if (extra > 0) {
            int newCap = cap + Math.max(extra, cap);
            if (newCap < 0 || newCap > Integer.MAX_VALUE - 8)
                throw ModelIo.unsupported("ByteArrayOutputStream beyond the JDK's soft array limit");
            byte[] b = new byte[newCap];
            System.arraycopy(buf, 0, b, 0, cap);
            buf = b;
        }
    }

    public synchronized void write(int b) {
        grow(count + 1);
        buf[count] = (byte) b;
        count++;
    }

    public synchronized void write(byte[] b, int off, int len) {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        ModelIo.checkFromIndexSize(off, len, b.length);
        grow(count + len);
        System.arraycopy(b, off, buf, count, len);
        count += len;
    }

    public void writeBytes(byte[] b) {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        write(b, 0, b.length);
    }

    public void writeTo(OutputStream out) throws IOException {
        synchronized (this) {
            if (out == null) throw ModelIo.invokeOnNull("java.io.OutputStream.write(byte[], int, int)", "out");
            out.write(buf, 0, count);
        }
    }

    public synchronized void reset() {
        count = 0;
    }

    public synchronized byte[] toByteArray() {
        byte[] r = new byte[count];
        System.arraycopy(buf, 0, r, 0, count);
        return r;
    }

    public synchronized int size() {
        return count;
    }

    public synchronized String toString() {
        return new String(buf, 0, count);
    }

    public synchronized String toString(String charsetName) throws UnsupportedEncodingException {
        return new String(buf, 0, count, charsetName);
    }

    public synchronized String toString(Charset charset) {
        return new String(buf, 0, count, charset);
    }

    @Deprecated
    public synchronized String toString(int hibyte) {
        StringBuilder b = new StringBuilder(count);
        for (int i = 0; i < count; i++) b.append((char) (((hibyte & 0xff) << 8) | (buf[i] & 0xff)));
        return b.toString();
    }

    public void close() throws IOException {
    }
}

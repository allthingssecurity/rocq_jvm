/*
 * rocq-jvm model of java.io.CharArrayWriter (clean-room, Apache-2.0): JDK 21 behaviour
 * (initial capacity 32, growth to max(2 * capacity, needed) before the copy, so a failing
 * write(String, off, len) may still have grown the buffer) and messages.
 */
package java.io;

public class CharArrayWriter extends Writer {
    protected char[] buf;
    protected int count;

    public CharArrayWriter() {
        this(32);
    }

    public CharArrayWriter(int initialSize) {
        if (initialSize < 0) throw new IllegalArgumentException("Negative initial size: " + initialSize);
        buf = new char[initialSize];
    }

    private void ensure(int newcount) {
        if (newcount > buf.length) {
            char[] b = new char[Math.max(buf.length << 1, newcount)];
            System.arraycopy(buf, 0, b, 0, buf.length);
            buf = b;
        }
    }

    public void write(int c) {
        synchronized (lock) {
            int newcount = count + 1;
            ensure(newcount);
            buf[count] = (char) c;
            count = newcount;
        }
    }

    public void write(char[] c, int off, int len) {
        if (c == null) throw ModelIo.arrayLengthOfNull("c");
        ModelIo.checkFromIndexSize(off, len, c.length);
        if (len == 0) return;
        synchronized (lock) {
            int newcount = count + len;
            ensure(newcount);
            System.arraycopy(c, off, buf, count, len);
            count = newcount;
        }
    }

    public void write(String str, int off, int len) {
        synchronized (lock) {
            int newcount = count + len;
            ensure(newcount);
            if (str == null) throw ModelIo.invokeOnNull("String.getChars(int, int, char[], int)", "str");
            ModelIo.getChars(str, off, off + len, buf, count);
            count = newcount;
        }
    }

    public void writeTo(Writer out) throws IOException {
        synchronized (lock) {
            if (out == null) throw ModelIo.invokeOnNull("java.io.Writer.write(char[], int, int)", "out");
            out.write(buf, 0, count);
        }
    }

    public CharArrayWriter append(CharSequence csq) {
        String s = ModelIo.valueOf(csq);
        write(s, 0, s.length());
        return this;
    }

    public CharArrayWriter append(CharSequence csq, int start, int end) {
        if (csq == null) csq = "null";
        return append(ModelIo.subSequence(csq, start, end));
    }

    public CharArrayWriter append(char c) {
        write(c);
        return this;
    }

    public void reset() {
        count = 0;
    }

    public char[] toCharArray() {
        synchronized (lock) {
            char[] r = new char[count];
            System.arraycopy(buf, 0, r, 0, count);
            return r;
        }
    }

    public int size() {
        return count;
    }

    public String toString() {
        synchronized (lock) {
            return new String(buf, 0, count);
        }
    }

    public void flush() {
    }

    public void close() {
    }
}

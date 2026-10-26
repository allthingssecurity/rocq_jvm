/*
 * rocq-jvm model of java.io.StringWriter (clean-room, Apache-2.0): JDK 21 behaviour and
 * messages (write(String, off, len) and append treat a null string as "null"; the index errors
 * are those of StringBuffer.append). The buffer is a StringBuilder (the machine has no
 * StringBuffer model): getBuffer() is STUCK.
 */
package java.io;

public class StringWriter extends Writer {
    private final StringBuilder buf;

    public StringWriter() {
        buf = new StringBuilder();
        lock = buf;
    }

    public StringWriter(int initialSize) {
        if (initialSize < 0) throw new IllegalArgumentException("Negative buffer size");
        buf = new StringBuilder(initialSize);
        lock = buf;
    }

    public void write(int c) {
        buf.append((char) c);
    }

    public void write(char[] cbuf, int off, int len) {
        if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
        ModelIo.checkFromIndexSize(off, len, cbuf.length);
        if (len == 0) return;
        for (int i = 0; i < len; i++) buf.append(cbuf[off + i]);
    }

    public void write(String str) {
        buf.append(str);
    }

    public void write(String str, int off, int len) {
        // AbstractStringBuilder.append(CharSequence, start, end)
        String s = str == null ? "null" : str;
        int end = off + len;
        ModelIo.checkFromToIndex(off, end, s.length());
        for (int i = off; i < end; i++) buf.append(s.charAt(i));
    }

    public StringWriter append(CharSequence csq) {
        write(ModelIo.valueOf(csq));
        return this;
    }

    public StringWriter append(CharSequence csq, int start, int end) {
        if (csq == null) csq = "null";
        return append(ModelIo.subSequence(csq, start, end));
    }

    public StringWriter append(char c) {
        write(c);
        return this;
    }

    public String toString() {
        return buf.toString();
    }

    public StringBuffer getBuffer() {
        throw ModelIo.unsupported("StringWriter.getBuffer (no StringBuffer model)");
    }

    public void flush() {
    }

    public void close() throws IOException {
    }
}

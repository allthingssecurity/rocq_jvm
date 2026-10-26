/*
 * rocq-jvm model of java.io.Writer (clean-room, Apache-2.0): the JDK 21 lock rules (as in
 * Reader), write(int) and write(String, int, int) through write(char[], int, int) with the JDK's
 * shared 1024-char buffer (a larger fresh array for longer strings), the append methods
 * (String.valueOf / subSequence), nullWriter(), and the JDK's messages.
 */
package java.io;

public abstract class Writer implements Appendable, Closeable, Flushable {
    private static final int BUF = 1024;
    private char[] writeBuf;

    public static Writer nullWriter() {
        return new NullWriter();
    }

    private static final class NullWriter extends Writer {
        private volatile boolean closed;

        private void checkOpen() throws IOException {
            if (closed) throw new IOException("Stream closed");
        }

        public Writer append(char c) throws IOException {
            checkOpen();
            return this;
        }

        public Writer append(CharSequence csq) throws IOException {
            checkOpen();
            return this;
        }

        public Writer append(CharSequence csq, int start, int end) throws IOException {
            checkOpen();
            if (csq != null) ModelIo.checkFromToIndex(start, end, csq.length());
            return this;
        }

        public void write(int c) throws IOException {
            checkOpen();
        }

        public void write(char[] cbuf, int off, int len) throws IOException {
            if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
            ModelIo.checkFromIndexSize(off, len, cbuf.length);
            checkOpen();
        }

        public void write(String str) throws IOException {
            if (str == null) throw new NullPointerException();
            checkOpen();
        }

        public void write(String str, int off, int len) throws IOException {
            if (str == null) throw ModelIo.invokeOnNull("String.length()", "str");
            ModelIo.checkFromIndexSize(off, len, str.length());
            checkOpen();
        }

        public void flush() throws IOException {
            checkOpen();
        }

        public void close() throws IOException {
            closed = true;
        }
    }

    protected Object lock;

    protected Writer() {
        this.lock = this;
    }

    /** The JDK's package-private Writer(Writer): writer.getClass() is the null check. */
    Writer(Writer writer) {
        if (writer == null) throw ModelIo.invokeOnNull("Object.getClass()", "writer");
        this.lock = writer;
    }

    protected Writer(Object lock) {
        if (lock == null) throw new NullPointerException();
        this.lock = lock;
    }

    public void write(int c) throws IOException {
        synchronized (lock) {
            if (writeBuf == null) writeBuf = new char[BUF];
            writeBuf[0] = (char) c;
            write(writeBuf, 0, 1);
        }
    }

    public void write(char[] cbuf) throws IOException {
        if (cbuf == null) throw ModelIo.arrayLengthOfNull("cbuf");
        write(cbuf, 0, cbuf.length);
    }

    public abstract void write(char[] cbuf, int off, int len) throws IOException;

    public void write(String str) throws IOException {
        if (str == null) throw ModelIo.invokeOnNull("String.length()", "str");
        write(str, 0, str.length());
    }

    public void write(String str, int off, int len) throws IOException {
        synchronized (lock) {
            char[] b;
            if (len <= BUF) {
                if (writeBuf == null) writeBuf = new char[BUF];
                b = writeBuf;
            } else {
                b = new char[len];
            }
            if (str == null) throw ModelIo.invokeOnNull("String.getChars(int, int, char[], int)", "str");
            ModelIo.getChars(str, off, off + len, b, 0);
            write(b, 0, len);
        }
    }

    public Writer append(CharSequence csq) throws IOException {
        write(ModelIo.valueOf(csq));
        return this;
    }

    public Writer append(CharSequence csq, int start, int end) throws IOException {
        if (csq == null) csq = "null";
        return append(ModelIo.subSequence(csq, start, end));
    }

    public Writer append(char c) throws IOException {
        write(c);
        return this;
    }

    public abstract void flush() throws IOException;

    public abstract void close() throws IOException;
}

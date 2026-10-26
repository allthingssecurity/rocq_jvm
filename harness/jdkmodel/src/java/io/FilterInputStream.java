/*
 * rocq-jvm model of java.io.FilterInputStream (clean-room, Apache-2.0): every method delegates
 * to the wrapped stream (read(byte[]) through this.read(b, 0, b.length)); a null wrapped stream
 * gives HotSpot's NullPointerException messages of the JDK 21 code.
 */
package java.io;

public class FilterInputStream extends InputStream {
    protected volatile InputStream in;

    protected FilterInputStream(InputStream in) {
        this.in = in;
    }

    final InputStream inOrNpe(String method) {
        InputStream i = in;
        if (i == null) throw ModelIo.invokeOnNull("java.io.InputStream." + method, "this.in");
        return i;
    }

    public int read() throws IOException {
        return inOrNpe("read()").read();
    }

    public int read(byte[] b) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        return read(b, 0, b.length);
    }

    public int read(byte[] b, int off, int len) throws IOException {
        return inOrNpe("read(byte[], int, int)").read(b, off, len);
    }

    public long skip(long n) throws IOException {
        return inOrNpe("skip(long)").skip(n);
    }

    public int available() throws IOException {
        return inOrNpe("available()").available();
    }

    public void close() throws IOException {
        inOrNpe("close()").close();
    }

    public void mark(int readlimit) {
        inOrNpe("mark(int)").mark(readlimit);
    }

    public void reset() throws IOException {
        inOrNpe("reset()").reset();
    }

    public boolean markSupported() {
        return inOrNpe("markSupported()").markSupported();
    }
}

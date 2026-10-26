/* rocq-jvm model of java.io.Closeable (clean-room, Apache-2.0). */
package java.io;

public interface Closeable extends AutoCloseable {
    public void close() throws IOException;
}

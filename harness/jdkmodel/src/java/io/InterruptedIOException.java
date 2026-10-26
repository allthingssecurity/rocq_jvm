/* rocq-jvm model of java.io.InterruptedIOException (clean-room, Apache-2.0): the JDK 21
 * constructors and the public bytesTransferred field. */
package java.io;

public class InterruptedIOException extends IOException {
    private static final long serialVersionUID = 4020568460727500567L;

    public int bytesTransferred = 0;

    public InterruptedIOException() {
        super();
    }

    public InterruptedIOException(String s) {
        super(s);
    }
}

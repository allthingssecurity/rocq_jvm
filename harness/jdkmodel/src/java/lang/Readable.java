/* rocq-jvm model of java.lang.Readable (clean-room, Apache-2.0). java.nio.CharBuffer is not
 * modelled: the readers' read(CharBuffer) is STUCK. */
package java.lang;

public interface Readable {
    public int read(java.nio.CharBuffer cb) throws java.io.IOException;
}

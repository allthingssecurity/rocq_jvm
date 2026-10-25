/* rocq-jvm model of java.io.FileNotFoundException (clean-room, Apache-2.0): the JDK 21 constructors. */
package java.io;

public class FileNotFoundException extends IOException {
    private static final long serialVersionUID = 1L;

    public FileNotFoundException() {
        super();
    }

    public FileNotFoundException(String s) {
        super(s);
    }
}

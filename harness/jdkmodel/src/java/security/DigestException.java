/*
 * rocq-jvm model of java.security.DigestException (clean-room, Apache-2.0): the four constructors of a
 * checked exception (message, cause).
 */
package java.security;

public class DigestException extends GeneralSecurityException {
    private static final long serialVersionUID = 1L;

    public DigestException() {
        super();
    }

    public DigestException(String msg) {
        super(msg);
    }

    public DigestException(String message, Throwable cause) {
        super(message, cause);
    }

    public DigestException(Throwable cause) {
        super(cause);
    }
}

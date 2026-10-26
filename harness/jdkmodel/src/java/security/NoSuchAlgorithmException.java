/*
 * rocq-jvm model of java.security.NoSuchAlgorithmException (clean-room, Apache-2.0): the four constructors of a
 * checked exception (message, cause).
 */
package java.security;

public class NoSuchAlgorithmException extends GeneralSecurityException {
    private static final long serialVersionUID = 1L;

    public NoSuchAlgorithmException() {
        super();
    }

    public NoSuchAlgorithmException(String msg) {
        super(msg);
    }

    public NoSuchAlgorithmException(String message, Throwable cause) {
        super(message, cause);
    }

    public NoSuchAlgorithmException(Throwable cause) {
        super(cause);
    }
}

/*
 * rocq-jvm model of java.security.GeneralSecurityException (clean-room, Apache-2.0): the four constructors of a
 * checked exception (message, cause).
 */
package java.security;

public class GeneralSecurityException extends Exception {
    private static final long serialVersionUID = 1L;

    public GeneralSecurityException() {
        super();
    }

    public GeneralSecurityException(String msg) {
        super(msg);
    }

    public GeneralSecurityException(String message, Throwable cause) {
        super(message, cause);
    }

    public GeneralSecurityException(Throwable cause) {
        super(cause);
    }
}

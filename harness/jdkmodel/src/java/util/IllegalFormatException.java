/* rocq-jvm model of java.util.IllegalFormatException (clean-room). toString and
 * getLocalizedMessage as Throwable's, through the subclasses' getMessage. */
package java.util;

public class IllegalFormatException extends IllegalArgumentException {
    IllegalFormatException() {
    }

    public String getLocalizedMessage() {
        return getMessage();
    }

    public String toString() {
        String s = getClass().getName();
        String m = getLocalizedMessage();
        return (m != null) ? (s + ": " + m) : s;
    }
}

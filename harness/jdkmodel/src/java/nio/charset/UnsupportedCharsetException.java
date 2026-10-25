/* rocq-jvm model of java.nio.charset.UnsupportedCharsetException (clean-room, Apache-2.0). */
package java.nio.charset;

public class UnsupportedCharsetException extends IllegalArgumentException {
    private static final long serialVersionUID = 1490765524727386367L;
    private final String charsetName;

    public UnsupportedCharsetException(String charsetName) {
        super(String.valueOf(charsetName));
        this.charsetName = charsetName;
    }

    public String getCharsetName() {
        return charsetName;
    }
}

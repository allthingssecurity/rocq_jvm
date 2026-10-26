/*
 * rocq-jvm model of java.net.URISyntaxException (clean-room, Apache-2.0), from the Javadoc: the input
 * string, the reason (the Throwable message) and the index (-1 = unknown). A null input or reason is a
 * NullPointerException, an index below -1 an IllegalArgumentException (neither has a message, as in
 * JDK 21). getMessage() is "<reason>[ at index <index>]: <input>".
 */
package java.net;

public class URISyntaxException extends Exception {
    private static final long serialVersionUID = 2137979680897488891L;

    private final String input;
    private final int index;

    public URISyntaxException(String input, String reason, int index) {
        super(reason);
        if (input == null || reason == null) throw new NullPointerException();
        if (index < -1) throw new IllegalArgumentException();
        this.input = input;
        this.index = index;
    }

    public URISyntaxException(String input, String reason) {
        this(input, reason, -1);
    }

    public String getInput() {
        return input;
    }

    public String getReason() {
        return super.getMessage();
    }

    public int getIndex() {
        return index;
    }

    public String getMessage() {
        StringBuilder b = new StringBuilder();
        b.append(getReason());
        if (index > -1) b.append(" at index ").append(index);
        b.append(": ").append(input);
        return b.toString();
    }
}

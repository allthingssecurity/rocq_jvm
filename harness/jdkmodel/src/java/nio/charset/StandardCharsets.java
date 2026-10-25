/* rocq-jvm model of java.nio.charset.StandardCharsets (clean-room, Apache-2.0). */
package java.nio.charset;

public final class StandardCharsets {
    private StandardCharsets() {
        throw new AssertionError("No java.nio.charset.StandardCharsets instances for you!");
    }

    public static final Charset US_ASCII = sun.nio.cs.US_ASCII.INSTANCE;
    public static final Charset ISO_8859_1 = sun.nio.cs.ISO_8859_1.INSTANCE;
    public static final Charset UTF_8 = sun.nio.cs.UTF_8.INSTANCE;
    public static final Charset UTF_16BE = sun.nio.cs.UTF_16BE.INSTANCE;
    public static final Charset UTF_16LE = sun.nio.cs.UTF_16LE.INSTANCE;
    public static final Charset UTF_16 = sun.nio.cs.UTF_16.INSTANCE;
}

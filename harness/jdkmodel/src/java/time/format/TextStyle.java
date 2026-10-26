/* rocq-jvm model of java.time.format.TextStyle (clean-room, Apache-2.0). */
package java.time.format;

public enum TextStyle {
    FULL,
    FULL_STANDALONE,
    SHORT,
    SHORT_STANDALONE,
    NARROW,
    NARROW_STANDALONE;

    public boolean isStandalone() {
        return (ordinal() & 1) == 1;
    }

    public TextStyle asStandalone() {
        return TextStyle.values()[ordinal() | 1];
    }

    public TextStyle asNormal() {
        return TextStyle.values()[ordinal() & ~1];
    }
}

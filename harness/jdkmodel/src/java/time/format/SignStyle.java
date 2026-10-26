/* rocq-jvm model of java.time.format.SignStyle (clean-room, Apache-2.0): JDK 21's parse rule. */
package java.time.format;

public enum SignStyle {
    NORMAL,
    ALWAYS,
    NEVER,
    NOT_NEGATIVE,
    EXCEEDS_PAD;

    boolean parse(boolean positive, boolean strict, boolean fixedWidth) {
        switch (ordinal()) {
            case 0: return !positive || !strict;
            case 1:
            case 4: return true;
            default: return !strict && !fixedWidth;
        }
    }
}

/* rocq-jvm model of sun.nio.cs.UTF_16 (clean-room, Apache-2.0): the charset UTF-16. */
package sun.nio.cs;

import java.nio.charset.Charset;

public final class UTF_16 extends Charset {
    public static final UTF_16 INSTANCE = new UTF_16();

    public UTF_16() {
        super("UTF-16", new String[] {"UTF_16", "utf16", "unicode", "UnicodeBig"});
    }

    public boolean contains(Charset cs) {
        throw new UnsupportedOperationException();
    }

    protected int kind$() {
        return K_UTF16;
    }
}

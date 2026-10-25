/* rocq-jvm model of sun.nio.cs.UTF_8 (clean-room, Apache-2.0): the charset UTF-8. */
package sun.nio.cs;

import java.nio.charset.Charset;

public final class UTF_8 extends Charset {
    public static final UTF_8 INSTANCE = new UTF_8();

    public UTF_8() {
        super("UTF-8", new String[] {"UTF8", "unicode-1-1-utf-8"});
    }

    public boolean contains(Charset cs) {
        throw new UnsupportedOperationException();
    }

    protected int kind$() {
        return K_UTF8;
    }
}

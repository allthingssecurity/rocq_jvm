/* rocq-jvm model of sun.nio.cs.UTF_16BE (clean-room, Apache-2.0): the charset UTF-16BE. */
package sun.nio.cs;

import java.nio.charset.Charset;

public final class UTF_16BE extends Charset {
    public static final UTF_16BE INSTANCE = new UTF_16BE();

    public UTF_16BE() {
        super("UTF-16BE", new String[] {"UTF_16BE", "ISO-10646-UCS-2", "X-UTF-16BE", "UnicodeBigUnmarked"});
    }

    public boolean contains(Charset cs) {
        throw new UnsupportedOperationException();
    }

    protected int kind$() {
        return K_UTF16BE;
    }
}

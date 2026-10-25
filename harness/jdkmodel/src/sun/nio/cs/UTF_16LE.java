/* rocq-jvm model of sun.nio.cs.UTF_16LE (clean-room, Apache-2.0): the charset UTF-16LE. */
package sun.nio.cs;

import java.nio.charset.Charset;

public final class UTF_16LE extends Charset {
    public static final UTF_16LE INSTANCE = new UTF_16LE();

    public UTF_16LE() {
        super("UTF-16LE", new String[] {"UTF_16LE", "X-UTF-16LE", "UnicodeLittleUnmarked"});
    }

    public boolean contains(Charset cs) {
        throw new UnsupportedOperationException();
    }

    protected int kind$() {
        return K_UTF16LE;
    }
}

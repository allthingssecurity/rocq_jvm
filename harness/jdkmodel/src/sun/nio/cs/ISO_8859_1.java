/* rocq-jvm model of sun.nio.cs.ISO_8859_1 (clean-room, Apache-2.0): the charset ISO-8859-1. */
package sun.nio.cs;

import java.nio.charset.Charset;

public final class ISO_8859_1 extends Charset {
    public static final ISO_8859_1 INSTANCE = new ISO_8859_1();

    public ISO_8859_1() {
        super("ISO-8859-1", new String[] {"iso-ir-100", "ISO_8859-1", "latin1", "l1", "IBM819", "cp819", "csISOLatin1", "819", "IBM-819", "ISO8859_1", "ISO_8859-1:1987", "ISO_8859_1", "8859_1", "ISO8859-1"});
    }

    public boolean contains(Charset cs) {
        throw new UnsupportedOperationException();
    }

    protected int kind$() {
        return K_LATIN1;
    }
}

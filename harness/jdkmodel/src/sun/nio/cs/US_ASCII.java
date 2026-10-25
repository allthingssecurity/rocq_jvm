/* rocq-jvm model of sun.nio.cs.US_ASCII (clean-room, Apache-2.0): the charset US-ASCII. */
package sun.nio.cs;

import java.nio.charset.Charset;

public final class US_ASCII extends Charset {
    public static final US_ASCII INSTANCE = new US_ASCII();

    public US_ASCII() {
        super("US-ASCII", new String[] {"iso-ir-6", "ANSI_X3.4-1986", "ISO_646.irv:1991", "ASCII", "ISO646-US", "us", "IBM367", "cp367", "csASCII", "646", "iso_646.irv:1983", "ANSI_X3.4-1968", "ascii7"});
    }

    public boolean contains(Charset cs) {
        throw new UnsupportedOperationException();
    }

    protected int kind$() {
        return K_ASCII;
    }
}

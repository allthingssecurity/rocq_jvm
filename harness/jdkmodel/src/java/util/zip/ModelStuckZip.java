/* rocq-jvm helper (not a JDK class): a native method without a Rocq model, so that a call makes
 * the machine STUCK (no claim), as java.util.ModelStuck. HotSpot never loads this class. */
package java.util.zip;

final class ModelStuckZip {
    private ModelStuckZip() {
    }

    static native RuntimeException unsupported(String what);

    /** Preconditions.checkFromIndexSize with the AIOOBE formatter, after the JDK's explicit
     *  null check. */
    static void checkArray(byte[] b, int off, int len) {
        if (b == null) throw new NullPointerException();
        if ((b.length | off | len) < 0 || len > b.length - off)
            throw new ArrayIndexOutOfBoundsException("Range [" + off + ", " + off + " + " + len
                + ") out of bounds for length " + b.length);
    }
}

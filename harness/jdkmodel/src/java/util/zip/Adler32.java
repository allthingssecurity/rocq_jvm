/* rocq-jvm model of java.util.zip.Adler32 (clean-room, Apache-2.0): Adler-32 of RFC 1950 (sums
 * modulo 65521, initial value 1); JDK 21's argument checks. update(ByteBuffer) is STUCK. */
package java.util.zip;

public class Adler32 implements Checksum {
    private int adler = 1;

    public Adler32() {
    }

    private static int step(int adler, int b) {
        int s1 = adler & 0xffff, s2 = adler >>> 16;
        s1 = (s1 + (b & 0xff)) % 65521;
        s2 = (s2 + s1) % 65521;
        return (s2 << 16) | s1;
    }

    public void update(int b) {
        adler = step(adler, b);
    }

    public void update(byte[] b, int off, int len) {
        ModelStuckZip.checkArray(b, off, len);
        for (int i = 0; i < len; i++) adler = step(adler, b[off + i]);
    }

    public void update(java.nio.ByteBuffer buffer) {
        throw ModelStuckZip.unsupported("Adler32.update(ByteBuffer)");
    }

    public void reset() {
        adler = 1;
    }

    public long getValue() {
        return (long) adler & 0xffffffffL;
    }
}

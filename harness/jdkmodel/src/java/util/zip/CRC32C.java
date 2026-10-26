/* rocq-jvm model of java.util.zip.CRC32C (clean-room, Apache-2.0): CRC-32C (Castagnoli, RFC 3720;
 * reflected polynomial 0x82F63B78, initial and final value 0xFFFFFFFF), computed bitwise; JDK
 * 21's argument checks. update(ByteBuffer) is STUCK. */
package java.util.zip;

public final class CRC32C implements Checksum {
    private int crc = 0xFFFFFFFF;

    public CRC32C() {
    }

    private static int step(int c, int b) {
        c ^= (b & 0xff);
        for (int k = 0; k < 8; k++) c = (c >>> 1) ^ ((c & 1) != 0 ? 0x82F63B78 : 0);
        return c;
    }

    public void update(int b) {
        crc = step(crc, b);
    }

    public void update(byte[] b, int off, int len) {
        ModelStuckZip.checkArray(b, off, len);
        for (int i = 0; i < len; i++) crc = step(crc, b[off + i]);
    }

    public void update(java.nio.ByteBuffer buffer) {
        throw ModelStuckZip.unsupported("CRC32C.update(ByteBuffer)");
    }

    public void reset() {
        crc = 0xFFFFFFFF;
    }

    public long getValue() {
        return (~crc) & 0xFFFFFFFFL;
    }
}

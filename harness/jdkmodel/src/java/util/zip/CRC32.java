/* rocq-jvm model of java.util.zip.CRC32 (clean-room, Apache-2.0): the CRC-32 of ISO 3309 /
 * ITU-T V.42 (reflected polynomial 0xEDB88320, initial and final value 0xFFFFFFFF), computed
 * bitwise; JDK 21's argument checks. update(ByteBuffer) is STUCK. */
package java.util.zip;

public class CRC32 implements Checksum {
    private int crc;

    public CRC32() {
    }

    static int step(int crc, int b, int poly) {
        int c = ~crc ^ (b & 0xff);
        for (int k = 0; k < 8; k++) c = (c >>> 1) ^ ((c & 1) != 0 ? poly : 0);
        return ~c;
    }

    public void update(int b) {
        crc = step(crc, b, 0xEDB88320);
    }

    public void update(byte[] b, int off, int len) {
        ModelStuckZip.checkArray(b, off, len);
        for (int i = 0; i < len; i++) crc = step(crc, b[off + i], 0xEDB88320);
    }

    public void update(java.nio.ByteBuffer buffer) {
        throw ModelStuckZip.unsupported("CRC32.update(ByteBuffer)");
    }

    public void reset() {
        crc = 0;
    }

    public long getValue() {
        return (long) crc & 0xffffffffL;
    }
}

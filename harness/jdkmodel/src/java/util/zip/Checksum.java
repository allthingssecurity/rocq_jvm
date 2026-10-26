/* rocq-jvm model of java.util.zip.Checksum (clean-room, Apache-2.0); update(ByteBuffer) is STUCK
 * (no java.nio buffers). */
package java.util.zip;

public interface Checksum {
    public void update(int b);

    default public void update(byte[] b) {
        if (b == null) throw new NullPointerException("Cannot read the array length because \"b\" is null");
        update(b, 0, b.length);
    }

    public void update(byte[] b, int off, int len);

    default public void update(java.nio.ByteBuffer buffer) {
        throw ModelStuckZip.unsupported("Checksum.update(ByteBuffer)");
    }

    public long getValue();

    public void reset();
}

/*
 * rocq-jvm model of java.io.DataOutputStream (clean-room, Apache-2.0), JDK 21 behaviour:
 * big-endian primitives written as one write of 2/4/8 bytes, writeBytes / writeChars, writeUTF
 * in modified UTF-8 (length prefix, '\0' as two bytes, chars as 1-3 bytes) through this.write
 * with the JDK's "too long" UTFDataFormatException message, and the written counter (saturating
 * at Integer.MAX_VALUE).
 */
package java.io;

public class DataOutputStream extends FilterOutputStream implements DataOutput {
    protected int written;
    private byte[] bytearr = null;
    private final byte[] writeBuffer = new byte[8];

    public DataOutputStream(OutputStream out) {
        super(out);
    }

    private void incCount(int value) {
        int temp = written + value;
        if (temp < 0) temp = Integer.MAX_VALUE;
        written = temp;
    }

    public synchronized void write(int b) throws IOException {
        outOrNpe("write(int)").write(b);
        incCount(1);
    }

    public synchronized void write(byte[] b, int off, int len) throws IOException {
        outOrNpe("write(byte[], int, int)").write(b, off, len);
        incCount(len);
    }

    public void flush() throws IOException {
        outOrNpe("flush()").flush();
    }

    public final void writeBoolean(boolean v) throws IOException {
        outOrNpe("write(int)").write(v ? 1 : 0);
        incCount(1);
    }

    public final void writeByte(int v) throws IOException {
        outOrNpe("write(int)").write(v);
        incCount(1);
    }

    private void put(int n, long v) throws IOException {
        for (int i = n - 1; i >= 0; i--) {
            writeBuffer[i] = (byte) v;
            v >>= 8;
        }
        outOrNpe("write(byte[], int, int)").write(writeBuffer, 0, n);
        incCount(n);
    }

    public final void writeShort(int v) throws IOException {
        put(2, v);
    }

    public final void writeChar(int v) throws IOException {
        put(2, v);
    }

    public final void writeInt(int v) throws IOException {
        put(4, v);
    }

    public final void writeLong(long v) throws IOException {
        put(8, v);
    }

    public final void writeFloat(float v) throws IOException {
        put(4, Float.floatToIntBits(v));
    }

    public final void writeDouble(double v) throws IOException {
        put(8, Double.doubleToLongBits(v));
    }

    public final void writeBytes(String s) throws IOException {
        if (s == null) throw ModelIo.invokeOnNull("String.length()", "s");
        int len = s.length();
        for (int i = 0; i < len; i++) outOrNpe("write(int)").write((byte) s.charAt(i));
        incCount(len);
    }

    public final void writeChars(String s) throws IOException {
        if (s == null) throw ModelIo.invokeOnNull("String.length()", "s");
        int len = s.length();
        for (int i = 0; i < len; i++) {
            int v = s.charAt(i);
            writeBuffer[0] = (byte) (v >>> 8);
            writeBuffer[1] = (byte) v;
            outOrNpe("write(byte[], int, int)").write(writeBuffer, 0, 2);
        }
        incCount(len * 2);
    }

    public final void writeUTF(String str) throws IOException {
        writeUTF(str, this);
    }

    static int writeUTF(String str, DataOutput out) throws IOException {
        if (str == null) throw ModelIo.invokeOnNull("String.length()", "str");
        final int strlen = str.length();
        int utflen = strlen;
        for (int i = 0; i < strlen; i++) {
            int c = str.charAt(i);
            if (c >= 0x80 || c == 0) utflen += (c >= 0x800) ? 2 : 1;
        }
        if (utflen > 65535 || utflen < strlen) throw new UTFDataFormatException(tooLongMsg(str, utflen));
        final byte[] bytes;
        if (out instanceof DataOutputStream) {
            DataOutputStream dos = (DataOutputStream) out;
            if (dos.bytearr == null || dos.bytearr.length < utflen + 2) dos.bytearr = new byte[utflen * 2 + 2];
            bytes = dos.bytearr;
        } else {
            bytes = new byte[utflen + 2];
        }
        int count = 0;
        bytes[count++] = (byte) (utflen >>> 8);
        bytes[count++] = (byte) utflen;
        for (int i = 0; i < strlen; i++) {
            int c = str.charAt(i);
            if (c < 0x80 && c != 0) {
                bytes[count++] = (byte) c;
            } else if (c >= 0x800) {
                bytes[count++] = (byte) (0xE0 | ((c >> 12) & 0x0F));
                bytes[count++] = (byte) (0x80 | ((c >> 6) & 0x3F));
                bytes[count++] = (byte) (0x80 | (c & 0x3F));
            } else {
                bytes[count++] = (byte) (0xC0 | ((c >> 6) & 0x1F));
                bytes[count++] = (byte) (0x80 | (c & 0x3F));
            }
        }
        out.write(bytes, 0, utflen + 2);
        return utflen + 2;
    }

    private static String tooLongMsg(String s, int bits32) {
        int slen = s.length();
        String head = s.substring(0, 8);
        String tail = s.substring(slen - 8, slen);
        long actualLength = (long) slen + ((long) (bits32 - slen) & 0xffffffffL);
        return "encoded string (" + head + "..." + tail + ") too long: " + actualLength + " bytes";
    }

    public final int size() {
        return written;
    }
}

/*
 * rocq-jvm model of java.io.DataInputStream (clean-room, Apache-2.0), JDK 21 behaviour: big-endian
 * primitives read with readFully (EOFException at the end), readUTF in modified UTF-8 with the
 * JDK's UTFDataFormatException messages (the length is read first; the whole encoded string is
 * read before decoding), readLine ending at '\n', '\r' or "\r\n" (after a '\r' the next byte is
 * pushed back by wrapping the stream in a PushbackInputStream, as the JDK does).
 */
package java.io;

public class DataInputStream extends FilterInputStream implements DataInput {
    private final byte[] readBuffer = new byte[8];
    private byte[] bytearr = new byte[0];
    private char[] chararr = new char[0];
    private char[] lineBuffer;

    public DataInputStream(InputStream in) {
        super(in);
    }

    public final int read(byte[] b) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        return inOrNpe("read(byte[], int, int)").read(b, 0, b.length);
    }

    public final int read(byte[] b, int off, int len) throws IOException {
        return inOrNpe("read(byte[], int, int)").read(b, off, len);
    }

    public final void readFully(byte[] b) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        readFully(b, 0, b.length);
    }

    public final void readFully(byte[] b, int off, int len) throws IOException {
        if (b == null) throw ModelIo.arrayLengthOfNull("b");
        ModelIo.checkFromIndexSize(off, len, b.length);
        int n = 0;
        while (n < len) {
            int k = inOrNpe("read(byte[], int, int)").read(b, off + n, len - n);
            if (k < 0) throw new EOFException();
            n += k;
        }
    }

    public final int skipBytes(int n) throws IOException {
        int total = 0;
        int cur;
        while (total < n && (cur = (int) inOrNpe("skip(long)").skip(n - total)) > 0) total += cur;
        return total;
    }

    public final boolean readBoolean() throws IOException {
        return readUnsignedByte() != 0;
    }

    public final byte readByte() throws IOException {
        return (byte) readUnsignedByte();
    }

    public final int readUnsignedByte() throws IOException {
        int ch = inOrNpe("read()").read();
        if (ch < 0) throw new EOFException();
        return ch;
    }

    private int u(int i) {
        return readBuffer[i] & 0xff;
    }

    public final short readShort() throws IOException {
        readFully(readBuffer, 0, 2);
        return (short) ((u(0) << 8) | u(1));
    }

    public final int readUnsignedShort() throws IOException {
        readFully(readBuffer, 0, 2);
        return (u(0) << 8) | u(1);
    }

    public final char readChar() throws IOException {
        readFully(readBuffer, 0, 2);
        return (char) ((u(0) << 8) | u(1));
    }

    private int int4() {
        return (u(0) << 24) | (u(1) << 16) | (u(2) << 8) | u(3);
    }

    public final int readInt() throws IOException {
        readFully(readBuffer, 0, 4);
        return int4();
    }

    private long long8() {
        long r = 0;
        for (int i = 0; i < 8; i++) r = (r << 8) | u(i);
        return r;
    }

    public final long readLong() throws IOException {
        readFully(readBuffer, 0, 8);
        return long8();
    }

    public final float readFloat() throws IOException {
        readFully(readBuffer, 0, 4);
        return Float.intBitsToFloat(int4());
    }

    public final double readDouble() throws IOException {
        readFully(readBuffer, 0, 8);
        return Double.longBitsToDouble(long8());
    }

    @Deprecated
    public final String readLine() throws IOException {
        char[] buf = lineBuffer;
        if (buf == null) buf = lineBuffer = new char[128];
        int room = buf.length;
        int offset = 0;
        int c;
        for (;;) {
            c = inOrNpe("read()").read();
            if (c == -1 || c == '\n') break;
            if (c == '\r') {
                int c2 = in.read();
                if (c2 != '\n' && c2 != -1) {
                    if (!(in instanceof PushbackInputStream)) this.in = new PushbackInputStream(in);
                    ((PushbackInputStream) in).unread(c2);
                }
                break;
            }
            if (--room < 0) {
                buf = new char[offset + 128];
                room = buf.length - offset - 1;
                System.arraycopy(lineBuffer, 0, buf, 0, offset);
                lineBuffer = buf;
            }
            buf[offset++] = (char) c;
        }
        if (c == -1 && offset == 0) return null;
        return String.valueOf(buf, 0, offset);
    }

    public final String readUTF() throws IOException {
        return readUTF(this);
    }

    public static final String readUTF(DataInput in) throws IOException {
        if (in == null) throw ModelIo.invokeOnNull("java.io.DataInput.readUnsignedShort()", "in");
        int utflen = in.readUnsignedShort();
        byte[] bytes;
        char[] chars;
        if (in instanceof DataInputStream) {
            DataInputStream dis = (DataInputStream) in;
            if (dis.bytearr.length < utflen) {
                dis.bytearr = new byte[utflen * 2];
                dis.chararr = new char[utflen * 2];
            }
            chars = dis.chararr;
            bytes = dis.bytearr;
        } else {
            bytes = new byte[utflen];
            chars = new char[utflen];
        }
        in.readFully(bytes, 0, utflen);
        int count = 0;
        int n = 0;
        while (count < utflen) {
            int c = bytes[count] & 0xff;
            switch (c >> 4) {
                case 0: case 1: case 2: case 3: case 4: case 5: case 6: case 7:
                    count++;
                    chars[n++] = (char) c;
                    break;
                case 12: case 13: {
                    count += 2;
                    if (count > utflen) throw new UTFDataFormatException("malformed input: partial character at end");
                    int c2 = bytes[count - 1];
                    if ((c2 & 0xC0) != 0x80) throw new UTFDataFormatException("malformed input around byte " + count);
                    chars[n++] = (char) (((c & 0x1F) << 6) | (c2 & 0x3F));
                    break;
                }
                case 14: {
                    count += 3;
                    if (count > utflen) throw new UTFDataFormatException("malformed input: partial character at end");
                    int c2 = bytes[count - 2];
                    int c3 = bytes[count - 1];
                    if ((c2 & 0xC0) != 0x80 || (c3 & 0xC0) != 0x80)
                        throw new UTFDataFormatException("malformed input around byte " + (count - 1));
                    chars[n++] = (char) (((c & 0x0F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F));
                    break;
                }
                default:
                    throw new UTFDataFormatException("malformed input around byte " + count);
            }
        }
        return new String(chars, 0, n);
    }
}

/*
 * rocq-jvm model of java.util.UUID (clean-room, Apache-2.0), from the Javadoc: two longs; the
 * getters, version/variant and the time-based fields ("Not a time-based UUID"), toString in the
 * 8-4-4-4-12 lower-case hex form, fromString (the 36-character fast form, else the dash-separated
 * groups parsed by Long.parseLong(CharSequence, begin, end, 16), with JDK 21's messages),
 * nameUUIDFromBytes (version 3: MD5 of the bytes, computed here), equals/hashCode/compareTo.
 * Not modelled (STUCK): randomUUID (SecureRandom).
 */
package java.util;

public final class UUID implements java.io.Serializable, Comparable<UUID> {
    private static final long serialVersionUID = -4856846361193249489L;

    private final long mostSigBits;
    private final long leastSigBits;

    public UUID(long mostSigBits, long leastSigBits) {
        this.mostSigBits = mostSigBits;
        this.leastSigBits = leastSigBits;
    }

    public static UUID randomUUID() {
        throw ModelStuck.unsupported("UUID.randomUUID (SecureRandom)");
    }

    public static UUID nameUUIDFromBytes(byte[] name) {
        if (name == null) throw new NullPointerException("Cannot read the array length because \"input\" is null");
        byte[] md5 = md5(name);
        md5[6] &= 0x0f;
        md5[6] |= 0x30;
        md5[8] &= 0x3f;
        md5[8] |= (byte) 0x80;
        long msb = 0, lsb = 0;
        for (int i = 0; i < 8; i++) msb = (msb << 8) | (md5[i] & 0xff);
        for (int i = 8; i < 16; i++) lsb = (lsb << 8) | (md5[i] & 0xff);
        return new UUID(msb, lsb);
    }

    private static final int[] S = {7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
        5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
        4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
        6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21};

    private static final int[] K = {
        0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
        0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
        0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
        0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
        0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
        0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
        0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
        0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391};

    /** RFC 1321. */
    private static byte[] md5(byte[] msg) {
        int n = msg.length;
        int blocks = ((n + 8) >>> 6) + 1;
        byte[] m = new byte[blocks * 64];
        System.arraycopy(msg, 0, m, 0, n);
        m[n] = (byte) 0x80;
        long bits = (long) n * 8;
        for (int i = 0; i < 8; i++) m[m.length - 8 + i] = (byte) (bits >>> (8 * i));
        int a0 = 0x67452301, b0 = 0xefcdab89, c0 = 0x98badcfe, d0 = 0x10325476;
        int[] w = new int[16];
        for (int blk = 0; blk < blocks; blk++) {
            for (int j = 0; j < 16; j++) {
                int o = blk * 64 + j * 4;
                w[j] = (m[o] & 0xff) | (m[o + 1] & 0xff) << 8 | (m[o + 2] & 0xff) << 16 | (m[o + 3] & 0xff) << 24;
            }
            int a = a0, b = b0, c = c0, d = d0;
            for (int i = 0; i < 64; i++) {
                int f, g;
                if (i < 16) { f = (b & c) | (~b & d); g = i; }
                else if (i < 32) { f = (d & b) | (~d & c); g = (5 * i + 1) & 15; }
                else if (i < 48) { f = b ^ c ^ d; g = (3 * i + 5) & 15; }
                else { f = c ^ (b | ~d); g = (7 * i) & 15; }
                f = f + a + K[i] + w[g];
                a = d;
                d = c;
                c = b;
                b = b + Integer.rotateLeft(f, S[i]);
            }
            a0 += a;
            b0 += b;
            c0 += c;
            d0 += d;
        }
        byte[] out = new byte[16];
        int[] h = {a0, b0, c0, d0};
        for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) out[i * 4 + j] = (byte) (h[i] >>> (8 * j));
        return out;
    }

    private static int nibble(char c) {
        if (c >= '0' && c <= '9') return c - '0';
        if (c >= 'a' && c <= 'f') return c - 'a' + 10;
        if (c >= 'A' && c <= 'F') return c - 'A' + 10;
        return -1;
    }

    private static long parse4Nibbles(String name, int pos) {
        char c1 = name.charAt(pos), c2 = name.charAt(pos + 1), c3 = name.charAt(pos + 2), c4 = name.charAt(pos + 3);
        if ((c1 | c2 | c3 | c4) > 0xff) return -1;
        int n1 = nibble(c1), n2 = nibble(c2), n3 = nibble(c3), n4 = nibble(c4);
        return n1 << 12 | n2 << 8 | n3 << 4 | n4;
    }

    public static UUID fromString(String name) {
        if (name == null) throw new NullPointerException("Cannot invoke \"String.length()\" because \"name\" is null");
        if (name.length() == 36) {
            if (name.charAt(8) == '-' && name.charAt(13) == '-' && name.charAt(18) == '-' && name.charAt(23) == '-') {
                long msb1 = parse4Nibbles(name, 0), msb2 = parse4Nibbles(name, 4), msb3 = parse4Nibbles(name, 9),
                     msb4 = parse4Nibbles(name, 14), lsb1 = parse4Nibbles(name, 19), lsb2 = parse4Nibbles(name, 24),
                     lsb3 = parse4Nibbles(name, 28), lsb4 = parse4Nibbles(name, 32);
                if ((msb1 | msb2 | msb3 | msb4 | lsb1 | lsb2 | lsb3 | lsb4) >= 0) {
                    return new UUID(msb1 << 48 | msb2 << 32 | msb3 << 16 | msb4, lsb1 << 48 | lsb2 << 32 | lsb3 << 16 | lsb4);
                }
            }
        }
        int len = name.length();
        if (len > 36) throw new IllegalArgumentException("UUID string too large");
        int dash1 = name.indexOf('-');
        int dash2 = name.indexOf('-', dash1 + 1);
        int dash3 = name.indexOf('-', dash2 + 1);
        int dash4 = name.indexOf('-', dash3 + 1);
        int dash5 = name.indexOf('-', dash4 + 1);
        if (dash4 < 0 || dash5 >= 0) throw new IllegalArgumentException("Invalid UUID string: " + name);
        long mostSigBits = Long.parseLong(name, 0, dash1, 16) & 0xffffffffL;
        mostSigBits <<= 16;
        mostSigBits |= Long.parseLong(name, dash1 + 1, dash2, 16) & 0xffffL;
        mostSigBits <<= 16;
        mostSigBits |= Long.parseLong(name, dash2 + 1, dash3, 16) & 0xffffL;
        long leastSigBits = Long.parseLong(name, dash3 + 1, dash4, 16) & 0xffffL;
        leastSigBits <<= 48;
        leastSigBits |= Long.parseLong(name, dash4 + 1, len, 16) & 0xffffffffffffL;
        return new UUID(mostSigBits, leastSigBits);
    }

    public long getLeastSignificantBits() {
        return leastSigBits;
    }

    public long getMostSignificantBits() {
        return mostSigBits;
    }

    public int version() {
        return (int) ((mostSigBits >> 12) & 0x0f);
    }

    public int variant() {
        return (int) ((leastSigBits >>> (64 - (leastSigBits >>> 62))) & (leastSigBits >> 63));
    }

    public long timestamp() {
        if (version() != 1) throw new UnsupportedOperationException("Not a time-based UUID");
        return (mostSigBits & 0x0FFFL) << 48 | ((mostSigBits >> 16) & 0x0FFFFL) << 32 | mostSigBits >>> 32;
    }

    public int clockSequence() {
        if (version() != 1) throw new UnsupportedOperationException("Not a time-based UUID");
        return (int) ((leastSigBits & 0x3FFF000000000000L) >>> 48);
    }

    public long node() {
        if (version() != 1) throw new UnsupportedOperationException("Not a time-based UUID");
        return leastSigBits & 0x0000FFFFFFFFFFFFL;
    }

    private static void hex(StringBuilder b, long v, int digits) {
        for (int i = digits - 1; i >= 0; i--) {
            int d = (int) ((v >>> (4 * i)) & 0xf);
            b.append((char) (d < 10 ? '0' + d : 'a' + d - 10));
        }
    }

    @Override
    public String toString() {
        StringBuilder b = new StringBuilder(36);
        hex(b, mostSigBits >>> 32, 8);
        b.append('-');
        hex(b, mostSigBits >>> 16, 4);
        b.append('-');
        hex(b, mostSigBits, 4);
        b.append('-');
        hex(b, leastSigBits >>> 48, 4);
        b.append('-');
        hex(b, leastSigBits, 12);
        return b.toString();
    }

    @Override
    public int hashCode() {
        long hilo = mostSigBits ^ leastSigBits;
        return ((int) (hilo >> 32)) ^ (int) hilo;
    }

    @Override
    public boolean equals(Object obj) {
        if ((null == obj) || (obj.getClass() != UUID.class)) return false;
        UUID id = (UUID) obj;
        return mostSigBits == id.mostSigBits && leastSigBits == id.leastSigBits;
    }

    @Override
    public int compareTo(UUID val) {
        if (val == null) throw new NullPointerException("Cannot read field \"mostSigBits\" because \"val\" is null");
        int m = Long.compare(this.mostSigBits, val.mostSigBits);
        return m != 0 ? m : Long.compare(this.leastSigBits, val.leastSigBits);
    }
}

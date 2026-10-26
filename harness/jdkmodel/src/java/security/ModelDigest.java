/*
 * rocq-jvm helper (not a JDK class; clean-room, Apache-2.0): the digest computations of the
 * MessageDigest model: MD5 (RFC 1321), SHA-1 and SHA-2 (FIPS 180-4), over the whole message (the
 * input is collected and hashed at digest()); the DigestBase checks and messages of
 * engineUpdate/engineDigest. HotSpot never loads this class.
 */
package java.security;

final class ModelDigest {
    final String name;
    final int length;
    private byte[] buf = new byte[64];
    private int n;

    ModelDigest(String name) {
        this.name = name;
        switch (name) {
            case "MD5": length = 16; break;
            case "SHA-1": length = 20; break;
            case "SHA-224": case "SHA-512/224": length = 28; break;
            case "SHA-256": case "SHA-512/256": length = 32; break;
            case "SHA-384": length = 48; break;
            default: length = 64; break;
        }
    }

    private static byte[] copyOf(byte[] a, int n) {
        byte[] c = new byte[n];
        System.arraycopy(a, 0, c, 0, Math.min(a.length, n));
        return c;
    }

    ModelDigest copy() {
        ModelDigest d = new ModelDigest(name);
        d.buf = buf.clone();
        d.n = n;
        return d;
    }

    void reset() {
        n = 0;
    }

    void update(byte b) {
        if (n == buf.length) buf = copyOf(buf, n * 2);
        buf[n++] = b;
    }

    void update(byte[] b, int ofs, int len) {
        if (len == 0) return;
        if (ofs < 0 || len < 0 || ofs > b.length - len)
            throw new ArrayIndexOutOfBoundsException("Range [" + ofs + ", " + ofs + " + " + len + ") out of bounds for length " + b.length);
        for (int i = 0; i < len; i++) update(b[ofs + i]);
    }

    byte[] digest() {
        byte[] m = copyOf(buf, n);
        n = 0;
        switch (name) {
            case "MD5": return md5(m);
            case "SHA-1": return sha1(m);
            case "SHA-224": return copyOf(sha256(m, H224), 28);
            case "SHA-256": return sha256(m, H256);
            case "SHA-384": return copyOf(sha512(m, H384), 48);
            case "SHA-512/224": return copyOf(sha512(m, H512_224), 28);
            case "SHA-512/256": return copyOf(sha512(m, H512_256), 32);
            default: return sha512(m, H512);
        }
    }

    int digest(byte[] out, int ofs, int len) throws DigestException {
        if (len < length) throw new DigestException("Length must be at least " + length + " for " + name + "digests");
        if (ofs < 0 || len < 0 || ofs > out.length - len) throw new DigestException("Buffer too short to store digest");
        byte[] d = digest();
        System.arraycopy(d, 0, out, ofs, length);
        return length;
    }

    /** The message padded to whole blocks with the bit length (big- or little-endian). */
    private static byte[] pad(byte[] msg, int block, int lenBytes, boolean little) {
        int n = msg.length;
        int total = ((n + 1 + lenBytes + block - 1) / block) * block;
        byte[] m = new byte[total];
        System.arraycopy(msg, 0, m, 0, n);
        m[n] = (byte) 0x80;
        long bits = (long) n * 8;
        for (int i = 0; i < 8; i++) {
            byte v = (byte) (bits >>> (8 * i));
            if (little) m[total - 8 + i] = v;
            else m[total - 1 - i] = v;
        }
        return m;
    }

    private static final int[] MD5K = {
        0xd76aa478, 0xe8c7b756, 0x242070db, 0xc1bdceee, 0xf57c0faf, 0x4787c62a, 0xa8304613, 0xfd469501,
        0x698098d8, 0x8b44f7af, 0xffff5bb1, 0x895cd7be, 0x6b901122, 0xfd987193, 0xa679438e, 0x49b40821,
        0xf61e2562, 0xc040b340, 0x265e5a51, 0xe9b6c7aa, 0xd62f105d, 0x02441453, 0xd8a1e681, 0xe7d3fbc8,
        0x21e1cde6, 0xc33707d6, 0xf4d50d87, 0x455a14ed, 0xa9e3e905, 0xfcefa3f8, 0x676f02d9, 0x8d2a4c8a,
        0xfffa3942, 0x8771f681, 0x6d9d6122, 0xfde5380c, 0xa4beea44, 0x4bdecfa9, 0xf6bb4b60, 0xbebfbc70,
        0x289b7ec6, 0xeaa127fa, 0xd4ef3085, 0x04881d05, 0xd9d4d039, 0xe6db99e5, 0x1fa27cf8, 0xc4ac5665,
        0xf4292244, 0x432aff97, 0xab9423a7, 0xfc93a039, 0x655b59c3, 0x8f0ccc92, 0xffeff47d, 0x85845dd1,
        0x6fa87e4f, 0xfe2ce6e0, 0xa3014314, 0x4e0811a1, 0xf7537e82, 0xbd3af235, 0x2ad7d2bb, 0xeb86d391};

    private static final int[] MD5S = {7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22,
        5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20, 5, 9, 14, 20,
        4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23,
        6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21};

    private static byte[] md5(byte[] msg) {
        byte[] m = pad(msg, 64, 8, true);
        int a0 = 0x67452301, b0 = 0xefcdab89, c0 = 0x98badcfe, d0 = 0x10325476;
        int[] w = new int[16];
        for (int blk = 0; blk < m.length; blk += 64) {
            for (int j = 0; j < 16; j++) {
                int o = blk + j * 4;
                w[j] = (m[o] & 0xff) | (m[o + 1] & 0xff) << 8 | (m[o + 2] & 0xff) << 16 | (m[o + 3] & 0xff) << 24;
            }
            int a = a0, b = b0, c = c0, d = d0;
            for (int i = 0; i < 64; i++) {
                int f, g;
                if (i < 16) { f = (b & c) | (~b & d); g = i; }
                else if (i < 32) { f = (d & b) | (~d & c); g = (5 * i + 1) & 15; }
                else if (i < 48) { f = b ^ c ^ d; g = (3 * i + 5) & 15; }
                else { f = c ^ (b | ~d); g = (7 * i) & 15; }
                f = f + a + MD5K[i] + w[g];
                a = d;
                d = c;
                c = b;
                b = b + Integer.rotateLeft(f, MD5S[i]);
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

    private static byte[] sha1(byte[] msg) {
        byte[] m = pad(msg, 64, 8, false);
        int[] h = {0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0};
        int[] w = new int[80];
        for (int blk = 0; blk < m.length; blk += 64) {
            for (int t = 0; t < 16; t++) {
                int o = blk + 4 * t;
                w[t] = (m[o] & 0xff) << 24 | (m[o + 1] & 0xff) << 16 | (m[o + 2] & 0xff) << 8 | (m[o + 3] & 0xff);
            }
            for (int t = 16; t < 80; t++) w[t] = Integer.rotateLeft(w[t - 3] ^ w[t - 8] ^ w[t - 14] ^ w[t - 16], 1);
            int a = h[0], b = h[1], c = h[2], d = h[3], e = h[4];
            for (int t = 0; t < 80; t++) {
                int f, k;
                if (t < 20) { f = (b & c) | (~b & d); k = 0x5A827999; }
                else if (t < 40) { f = b ^ c ^ d; k = 0x6ED9EBA1; }
                else if (t < 60) { f = (b & c) | (b & d) | (c & d); k = 0x8F1BBCDC; }
                else { f = b ^ c ^ d; k = 0xCA62C1D6; }
                int tmp = Integer.rotateLeft(a, 5) + f + e + k + w[t];
                e = d;
                d = c;
                c = Integer.rotateLeft(b, 30);
                b = a;
                a = tmp;
            }
            h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e;
        }
        byte[] out = new byte[20];
        for (int i = 0; i < 5; i++) for (int j = 0; j < 4; j++) out[4 * i + j] = (byte) (h[i] >>> (24 - 8 * j));
        return out;
    }

    private static final int[] K256 = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};
    private static final int[] H256 = {
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    private static final int[] H224 = {
        0xc1059ed8, 0x367cd507, 0x3070dd17, 0xf70e5939, 0xffc00b31, 0x68581511, 0x64f98fa7, 0xbefa4fa4};

    private static byte[] sha256(byte[] msg, int[] init) {
        byte[] m = pad(msg, 64, 8, false);
        int[] h = init.clone();
        int[] w = new int[64];
        for (int blk = 0; blk < m.length; blk += 64) {
            for (int t = 0; t < 16; t++) {
                int o = blk + 4 * t;
                w[t] = (m[o] & 0xff) << 24 | (m[o + 1] & 0xff) << 16 | (m[o + 2] & 0xff) << 8 | (m[o + 3] & 0xff);
            }
            for (int t = 16; t < 64; t++) {
                int s0 = Integer.rotateRight(w[t - 15], 7) ^ Integer.rotateRight(w[t - 15], 18) ^ (w[t - 15] >>> 3);
                int s1 = Integer.rotateRight(w[t - 2], 17) ^ Integer.rotateRight(w[t - 2], 19) ^ (w[t - 2] >>> 10);
                w[t] = w[t - 16] + s0 + w[t - 7] + s1;
            }
            int a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
            for (int t = 0; t < 64; t++) {
                int S1 = Integer.rotateRight(e, 6) ^ Integer.rotateRight(e, 11) ^ Integer.rotateRight(e, 25);
                int ch = (e & f) ^ (~e & g);
                int t1 = hh + S1 + ch + K256[t] + w[t];
                int S0 = Integer.rotateRight(a, 2) ^ Integer.rotateRight(a, 13) ^ Integer.rotateRight(a, 22);
                int maj = (a & b) ^ (a & c) ^ (b & c);
                int t2 = S0 + maj;
                hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
            }
            h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
        }
        byte[] out = new byte[32];
        for (int i = 0; i < 8; i++) for (int j = 0; j < 4; j++) out[4 * i + j] = (byte) (h[i] >>> (24 - 8 * j));
        return out;
    }

    private static final long[] K512 = {
        0x428a2f98d728ae22L, 0x7137449123ef65cdL, 0xb5c0fbcfec4d3b2fL, 0xe9b5dba58189dbbcL,
        0x3956c25bf348b538L, 0x59f111f1b605d019L, 0x923f82a4af194f9bL, 0xab1c5ed5da6d8118L,
        0xd807aa98a3030242L, 0x12835b0145706fbeL, 0x243185be4ee4b28cL, 0x550c7dc3d5ffb4e2L,
        0x72be5d74f27b896fL, 0x80deb1fe3b1696b1L, 0x9bdc06a725c71235L, 0xc19bf174cf692694L,
        0xe49b69c19ef14ad2L, 0xefbe4786384f25e3L, 0x0fc19dc68b8cd5b5L, 0x240ca1cc77ac9c65L,
        0x2de92c6f592b0275L, 0x4a7484aa6ea6e483L, 0x5cb0a9dcbd41fbd4L, 0x76f988da831153b5L,
        0x983e5152ee66dfabL, 0xa831c66d2db43210L, 0xb00327c898fb213fL, 0xbf597fc7beef0ee4L,
        0xc6e00bf33da88fc2L, 0xd5a79147930aa725L, 0x06ca6351e003826fL, 0x142929670a0e6e70L,
        0x27b70a8546d22ffcL, 0x2e1b21385c26c926L, 0x4d2c6dfc5ac42aedL, 0x53380d139d95b3dfL,
        0x650a73548baf63deL, 0x766a0abb3c77b2a8L, 0x81c2c92e47edaee6L, 0x92722c851482353bL,
        0xa2bfe8a14cf10364L, 0xa81a664bbc423001L, 0xc24b8b70d0f89791L, 0xc76c51a30654be30L,
        0xd192e819d6ef5218L, 0xd69906245565a910L, 0xf40e35855771202aL, 0x106aa07032bbd1b8L,
        0x19a4c116b8d2d0c8L, 0x1e376c085141ab53L, 0x2748774cdf8eeb99L, 0x34b0bcb5e19b48a8L,
        0x391c0cb3c5c95a63L, 0x4ed8aa4ae3418acbL, 0x5b9cca4f7763e373L, 0x682e6ff3d6b2b8a3L,
        0x748f82ee5defb2fcL, 0x78a5636f43172f60L, 0x84c87814a1f0ab72L, 0x8cc702081a6439ecL,
        0x90befffa23631e28L, 0xa4506cebde82bde9L, 0xbef9a3f7b2c67915L, 0xc67178f2e372532bL,
        0xca273eceea26619cL, 0xd186b8c721c0c207L, 0xeada7dd6cde0eb1eL, 0xf57d4f7fee6ed178L,
        0x06f067aa72176fbaL, 0x0a637dc5a2c898a6L, 0x113f9804bef90daeL, 0x1b710b35131c471bL,
        0x28db77f523047d84L, 0x32caab7b40c72493L, 0x3c9ebe0a15c9bebcL, 0x431d67c49c100d4cL,
        0x4cc5d4becb3e42b6L, 0x597f299cfc657e2aL, 0x5fcb6fab3ad6faecL, 0x6c44198c4a475817L};
    private static final long[] H512 = {
        0x6a09e667f3bcc908L, 0xbb67ae8584caa73bL, 0x3c6ef372fe94f82bL, 0xa54ff53a5f1d36f1L,
        0x510e527fade682d1L, 0x9b05688c2b3e6c1fL, 0x1f83d9abfb41bd6bL, 0x5be0cd19137e2179L};
    private static final long[] H384 = {
        0xcbbb9d5dc1059ed8L, 0x629a292a367cd507L, 0x9159015a3070dd17L, 0x152fecd8f70e5939L,
        0x67332667ffc00b31L, 0x8eb44a8768581511L, 0xdb0c2e0d64f98fa7L, 0x47b5481dbefa4fa4L};
    private static final long[] H512_224 = {
        0x8C3D37C819544DA2L, 0x73E1996689DCD4D6L, 0x1DFAB7AE32FF9C82L, 0x679DD514582F9FCFL,
        0x0F6D2B697BD44DA8L, 0x77E36F7304C48942L, 0x3F9D85A86A1D36C8L, 0x1112E6AD91D692A1L};
    private static final long[] H512_256 = {
        0x22312194FC2BF72CL, 0x9F555FA3C84C64C2L, 0x2393B86B6F53B151L, 0x963877195940EABDL,
        0x96283EE2A88EFFE3L, 0xBE5E1E2553863992L, 0x2B0199FC2C85B8AAL, 0x0EB72DDC81C52CA2L};

    private static byte[] sha512(byte[] msg, long[] init) {
        byte[] m = pad(msg, 128, 16, false);
        long[] h = init.clone();
        long[] w = new long[80];
        for (int blk = 0; blk < m.length; blk += 128) {
            for (int t = 0; t < 16; t++) {
                long v = 0;
                for (int j = 0; j < 8; j++) v = (v << 8) | (m[blk + 8 * t + j] & 0xff);
                w[t] = v;
            }
            for (int t = 16; t < 80; t++) {
                long s0 = Long.rotateRight(w[t - 15], 1) ^ Long.rotateRight(w[t - 15], 8) ^ (w[t - 15] >>> 7);
                long s1 = Long.rotateRight(w[t - 2], 19) ^ Long.rotateRight(w[t - 2], 61) ^ (w[t - 2] >>> 6);
                w[t] = w[t - 16] + s0 + w[t - 7] + s1;
            }
            long a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
            for (int t = 0; t < 80; t++) {
                long S1 = Long.rotateRight(e, 14) ^ Long.rotateRight(e, 18) ^ Long.rotateRight(e, 41);
                long ch = (e & f) ^ (~e & g);
                long t1 = hh + S1 + ch + K512[t] + w[t];
                long S0 = Long.rotateRight(a, 28) ^ Long.rotateRight(a, 34) ^ Long.rotateRight(a, 39);
                long maj = (a & b) ^ (a & c) ^ (b & c);
                long t2 = S0 + maj;
                hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
            }
            h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
        }
        byte[] out = new byte[64];
        for (int i = 0; i < 8; i++) for (int j = 0; j < 8; j++) out[8 * i + j] = (byte) (h[i] >>> (56 - 8 * j));
        return out;
    }
}

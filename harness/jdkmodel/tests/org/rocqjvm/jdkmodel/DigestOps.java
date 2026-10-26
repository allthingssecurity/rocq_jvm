package org.rocqjvm.jdkmodel;

import java.security.DigestException;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;

/** Differential tests of java.security.MessageDigest (MD5, SHA-1, SHA-2): names and aliases, streaming
 *  updates, digest variants, reset, clone, toString, isEqual and the argument errors. */
public final class DigestOps {
    private DigestOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static final String[] NAMES = {"MD5", "md5", "SHA-1", "SHA", "sha1", "SHA-224", "SHA-256", "sha256", "SHA-384", "SHA-512",
        "SHA-512/224", "SHA512/256", "nope", "", "SHA-2"};

    static String hex(byte[] b) {
        StringBuilder o = new StringBuilder();
        for (byte x : b) o.append(Character.forDigit((x >> 4) & 15, 16)).append(Character.forDigit(x & 15, 16));
        return o.toString();
    }

    public static String digests(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 4; k++) {
            try {
                MessageDigest md = MessageDigest.getInstance(NAMES[r(NAMES.length)]);
                out.append(md.getAlgorithm()).append(md.getDigestLength()).append(md.toString()).append(md.getClass().getName());
                byte[] data = new byte[r(r(4) == 0 ? 400 : 70)];
                for (int i = 0; i < data.length; i++) data[i] = (byte) r(256);
                int pos = 0;
                while (pos < data.length) {
                    int c = Math.min(data.length - pos, r(90));
                    if (r(4) == 0) { md.update(data[pos]); c = 1; }
                    else md.update(data, pos, c);
                    pos += c;
                }
                out.append(md);
                MessageDigest cl = (MessageDigest) md.clone();
                byte[] d1 = md.digest();
                out.append(hex(d1)).append('|').append(hex(cl.digest(new byte[]{1, 2, 3}))).append('|').append(hex(md.digest()));
                md.update(data);
                md.reset();
                out.append(hex(md.digest(data))).append(MessageDigest.isEqual(d1, cl.digest())).append(MessageDigest.isEqual(d1, d1.clone()));
                byte[] buf = new byte[r(80)];
                try {
                    out.append(md.digest(buf, r(6) - 1, r(70) - 2)).append(hex(buf));
                } catch (DigestException | IllegalArgumentException x) {
                    out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
                }
                try {
                    switch (r(4)) {
                        case 0: md.update(null, 0, 1); break;
                        case 1: md.update(new byte[3], r(5) - 1, r(6) - 2); break;
                        case 2: md.update((byte[]) null); break;
                        default: try { md.digest(null, 0, 0); } catch (DigestException x) { out.append("!DE"); } break;
                    }
                    out.append(hex(md.digest()));
                } catch (RuntimeException x) {
                    out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
                }
            } catch (NoSuchAlgorithmException | CloneNotSupportedException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        try {
            MessageDigest.getInstance(null);
        } catch (NullPointerException | NoSuchAlgorithmException x) {
            out.append(x.getMessage());
        }
        out.append(MessageDigest.isEqual(null, new byte[0])).append(MessageDigest.isEqual(new byte[0], new byte[0])).append(MessageDigest.isEqual(new byte[]{1}, new byte[0]));
        return out.toString();
    }
}

package org.rocqjvm.jdkmodel;

import java.util.UUID;

/** Differential tests of java.util.UUID: constructors, fromString (fast and general forms, errors),
 *  toString, version/variant/time fields, nameUUIDFromBytes (MD5), equals/hashCode/compareTo. */
public final class UuidOps {
    private UuidOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static long rl() { return ((long) r(1 << 22) << 42) ^ ((long) r(1 << 22) << 20) ^ r(1 << 20); }

    static String text() {
        String hex = "0123456789abcdefABCDEF";
        switch (r(5)) {
            case 0: return new UUID(rl(), rl()).toString();
            case 1: return new UUID(rl(), rl()).toString().toUpperCase();
            case 2: { StringBuilder b = new StringBuilder();
                      int[] gs = {1 + r(9), 1 + r(5), 1 + r(5), 1 + r(5), 1 + r(13)};
                      for (int g = 0; g < 5; g++) { if (g > 0) b.append('-'); for (int i = 0; i < gs[g]; i++) b.append(hex.charAt(r(hex.length()))); }
                      return b.toString(); }
            case 3: { String[] e = {"", "-", "----", "-----", "1-2-3-4-5", "0-0-0-0-0-0", "g-0-0-0-0", "+1-2-3-4-5", "123456789-1-1-1-1",
                                    "1-1-1-1-1234567890123", "00000000-0000-0000-0000-00000000000g", "00000000-0000-0000-0000-0000000000000",
                                    "１-2-3-4-5", "00000000-0000-1000-8000-00805f9b34fb", null};
                      return e[r(e.length)]; }
            default: { char[] c = new UUID(rl(), rl()).toString().toCharArray(); c[r(36)] = "-xZĀ 9".charAt(r(6)); return new String(c); }
        }
    }

    public static String uuids(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 8; k++) {
            try {
                UUID u = UUID.fromString(text());
                UUID v = r(2) == 0 ? u : new UUID(rl() & (r(2) == 0 ? -1L : 0xffffffffffff0fffL | 0x1000L), rl());
                out.append(u).append('|').append(u.getMostSignificantBits()).append(',').append(u.getLeastSignificantBits()).append('|')
                   .append(u.version()).append(u.variant()).append('|').append(u.hashCode()).append(u.equals(v)).append(u.equals(null))
                   .append(u.compareTo(v)).append('|');
                try {
                    out.append(v.timestamp()).append(',').append(v.clockSequence()).append(',').append(v.node());
                } catch (UnsupportedOperationException x) {
                    out.append("!UOE:").append(x.getMessage());
                }
                if (r(5) == 0) out.append(u.compareTo(null));
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        byte[] b = new byte[r(130)];
        for (int i = 0; i < b.length; i++) b[i] = (byte) r(256);
        out.append(UUID.nameUUIDFromBytes(b)).append(UUID.nameUUIDFromBytes(new byte[0])).append(UUID.nameUUIDFromBytes("abc".getBytes()));
        try {
            UUID.nameUUIDFromBytes(null);
        } catch (NullPointerException x) {
            out.append(x.getMessage());
        }
        return out.toString();
    }
}

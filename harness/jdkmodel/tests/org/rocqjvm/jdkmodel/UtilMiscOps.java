package org.rocqjvm.jdkmodel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.StringTokenizer;
import java.util.random.RandomGenerator;
import java.util.zip.Adler32;
import java.util.zip.CRC32;
import java.util.zip.CRC32C;
import java.util.zip.Checksum;

/** Differential tests of java.util.StringTokenizer, the java.util.zip checksums, and
 *  java.util.Random with a seed (with Collections.shuffle / swap). */
public final class UtilMiscOps {
    private UtilMiscOps() {
    }

    static int s;

    static int r(int n) {
        s = s * 1103515245 + 12345;
        return ((s >>> 8) & 0x7fffff) % n;
    }

    static final String[] TPIECES = {"a", "bc", " ", ",", ";", "\t", "\n", "x y", ",,", "😀", "\ud800", "\udc00", "é", "q"};
    static final String[] DELIMS = {" ", ",", ",;", " \t\n", "😀", "\ud800", "a", "", "\udc00,", ";"};

    static String rstr(int max) {
        StringBuilder b = new StringBuilder();
        for (int i = r(max + 1); i > 0; i--) b.append(TPIECES[r(TPIECES.length)]);
        return b.toString();
    }

    static String rdelim() {
        return r(10) == 0 ? null : DELIMS[r(DELIMS.length)];
    }

    public static String tokenizer(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        StringTokenizer t;
        try {
            String str = r(12) == 0 ? null : rstr(8);
            switch (r(3)) {
                case 0: t = new StringTokenizer(str); break;
                case 1: t = new StringTokenizer(str, rdelim()); break;
                default: t = new StringTokenizer(str, rdelim(), r(2) == 0); break;
            }
        } catch (RuntimeException e) {
            IoOps.exc(out, e);
            return out.toString();
        }
        int ops = 3 + r(12);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(8)) {
                    case 0: case 1: out.append(t.hasMoreTokens()); break;
                    case 2: case 3: case 4: out.append('[').append(IoOps.esc(t.nextToken())).append(']'); break;
                    case 5: out.append('<').append(IoOps.esc(t.nextToken(rdelim()))).append('>'); break;
                    case 6: out.append(t.countTokens()); break;
                    default: out.append(t.hasMoreElements()).append(IoOps.esc((String) t.nextElement())); break;
                }
            } catch (RuntimeException e) {
                IoOps.exc(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String checksums(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        Checksum[] cs = {new CRC32(), new Adler32(), new CRC32C()};
        int ops = 3 + r(12);
        for (int k = 0; k < ops; k++) {
            Checksum c = cs[r(3)];
            try {
                switch (r(7)) {
                    case 0: c.update(r(1000) - 300); break;
                    case 1: case 2: { byte[] b = new byte[r(40)]; for (int i = 0; i < b.length; i++) b[i] = (byte) r(256); c.update(b); break; }
                    case 3: { byte[] b = new byte[r(8)]; for (int i = 0; i < b.length; i++) b[i] = (byte) r(256); c.update(r(9) == 0 ? null : b, r(5) - 1, r(6) - 1); break; }
                    case 4: c.reset(); break;
                    case 5: if (r(3) == 0) c.update((byte[]) null); else c.update(new byte[0]); break;
                    default: out.append(Long.toHexString(c.getValue())); break;
                }
            } catch (RuntimeException e) {
                IoOps.exc(out, e);
            }
            out.append(';');
        }
        for (Checksum c : cs) out.append(c.getValue()).append(',');
        return out.toString();
    }

    /** A Random subclass with its own next(bits) and a counting setSeed. */
    static final class Mine extends Random {
        int seeds;

        Mine(long seed) {
            super(seed);
        }

        public synchronized void setSeed(long seed) {
            seeds++;
            super.setSeed(seed + 1);
        }

        protected int next(int bits) {
            return super.next(bits) ^ (bits == 32 ? 0x55 : 0);
        }
    }

    public static String random(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        long sd = (long) seed * (r(1000) - 500) + r(7);
        Random rnd = r(4) == 0 ? new Mine(sd) : new Random(sd);
        RandomGenerator g = rnd;
        int ops = 4 + r(14);
        for (int k = 0; k < ops; k++) {
            try {
                switch (r(22)) {
                    case 0: case 1: out.append(rnd.nextInt()); break;
                    case 2: case 3: out.append(rnd.nextInt(r(4) == 0 ? r(5) - 2 : r(3) == 0 ? 1 << r(31) : 1 + r(1000000))); break;
                    case 4: out.append(rnd.nextInt(r(20) - 10, r(4) == 0 ? r(20) - 10 : 1 << r(31))); break;
                    case 5: out.append(rnd.nextInt(Integer.MIN_VALUE + r(3), Integer.MAX_VALUE - r(3))); break;
                    case 6: out.append(rnd.nextLong()); break;
                    case 7: out.append(rnd.nextLong(r(4) == 0 ? r(3) - 1 : (long) r(1000000) * 1000003L + 1)); break;
                    case 8: out.append(rnd.nextLong(-(long) r(100000) * 77777L, r(5) == 0 ? -5 : (long) r(1000) << r(50))); break;
                    case 9: out.append(rnd.nextBoolean()); break;
                    case 10: out.append(rnd.nextFloat()); break;
                    case 11: out.append(rnd.nextFloat(r(5) == 0 ? -1f : r(5) == 0 ? Float.POSITIVE_INFINITY : r(100) / 7f + 0.01f)); break;
                    case 12: out.append(rnd.nextFloat(r(10) - 5f, r(6) == 0 ? -10f : r(10) * 3f)); break;
                    case 13: out.append(rnd.nextDouble()); break;
                    case 14: out.append(rnd.nextDouble(r(5) == 0 ? 0.0 : r(5) == 0 ? Double.NaN : r(1000) / 3.0 + 1e-9)); break;
                    case 15: out.append(rnd.nextDouble(r(5) == 0 ? -Double.MAX_VALUE : r(10) - 5.0, r(5) == 0 ? Double.MAX_VALUE : r(10) * 1.5)); break;
                    case 16: { byte[] b = new byte[r(11)]; rnd.nextBytes(b); out.append(IoOps.hex(b)); break; }
                    case 17: { rnd.setSeed((long) r(100000) - 50000); out.append('S'); break; }
                    case 18: { out.append(g.nextInt(r(7) + 1)).append('/').append(g.nextBoolean()); break; }
                    case 19: case 20: {
                        List<Integer> l = r(2) == 0 ? new ArrayList<>() : new LinkedList<>();
                        for (int i = r(9); i > 0; i--) l.add(i);
                        Collections.shuffle(r(10) == 0 ? null : l, r(10) == 0 ? null : rnd);
                        out.append(l);
                        break;
                    }
                    default: {
                        List<String> l = new ArrayList<>(List.of("a", "b", "c"));
                        Collections.swap(r(10) == 0 ? null : l, r(4) - 1, r(3));
                        out.append(l);
                        break;
                    }
                }
            } catch (RuntimeException e) {
                IoOps.exc(out, e);
            }
            out.append(';');
        }
        if (rnd instanceof Mine) out.append(((Mine) rnd).seeds);
        return out.toString();
    }
}

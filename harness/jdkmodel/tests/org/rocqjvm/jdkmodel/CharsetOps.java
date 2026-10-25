package org.rocqjvm.jdkmodel;

import java.io.UnsupportedEncodingException;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;

/** Differential tests of String <-> bytes (UTF-8 with malformed input, ISO-8859-1, US-ASCII,
 *  UTF-16/BE/LE), the String constructors from char[]/StringBuilder/String, Charset lookup and
 *  names, and the Double/Float boxes (no decimal conversion). */
public final class CharsetOps {
    private CharsetOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static final Charset[] CS = {StandardCharsets.UTF_8, StandardCharsets.ISO_8859_1, StandardCharsets.US_ASCII,
        StandardCharsets.UTF_16, StandardCharsets.UTF_16BE, StandardCharsets.UTF_16LE};
    static final String[] NAMES = {"UTF-8", "utf8", "latin1", "ISO-8859-1", "us", "ASCII", "UTF-16", "UnicodeBig",
        "x-utf-16le", "UTF_16BE", "", "-x", "bad name", "UNICODE-1-1-UTF-8"};

    static String hex(byte[] b) {
        StringBuilder sb = new StringBuilder();
        for (byte x : b) sb.append(Integer.toHexString(x & 0xff)).append(' ');
        return sb.toString();
    }

    static String units(String t) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < t.length(); i++) sb.append(Integer.toHexString(t.charAt(i))).append(' ');
        return sb.toString();
    }

    static byte[] bytes() {
        byte[] b = new byte[r(9)];
        int[] pool = {0x41, 0x7a, 0x00, 0xc3, 0xa9, 0xe2, 0x82, 0xac, 0xf0, 0x9f, 0x98, 0x80, 0xed, 0xa0, 0x80, 0xff, 0xfe, 0xc0, 0x80, 0xbf, 0xf4, 0x90, 0xe0};
        for (int i = 0; i < b.length; i++) b[i] = (byte) (r(3) == 0 ? r(256) : pool[r(pool.length)]);
        return b;
    }

    static String str() {
        char[] pool = {'a', 'Z', '0', 'é', 'ÿ', 'Ā', '€', '\ud83d', '\ude00', '\ud800', '\udfff', '﻿', '￾'};
        StringBuilder sb = new StringBuilder();
        for (int i = r(7); i > 0; i--) sb.append(pool[r(pool.length)]);
        return sb.toString();
    }

    public static String codecs(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                Charset cs = CS[r(CS.length)];
                switch (r(6)) {
                    case 0: out.append(hex(str().getBytes(cs))); break;
                    case 1: out.append(units(new String(bytes(), cs))); break;
                    case 2: { byte[] b = bytes(); out.append(units(new String(b, r(4) - 1, r(6) - 1, cs))); break; }
                    case 3: { String t = str(); out.append(units(new String(t.getBytes(cs), cs))).append(units(t)); break; }
                    case 4: out.append(hex(str().getBytes())).append(units(new String(bytes()))); break;
                    default: out.append(units(new String(bytes(), NAMES[r(NAMES.length)]))); break;
                }
            } catch (RuntimeException | UnsupportedEncodingException e) {
                out.append('!').append(e.getClass().getName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String names(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 5; k++) {
            try {
                String n = NAMES[r(NAMES.length)];
                switch (r(5)) {
                    case 0: { Charset c = Charset.forName(n); out.append(c).append(c.name()).append(new java.util.TreeSet<>(c.aliases())).append(c.aliases().size()).append(c.getClass().getName()); break; }
                    case 1: out.append(Charset.forName(n).equals(CS[r(CS.length)])).append(Charset.forName(n).hashCode()); break;
                    case 2: out.append(Charset.isSupported(n)).append(Charset.defaultCharset()); break;
                    case 3: out.append(Charset.forName(n).compareTo(StandardCharsets.UTF_16)).append(Charset.forName(n).isRegistered()); break;
                    default: out.append(hex("xé".getBytes(n))); break;
                }
            } catch (RuntimeException | UnsupportedEncodingException e) {
                out.append('!').append(e.getClass().getName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String ctors(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        char[] c = str().toCharArray();
        for (int k = 0; k < 5; k++) {
            try {
                switch (r(7)) {
                    case 0: out.append(units(new String(c))); break;
                    case 1: out.append(units(new String(c, r(4) - 1, r(5) - 1))); break;
                    case 2: out.append(units(String.valueOf(c, r(3), r(4)))).append(units(String.copyValueOf(c))); break;
                    case 3: out.append(new String(new StringBuilder("sb").append(k))).append(new String("lit") == "lit"); break;
                    case 4: out.append(new String().isEmpty()).append(new String((char[]) null)); break;
                    case 5: out.append(new String((String) null)); break;
                    default: out.append(new String(new byte[] {104, 105}, (Charset) null)); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String doubles(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        double[] ds = {0.0, -0.0, 1.5, -2.25, Double.NaN, Double.POSITIVE_INFINITY, Double.NEGATIVE_INFINITY, 1e300, 3.0e-320, 7};
        for (int k = 0; k < 6; k++) {
            double a = ds[r(ds.length)], b = ds[r(ds.length)];
            Double x = a, y = b;
            Float f = (float) a;
            out.append(x.equals(y)).append(x.hashCode()).append(x.compareTo(y)).append(Double.compare(a, b))
               .append(Double.isNaN(a)).append(x.isInfinite()).append(Double.isFinite(b))
               .append(Double.doubleToLongBits(a)).append(x.intValue()).append(x.longValue())
               .append(f.hashCode()).append(f.equals((float) b)).append(Float.compare((float) a, (float) b))
               .append(Float.floatToIntBits((float) a)).append(Double.longBitsToDouble(Double.doubleToLongBits(a)) == a)
               .append(Double.hashCode(b)).append(';');
        }
        return out.toString();
    }
}

package org.rocqjvm.jdkmodel;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.Base64;

/** Differential tests of java.util.Base64: the basic / URL / MIME encoders (custom line lengths
 *  and separators, without padding), decoding of well-formed and corrupted input with the JDK's
 *  messages, the sized encode/decode, and the wrapping streams. */
public final class Base64Ops {
    private Base64Ops() {
    }

    static int s;

    static int r(int n) {
        s = s * 1103515245 + 12345;
        return ((s >>> 8) & 0x7fffff) % n;
    }

    static byte[] rbytes(int max) {
        int n = r(max + 1);
        byte[] b = new byte[n];
        for (int i = 0; i < n; i++) b[i] = (byte) r(256);
        return b;
    }

    static final String[] SEPS = {"\r\n", "\n", "", "#", "=", "A", "-", "ÿ", ";;"};

    static Base64.Encoder encoder(StringBuilder out) {
        Base64.Encoder e;
        switch (r(5)) {
            case 0: e = Base64.getEncoder(); break;
            case 1: e = Base64.getUrlEncoder(); break;
            case 2: e = Base64.getMimeEncoder(); break;
            default: {
                String sep = r(8) == 0 ? null : SEPS[r(SEPS.length)];
                int len = r(24) - 4;
                out.append("mime(").append(len).append(',').append(IoOps.esc(sep)).append(')');
                e = Base64.getMimeEncoder(len, sep == null ? null : sep.getBytes(java.nio.charset.StandardCharsets.ISO_8859_1));
                break;
            }
        }
        if (r(3) == 0) e = e.withoutPadding();
        return e;
    }

    static Base64.Decoder decoder() {
        switch (r(3)) {
            case 0: return Base64.getDecoder();
            case 1: return Base64.getUrlDecoder();
            default: return Base64.getMimeDecoder();
        }
    }

    static final String NOISE = "=\n\r-_+/*A0 ÿ.";

    static String corrupt(String t) {
        StringBuilder b = new StringBuilder(t);
        for (int i = r(3); i > 0; i--) {
            int at = r(b.length() + 1);
            char c = NOISE.charAt(r(NOISE.length()));
            switch (r(3)) {
                case 0: b.insert(at, c); break;
                case 1: if (at < b.length()) b.deleteCharAt(at); break;
                default: if (at < b.length()) { b.deleteCharAt(at); b.insert(at, c); } break;
            }
        }
        return b.toString();
    }

    static void exc(StringBuilder out, Throwable e) {
        IoOps.exc(out, e);
    }

    public static String codec(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int rounds = 1 + r(4);
        for (int k = 0; k < rounds; k++) {
            try {
                byte[] src = rbytes(r(4) == 0 ? 70 : 12);
                Base64.Encoder e = encoder(out);
                String enc;
                switch (r(3)) {
                    case 0: enc = e.encodeToString(src); break;
                    case 1: enc = new String(e.encode(src), java.nio.charset.StandardCharsets.ISO_8859_1); break;
                    default: {
                        byte[] dst = new byte[r(4) == 0 ? r(20) : 120];
                        int n = e.encode(src, dst);
                        enc = new String(dst, 0, n, java.nio.charset.StandardCharsets.ISO_8859_1);
                        break;
                    }
                }
                out.append(IoOps.esc(enc)).append("->");
                String in = r(3) == 0 ? corrupt(enc) : enc;
                Base64.Decoder d = decoder();
                byte[] dec;
                switch (r(3)) {
                    case 0: dec = d.decode(in); break;
                    case 1: dec = d.decode(in.getBytes(java.nio.charset.StandardCharsets.ISO_8859_1)); break;
                    default: {
                        byte[] dst = new byte[r(4) == 0 ? r(12) : 100];
                        int n = d.decode(in.getBytes(java.nio.charset.StandardCharsets.ISO_8859_1), dst);
                        dec = new byte[n];
                        System.arraycopy(dst, 0, dec, 0, n);
                        break;
                    }
                }
                out.append(IoOps.hex(dec)).append(dec.length == src.length);
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    /** Decoding of short random strings over the base64 alphabets and the padding. */
    public static String decodeOnly(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        String alpha = "ABCDabcd0189+/-_=\n\r *ÿ";
        int rounds = 2 + r(5);
        for (int k = 0; k < rounds; k++) {
            StringBuilder b = new StringBuilder();
            for (int i = r(10); i > 0; i--) b.append(alpha.charAt(r(alpha.length())));
            if (r(2) == 0) b.append("==".substring(r(3) == 0 ? 0 : 1));
            try {
                out.append(IoOps.esc(b.toString())).append("->").append(IoOps.hex(decoder().decode(b.toString())));
            } catch (Exception e) {
                exc(out, e);
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String streams(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        try {
            IoOps.Log lo = new IoOps.Log(r(5) == 0 ? r(6) : -1);
            Base64.Encoder e = encoder(out);
            OutputStream os = e.wrap(r(10) == 0 ? null : lo);
            int ops = 1 + r(6);
            for (int k = 0; k < ops; k++) {
                try {
                    switch (r(5)) {
                        case 0: os.write(r(256)); break;
                        case 1: case 2: { byte[] b = rbytes(10); os.write(b, r(3) - 1, r(b.length + 2) - 1); break; }
                        case 3: os.write(rbytes(8)); break;
                        default: os.close(); out.append('c'); break;
                    }
                } catch (Exception x) {
                    exc(out, x);
                }
                out.append(',');
            }
            try {
                os.close();
            } catch (Exception x) {
                exc(out, x);
            }
            out.append(lo.show()).append('|');
            byte[] enc = lo.bytes.toByteArray();
            String in = new String(enc, java.nio.charset.StandardCharsets.ISO_8859_1);
            if (r(3) == 0) in = corrupt(in);
            byte[] bytes = in.getBytes(java.nio.charset.StandardCharsets.ISO_8859_1);
            IoOps.s = s;
            InputStream base = r(2) == 0 ? new ByteArrayInputStream(bytes) : new IoOps.Trickle(bytes, null);
            InputStream is = decoder().wrap(base);
            int reads = 2 + r(8);
            for (int k = 0; k < reads; k++) {
                try {
                    switch (r(5)) {
                        case 0: case 1: out.append(is.read()); break;
                        case 2: case 3: { byte[] b = new byte[r(6) + 1]; int n = is.read(b, r(2), r(b.length)); out.append(n).append(':').append(IoOps.hex(b)); break; }
                        default: { if (r(3) == 0) is.close(); else out.append(is.available()); break; }
                    }
                } catch (Exception x) {
                    exc(out, x);
                }
                out.append(',');
            }
        } catch (Exception e) {
            exc(out, e);
        }
        return out.toString();
    }
}

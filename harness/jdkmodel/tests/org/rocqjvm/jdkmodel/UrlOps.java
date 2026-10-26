package org.rocqjvm.jdkmodel;

import java.io.UnsupportedEncodingException;
import java.net.URLDecoder;
import java.net.URLEncoder;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;

/** Differential tests of URLEncoder.encode / URLDecoder.decode over random strings (unreserved
 *  characters, spaces, '+', '%' escapes valid and broken, non-ASCII, surrogates paired and lone)
 *  in the six standard charsets, the charset-name overloads and their exceptions. */
public final class UrlOps {
    private UrlOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static final String POOL = "aZ09-_.*~ +%/?&=#:@!$'()éÿĀ€😀𐀀中\t\n";
    static final Charset[] CS = {StandardCharsets.UTF_8, StandardCharsets.ISO_8859_1, StandardCharsets.US_ASCII,
        StandardCharsets.UTF_16, StandardCharsets.UTF_16BE, StandardCharsets.UTF_16LE};
    static final String[] NAMES = {"UTF-8", "utf8", "ISO-8859-1", "latin1", "US-ASCII", "UTF-16", "", "bogus charset", "UTF-16LE", null};

    static String str() {
        StringBuilder b = new StringBuilder();
        for (int i = r(10); i > 0; i--) b.append(POOL.charAt(r(POOL.length())));
        return b.toString();
    }

    static String esc() {
        StringBuilder b = new StringBuilder();
        String hex = "0123456789abcdefABCDEFgG-+１١";
        for (int i = r(8); i > 0; i--) {
            switch (r(5)) {
                case 0: b.append('%').append(hex.charAt(r(22))).append(hex.charAt(r(22))); break;
                case 1: b.append('%').append(hex.charAt(r(hex.length()))).append(hex.charAt(r(hex.length()))); break;
                case 2: b.append(r(3) == 0 ? "%" : r(2) == 0 ? "%4" : "+"); break;
                case 3: b.append("%C3%A9%E2%82%AC%F0%9F%98%80%FF%80".substring(r(4) * 3, 15 + r(4) * 3)); break;
                default: b.append(POOL.charAt(r(POOL.length())));
            }
        }
        return b.toString();
    }

    public static String enc(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 8; k++) {
            String t = r(12) == 0 ? null : str();
            try {
                String e = URLEncoder.encode(t, CS[r(CS.length)]);
                out.append(e).append(e == t);
                if (r(3) == 0) out.append('|').append(URLEncoder.encode(t, NAMES[r(NAMES.length)]));
                if (r(4) == 0) out.append('|').append(URLEncoder.encode(t));
                if (r(6) == 0) out.append('|').append(URLEncoder.encode(t, (Charset) null));
            } catch (UnsupportedEncodingException | RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String dec(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 8; k++) {
            String t = r(12) == 0 ? null : r(3) == 0 ? URLEncoder.encode(str(), StandardCharsets.UTF_8) : esc();
            try {
                String d = URLDecoder.decode(t, CS[r(CS.length)]);
                out.append(d).append(d == t);
                if (r(3) == 0) out.append('|').append(URLDecoder.decode(t, NAMES[r(NAMES.length)]));
                if (r(4) == 0) out.append('|').append(URLDecoder.decode(t));
                if (r(6) == 0) out.append('|').append(URLDecoder.decode(t, (Charset) null));
            } catch (UnsupportedEncodingException | RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }
}

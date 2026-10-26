/*
 * rocq-jvm model of java.net.URLDecoder (clean-room, Apache-2.0), from the Javadoc: '+' becomes a
 * space, each run of consecutive "%xy" escapes is parsed as hex bytes (Integer.parseInt(s, i + 1,
 * i + 3, 16), so a sign or any Unicode digit is accepted as the JDK does) and decoded with the
 * charset (new String(bytes, charset): malformed input becomes U+FFFD), other characters stay. The
 * result is the argument itself when nothing changed. The IllegalArgumentException, the
 * UnsupportedEncodingException and the null-argument exceptions carry JDK 21's texts.
 */
package java.net;

import java.io.UnsupportedEncodingException;
import java.nio.charset.Charset;
import java.nio.charset.IllegalCharsetNameException;
import java.nio.charset.UnsupportedCharsetException;

public class URLDecoder {
    private URLDecoder() {
    }

    @Deprecated
    public static String decode(String s) {
        try {
            return decode(s, "UTF-8");
        } catch (UnsupportedEncodingException e) {
            return null;
        }
    }

    public static String decode(String s, String enc) throws UnsupportedEncodingException {
        if (enc == null) throw new NullPointerException("Cannot invoke \"String.isEmpty()\" because \"enc\" is null");
        if (enc.isEmpty()) throw new UnsupportedEncodingException("URLDecoder: empty string enc parameter");
        try {
            return decode(s, Charset.forName(enc));
        } catch (IllegalCharsetNameException | UnsupportedCharsetException e) {
            throw new UnsupportedEncodingException(enc);
        }
    }

    private static final String ILLEGAL = "URLDecoder: Illegal hex characters in escape (%) pattern - ";

    public static String decode(String s, Charset charset) {
        if (charset == null) throw new NullPointerException("Charset");
        if (s == null) throw new NullPointerException("Cannot invoke \"String.length()\" because \"s\" is null");
        boolean changed = false;
        int n = s.length();
        StringBuilder sb = new StringBuilder();
        byte[] bytes = null;
        int i = 0;
        while (i < n) {
            char c = s.charAt(i);
            if (c == '+') {
                sb.append(' ');
                i++;
                changed = true;
            } else if (c == '%') {
                if (bytes == null) bytes = new byte[(n - i) / 3];
                int pos = 0;
                while (i + 2 < n && c == '%') {
                    int v;
                    try {
                        v = Integer.parseInt(s, i + 1, i + 3, 16);
                    } catch (NumberFormatException e) {
                        throw new IllegalArgumentException(ILLEGAL + e.getMessage());
                    }
                    if (v < 0) throw new IllegalArgumentException(ILLEGAL + "negative value");
                    bytes[pos++] = (byte) v;
                    i += 3;
                    if (i < n) c = s.charAt(i);
                }
                if (i < n && c == '%') throw new IllegalArgumentException("URLDecoder: Incomplete trailing escape (%) pattern");
                sb.append(new String(bytes, 0, pos, charset));
                changed = true;
            } else {
                sb.append(c);
                i++;
            }
        }
        return changed ? sb.toString() : s;
    }
}

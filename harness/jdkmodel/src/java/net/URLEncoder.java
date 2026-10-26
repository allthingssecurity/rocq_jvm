/*
 * rocq-jvm model of java.net.URLEncoder (clean-room, Apache-2.0), from the Javadoc ("HTML form
 * encoding"): a-z A-Z 0-9 . - * _ stay, a space becomes '+', every other run of characters is
 * converted to bytes in the charset (String.getBytes, so a UTF-16 run starts with its byte-order
 * mark, a lone surrogate becomes the charset's replacement) and each byte becomes "%XY" (upper-case
 * hex). The result is the argument itself when nothing changed. encode(String) uses the default
 * charset (UTF-8). The null-argument exceptions carry JDK 21's texts.
 */
package java.net;

import java.io.UnsupportedEncodingException;
import java.nio.charset.Charset;
import java.nio.charset.IllegalCharsetNameException;
import java.nio.charset.UnsupportedCharsetException;

public class URLEncoder {
    private URLEncoder() {
    }

    static boolean plain(int c) {
        return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
            || c == ' ' || c == '-' || c == '_' || c == '.' || c == '*';
    }

    @Deprecated
    public static String encode(String s) {
        try {
            return encode(s, "UTF-8");
        } catch (UnsupportedEncodingException e) {
            return null;
        }
    }

    public static String encode(String s, String enc) throws UnsupportedEncodingException {
        if (enc == null) throw new NullPointerException("charsetName");
        try {
            return encode(s, Charset.forName(enc));
        } catch (IllegalCharsetNameException | UnsupportedCharsetException e) {
            throw new UnsupportedEncodingException(enc);
        }
    }

    public static String encode(String s, Charset charset) {
        if (charset == null) throw new NullPointerException("charset");
        if (s == null) throw new NullPointerException("Cannot invoke \"String.length()\" because \"s\" is null");
        boolean changed = false;
        int n = s.length();
        StringBuilder out = new StringBuilder(n);
        int i = 0;
        while (i < n) {
            char c = s.charAt(i);
            if (plain(c)) {
                if (c == ' ') {
                    c = '+';
                    changed = true;
                }
                out.append(c);
                i++;
                continue;
            }
            int start = i;
            do {
                // a high surrogate takes the low surrogate after it into the run
                if (Character.isHighSurrogate(s.charAt(i)) && i + 1 < n && Character.isLowSurrogate(s.charAt(i + 1))) i++;
                i++;
            } while (i < n && !plain(s.charAt(i)));
            byte[] ba = s.substring(start, i).getBytes(charset);
            for (byte b : ba) {
                out.append('%').append(hex((b >> 4) & 0xF)).append(hex(b & 0xF));
            }
            changed = true;
        }
        return changed ? out.toString() : s;
    }

    private static char hex(int d) {
        return (char) (d < 10 ? '0' + d : 'A' + d - 10);
    }
}

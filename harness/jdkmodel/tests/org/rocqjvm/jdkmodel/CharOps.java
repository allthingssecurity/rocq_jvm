package org.rocqjvm.jdkmodel;

/** Differential tests of java.lang.Character's classification methods (getType, identifier
 *  properties, alphabetic/ideographic/space/title case/defined/mirrored/ISO control,
 *  getNumericValue, digit in every radix) and the surrogate helpers, over random code points. */
public final class CharOps {
    private CharOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static int cp() {
        switch (r(5)) {
            case 0: return r(128);
            case 1: return r(0x800);
            case 2: return r(0x10000);
            case 3: return r(0x110000);
            default: { int[] e = {0x24, 0x5f, 0x7f, 0x9f, 0xa0, 0xad, 0x200b, 0x2028, 0x3000, 0x1c5, 0xff21, 0xff41, 0x0660, 0x2160, 0x00bd,
                                  0xd800, 0xdfff, 0x10400, 0x1f600, 0xfeff, 0x0300, 0x4e00, -1, 0x110000};
                      return e[r(e.length)]; }
        }
    }

    public static String props(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 12; k++) {
            int c = cp();
            char ch = (char) c;
            out.append(c).append(':').append(Character.getType(c)).append(Character.isJavaIdentifierStart(c) ? 'S' : 's')
               .append(Character.isJavaIdentifierPart(c) ? 'P' : 'p').append(Character.isUnicodeIdentifierStart(c) ? 'U' : 'u')
               .append(Character.isUnicodeIdentifierPart(c) ? 'V' : 'v').append(Character.isIdentifierIgnorable(c) ? 'I' : 'i')
               .append(Character.isAlphabetic(c) ? 'A' : 'a').append(Character.isIdeographic(c) ? 'G' : 'g')
               .append(Character.isSpaceChar(c) ? 'W' : 'w').append(Character.isTitleCase(c) ? 'T' : 't')
               .append(Character.isDefined(c) ? 'D' : 'd').append(Character.isMirrored(c) ? 'M' : 'm')
               .append(Character.isISOControl(c) ? 'C' : 'c').append(Character.getNumericValue(c)).append(',')
               .append(Character.digit(c, 2 + r(35))).append(',').append(Character.digit(c, 16)).append(',')
               .append(Character.isValidCodePoint(c)).append(Character.isBmpCodePoint(c)).append(Character.isSupplementaryCodePoint(c))
               .append(Character.charCount(c)).append(',').append((int) Character.highSurrogate(c)).append(',')
               .append((int) Character.lowSurrogate(c)).append(',').append(Character.getType(ch)).append(Character.isJavaIdentifierPart(ch))
               .append(Character.isSurrogate(ch)).append(Character.isLetterOrDigit(c)).append(Character.toCodePoint(Character.highSurrogate(c), Character.lowSurrogate(c)))
               .append(Character.compare(ch, (char) r(65536))).append(Character.hashCode(ch)).append((int) Character.reverseBytes(ch)).append(';');
        }
        return out.toString();
    }

    static final String POOL = "aZ09 ßŉǰΐΰﬀﬁﬃﬅﬆİıÀàÿŸµΣσςǅǈǋǲАяЁёΩωΆ\u0345\u1E9E\u1F80\u1FB3ǆ\uD801\uDC00\uD801\uDC28\uD83D\uDE00\uD800x\uDC00ⅰⅫ";

    public static String cases(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            StringBuilder b = new StringBuilder();
            for (int i = r(8); i > 0; i--) b.append(POOL.charAt(r(POOL.length())));
            String t = b.toString();
            String up = t.toUpperCase();
            out.append(up).append('|').append(up == t).append('|');
            if (t.indexOf('\u03A3') < 0) {
                String lo = t.toLowerCase();
                out.append(lo).append('|').append(lo == t).append('|').append(lo.toUpperCase().equals(up));
            }
            out.append(';');
        }
        return out.toString();
    }

    /** StringBuilder.append(CharSequence, start, end) and append(char[], offset, len), incl. null
     *  arguments and out-of-range bounds (with int overflow of offset + len). */
    public static String sb(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        String t = "abcdefgh";
        char[] cs = t.toCharArray();
        for (int k = 0; k < 8; k++) {
            StringBuilder b = new StringBuilder("x");
            int a = r(12) - 2, e = r(12) - 2;
            try {
                switch (r(5)) {
                    case 0: b.append(t, a, e); break;
                    case 1: b.append(new StringBuilder(t), a, e); break;
                    case 2: b.append((CharSequence) null, a, e); break;
                    case 3: b.append(cs, a, r(8) == 0 ? Integer.MAX_VALUE : e); break;
                    default: b.append(r(4) == 0 ? null : cs, a, e); break;
                }
                out.append(b);
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    static String numStr() {
        String digits = "0123456789abcdefzZ+-\uff11\u0661\u0966 x";
        switch (r(6)) {
            case 0: return null;
            case 1: { String[] e = {"", "+", "-", "2147483647", "2147483648", "-2147483648", "-2147483649", "9223372036854775807",
                                    "9223372036854775808", "-9223372036854775808", "32767", "32768", "-129", "127", "7fffffff", "-80000000", "+0", "00012", "1_000"};
                      return e[r(e.length)]; }
            default: { StringBuilder b = new StringBuilder();
                       for (int i = r(12); i > 0; i--) b.append(r(3) == 0 ? digits.charAt(r(digits.length())) : (char) ('0' + r(10)));
                       return b.toString(); }
        }
    }

    /** Integer/Long/Short/Byte parse and valueOf(String[, radix]), parseInt/parseLong(CharSequence,
     *  begin, end, radix), with every NumberFormatException text and the Integer cache identity. */
    public static String nums(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int[] radixes = {10, 10, 16, 2, 36, 8, 1, 37, 0};
        for (int k = 0; k < 10; k++) {
            String t = numStr();
            int rad = radixes[r(radixes.length)];
            try {
                switch (r(14)) {
                    case 0: out.append(Integer.parseInt(t)); break;
                    case 1: out.append(Integer.parseInt(t, rad)); break;
                    case 2: out.append(Long.parseLong(t)); break;
                    case 3: out.append(Long.parseLong(t, rad)); break;
                    case 4: out.append(Short.parseShort(t, rad)).append(Byte.parseByte(t)); break;
                    case 5: { Integer a = Integer.valueOf(t), b = Integer.valueOf(t); out.append(a).append(a == b); break; }
                    case 6: { Long a = Long.valueOf(t, rad); out.append(a).append(Short.valueOf(t)).append(Byte.valueOf(t, rad)); break; }
                    case 7: { int b = r(5) - 1, e = r(14) - 1;
                              out.append(Integer.parseInt(t == null || r(5) == 0 ? (CharSequence) t : new StringBuilder(t), b, e, rad)); break; }
                    case 8: { int b = r(5) - 1, e = r(14) - 1; out.append(Long.parseLong(t, b, e, rad)); break; }
                    case 9: out.append(Short.parseShort(t)); break;
                    case 10: { String d = r(3) == 0 ? t : (r(2) == 0 ? "-" : r(2) == 0 ? "+" : "") + new String[]{"0x", "0X", "#", "0", "", "0x-", "#+"}[r(7)] + (t == null ? "" : t);
                               out.append(Integer.decode(d)).append(',').append(Long.decode(d)).append(',').append(Short.decode(d)).append(Byte.decode(d)); break; }
                    case 11: { String u = r(3) == 0 ? t : new String[]{"4294967295", "4294967296", "18446744073709551615", "18446744073709551616",
                                   "ffffffff", "1ffffffff", "-0", "+42", "zzzzzzzzzzzzz", "3w5e11264sgsf", "3w5e11264sgsg", "", "9223372036854775808x",
                                   "18446744073709551619", "12345678901234567890"}[r(15)];
                               try { out.append(Integer.parseUnsignedInt(u, rad)); } catch (RuntimeException x) { out.append('!').append(x.getMessage()); }
                               try { out.append(Long.parseUnsignedLong(u, rad)).append(Long.parseUnsignedLong(u)); } catch (RuntimeException x) { out.append('!').append(x.getMessage()); }
                               out.append(Integer.parseUnsignedInt(u == null || u.isEmpty() || u.charAt(0) == '-' ? "7" : "123")); break; }
                    case 12: { int iv = r(1 << 30) * 7 + r(3); long lv = (long) iv * 1234567891L;
                               out.append(Integer.reverse(iv)).append(',').append(Integer.reverseBytes(iv)).append(',').append(Long.reverse(lv)).append(',')
                                  .append(Long.reverseBytes(lv)).append(',').append(Long.min(lv, iv)).append(Long.max(lv, iv)); break; }
                    default: { long v = r(2) == 0 ? (long) r(1 << 30) * (r(2) == 0 ? -7 : 3) : Long.MIN_VALUE + r(100);
                               out.append(Integer.toString((int) v, rad)).append(',').append(Long.toString(v, rad)); break; }
                }
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    /** StringIndexOutOfBoundsException texts of String/StringBuilder index and range checks. */
    public static String idx(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 10; k++) {
            String t = "abcdef".substring(0, r(7));
            int a = r(10) - 3, b = r(10) - 3;
            try {
                switch (r(9)) {
                    case 0: out.append(t.charAt(a)); break;
                    case 1: out.append(t.substring(a)); break;
                    case 2: out.append(t.substring(a, b)); break;
                    case 3: out.append(new StringBuilder(t).charAt(a)); break;
                    case 4: out.append(new StringBuilder(t).deleteCharAt(a)); break;
                    case 5: { StringBuilder x = new StringBuilder(t); x.setLength(a); out.append(x).append(x.length()); break; }
                    case 6: out.append(t.subSequence(a, b)); break;
                    case 7: out.append(new StringBuilder(t).insert(a, "XY")); break;
                    default: out.append(System.lineSeparator().length()).append(System.lineSeparator().charAt(0) == '\n')
                                .append(System.lineSeparator() == "\n").append(System.getProperty("line.separator") == System.lineSeparator())
                                .append(System.getProperty("file.separator")).append(System.getProperty("path.separator", "?"))
                                .append(System.getProperty("file.separator") == System.getProperty("file.separator"));
                             try { System.getProperty(r(2) == 0 ? null : ""); } catch (RuntimeException x) { out.append(x.getMessage()); }
                             break;
                }
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    @SuppressWarnings("deprecation")
    static java.util.Locale loc() {
        java.util.Locale[] c = {java.util.Locale.ROOT, java.util.Locale.ENGLISH, java.util.Locale.US, java.util.Locale.UK, java.util.Locale.CANADA,
            java.util.Locale.GERMANY, java.util.Locale.FRENCH, java.util.Locale.CHINA, java.util.Locale.JAPAN};
        String[] ls = {"en", "EN", "de", "iw", "in", "ji", "", "xx", "zh"};
        String[] rs = {"", "us", "GB", "Ca", "001", "x"};
        String[] vs = {"", "", "", "POSIX", "v1"};
        switch (r(4)) {
            case 0: return c[r(c.length)];
            case 1: return new java.util.Locale(ls[r(ls.length)]);
            case 2: return new java.util.Locale(ls[r(ls.length)], rs[r(rs.length)]);
            default: return new java.util.Locale(ls[r(ls.length)], rs[r(rs.length)], vs[r(vs.length)]);
        }
    }

    /** Locale constants, constructors (normalisation, legacy codes), getters, toString, equals,
     *  hashCode, language tags; String.toLowerCase/toUpperCase(Locale) and String.format(Locale, ...). */
    public static String locales(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            java.util.Locale l = loc(), m = loc();
            try {
                out.append(l).append('|').append(l.getLanguage()).append('|').append(l.getCountry()).append('|').append(l.getVariant())
                   .append('|').append(l.hashCode()).append(l.equals(m)).append(l.equals(null)).append(m.hashCode() == l.hashCode()).append('|');
                if (l.getVariant().isEmpty() && (l.getCountry().isEmpty() || l.getCountry().length() == 2 || l.getCountry().equals("001")))
                    out.append(l.toLanguageTag()).append('|').append(java.util.Locale.forLanguageTag(l.toLanguageTag())).append('|');
                String t = "Title İı ßx " + (char) ('a' + r(26));
                out.append(t.toUpperCase(java.util.Locale.ROOT)).append(t.toLowerCase(java.util.Locale.ENGLISH)).append('|')
                   .append(String.format(r(2) == 0 ? java.util.Locale.ROOT : r(2) == 0 ? java.util.Locale.US : null, "%,d %.2f %S %e %s", r(10000000), r(100000) / 7.0, t, r(1000) * 1.5, l));
                if (r(4) == 0) out.append(t.toLowerCase(r(2) == 0 ? null : l));
                if (r(8) == 0) out.append(String.format(l, "%,.3f", 1234567.891));
            } catch (RuntimeException x) {
                out.append('!').append(x.getClass().getSimpleName()).append(':').append(x.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }
}

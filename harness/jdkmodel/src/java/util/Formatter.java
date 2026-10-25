/*
 * rocq-jvm model of java.util.Formatter (clean-room, Apache-2.0), from the class Javadoc
 * ("Format String Syntax", "Conversions", "Details"), for the default locale en / root (zero
 * digit '0', grouping ',' every 3 digits, ASCII case mapping) and line separator "\n".
 *
 * Supported: %[argument_index$][flags][width][.precision]conversion with the general (b B h H
 * s S), character (c C), integral (d o x X for Byte, Short, Integer, Long) and text (n %)
 * conversions, the flags - # + space 0 , ( <, ordinary, explicit and relative indexing, and the
 * exceptions the Javadoc gives for bad specifiers, which are all detected while the whole format
 * string is parsed, before any output, as in the JDK.
 * Not modelled (STUCK): floating-point and BigDecimal/BigInteger conversions (e E f g G a A),
 * date/time (t T), Formattable arguments, explicit locales, index 0.
 */
package java.util;

public final class Formatter {
    private final StringBuilder out;

    public Formatter() {
        out = new StringBuilder();
    }

    public Formatter(StringBuilder sb) {
        out = (sb == null) ? new StringBuilder() : sb;
    }

    public String toString() {
        return out.toString();
    }

    public StringBuilder out() {
        return out;
    }

    public void flush() {
    }

    public void close() {
    }

    public java.io.IOException ioException() {
        return null;
    }

    // flags, in the order Flags.toString prints them
    private static final int LEFT = 1, ALT = 2, PLUS = 4, SPACE = 8, ZERO = 16, GROUP = 32, PAREN = 64, PREV = 128, UPPER = 256;

    private static String flagString(int f) {
        StringBuilder b = new StringBuilder();
        if ((f & LEFT) != 0) b.append('-');
        if ((f & UPPER) != 0) b.append('^');
        if ((f & ALT) != 0) b.append('#');
        if ((f & PLUS) != 0) b.append('+');
        if ((f & SPACE) != 0) b.append(' ');
        if ((f & ZERO) != 0) b.append('0');
        if ((f & GROUP) != 0) b.append(',');
        if ((f & PAREN) != 0) b.append('(');
        if ((f & PREV) != 0) b.append('<');
        return b.toString();
    }

    private static int flagOf(char c) {
        switch (c) {
            case '-': return LEFT;
            case '#': return ALT;
            case '+': return PLUS;
            case ' ': return SPACE;
            case '0': return ZERO;
            case ',': return GROUP;
            case '(': return PAREN;
            case '<': return PREV;
            default: return 0;
        }
    }

    /** A parsed piece: fixed text (conv == 0) or a format specifier. */
    private static final class Spec {
        String text;
        int index = 0;        // > 0 explicit, 0 ordinary, -1 previous ('<'), -2 text conversion
        int flags;
        int width = -1;
        int precision = -1;
        char conv;            // lower case
        char convAsGiven;

        public String toString() {
            StringBuilder sb = new StringBuilder("%");
            int dupf = flags & ~UPPER;
            sb.append(flagString(dupf));
            if (index > 0) sb.append(index).append('$');
            if (width != -1) sb.append(width);
            if (precision != -1) sb.append('.').append(precision);
            sb.append(convAsGiven);
            return sb.toString();
        }
    }

    private static boolean isDigit(char c) {
        return c >= '0' && c <= '9';
    }

    private static int toInt(String s, int from, int to, boolean width) {
        long v = 0;
        for (int i = from; i < to; i++) {
            v = v * 10 + (s.charAt(i) - '0');
            if (v > Integer.MAX_VALUE) {
                if (width) throw new IllegalFormatWidthException(Integer.MIN_VALUE);
                throw new IllegalFormatPrecisionException(Integer.MIN_VALUE);
            }
        }
        return (int) v;
    }

    private static List<Spec> parse(String s) {
        ArrayList<Spec> al = new ArrayList<>();
        int i = 0, max = s.length();
        while (i < max) {
            int n = s.indexOf('%', i);
            if (n < 0) {
                Spec t = new Spec();
                t.text = s.substring(i);
                al.add(t);
                break;
            }
            if (i != n) {
                Spec t = new Spec();
                t.text = s.substring(i, n);
                al.add(t);
            }
            i = n + 1;
            if (i >= max) throw new UnknownFormatConversionException("%");
            // a specifier that does not parse is reported by its first character (as the JDK does)
            String first = String.valueOf(s.charAt(i));
            Spec sp = new Spec();
            // argument index: digits followed by '$'
            int j = i;
            while (j < max && isDigit(s.charAt(j))) j++;
            if (j > i && j < max && s.charAt(j) == '$') {
                int idx = toInt(s, i, j, true);
                if (idx <= 0) throw ModelStuck.unsupported("Formatter: argument index 0");
                sp.index = idx;
                i = j + 1;
            }
            // flags
            while (i < max && flagOf(s.charAt(i)) != 0) {
                int f = flagOf(s.charAt(i));
                if ((sp.flags & f) != 0) throw new DuplicateFormatFlagsException(flagString(f));
                sp.flags |= f;
                i++;
            }
            if ((sp.flags & PREV) != 0) sp.index = -1;
            // width
            j = i;
            while (j < max && isDigit(s.charAt(j))) j++;
            if (j > i) {
                sp.width = toInt(s, i, j, true);
                i = j;
            }
            // precision
            if (i < max && s.charAt(i) == '.' && !(i + 1 < max && isDigit(s.charAt(i + 1))) && i > n + 1) {
                throw new UnknownFormatConversionException(first);
            }
            if (i + 1 < max && s.charAt(i) == '.' && isDigit(s.charAt(i + 1))) {
                j = i + 1;
                while (j < max && isDigit(s.charAt(j))) j++;
                sp.precision = toInt(s, i + 1, j, false);
                i = j;
            }
            if (i >= max) throw new UnknownFormatConversionException(first);
            char c = s.charAt(i++);
            if (c == 't' || c == 'T') {
                if (i >= max) throw new UnknownFormatConversionException(String.valueOf(c));
                if (sp.precision != -1) throw new IllegalFormatPrecisionException(sp.precision);
                char tc = s.charAt(i);
                if ("HIklMSLNpzZsQBbhAaCYyjmdeRTrDFc".indexOf(tc) < 0) throw new UnknownFormatConversionException(String.valueOf(c) + tc);
                throw ModelStuck.unsupported("Formatter: date/time conversions");
            }
            sp.convAsGiven = c;
            switch (c) {
                case 'b': case 'h': case 's': case 'c': case 'd': case 'o': case 'x': case 'n': case '%':
                case 'e': case 'f': case 'g': case 'a':
                    sp.conv = c;
                    break;
                case 'B': case 'H': case 'S': case 'C': case 'X': case 'E': case 'G': case 'A':
                    sp.conv = (char) (c + 32);
                    sp.flags |= UPPER;
                    break;
                default:
                    throw new UnknownFormatConversionException(String.valueOf(c));
            }
            check(sp);
            al.add(sp);
        }
        return al;
    }

    /** All the given flags that are present are reported together (as JDK 21 does). */
    private static void badFlags(Spec sp, int bad) {
        int b = sp.flags & bad;
        if (b != 0) throw new FormatFlagsConversionMismatchException(flagString(b), sp.conv);
    }

    private static void check(Spec sp) {
        char c = sp.conv;
        if (c == 'n' || c == '%') sp.index = -2;
        if (c == 'b' || c == 'h' || c == 's') {
            if ((c == 'b' || c == 'h') && (sp.flags & ALT) != 0) throw new FormatFlagsConversionMismatchException("#", c);
            if (sp.width == -1 && (sp.flags & LEFT) != 0) throw new MissingFormatWidthException(sp.toString());
            badFlags(sp, PLUS | SPACE | ZERO | GROUP | PAREN);
        } else if (c == 'c') {
            if (sp.precision != -1) throw new IllegalFormatPrecisionException(sp.precision);
            badFlags(sp, ALT | PLUS | SPACE | ZERO | GROUP | PAREN);
            if (sp.width == -1 && (sp.flags & LEFT) != 0) throw new MissingFormatWidthException(sp.toString());
        } else if (c == 'd' || c == 'o' || c == 'x') {
            if (sp.width == -1 && (sp.flags & (LEFT | ZERO)) != 0) throw new MissingFormatWidthException(sp.toString());
            if (((sp.flags & PLUS) != 0 && (sp.flags & SPACE) != 0) || ((sp.flags & LEFT) != 0 && (sp.flags & ZERO) != 0))
                throw new IllegalFormatFlagsException(flagString(sp.flags));
            if (sp.precision != -1) throw new IllegalFormatPrecisionException(sp.precision);
            if (c == 'd') badFlags(sp, ALT);
            else badFlags(sp, GROUP);
        } else if (c == 'n' || c == '%') {
            if (sp.precision != -1) throw new IllegalFormatPrecisionException(sp.precision);
            int f = sp.flags & ~UPPER;
            if (c == '%') {
                if (f != LEFT && f != 0) throw new IllegalFormatFlagsException(flagString(f));
                if (sp.width == -1 && (f & LEFT) != 0) throw new MissingFormatWidthException(sp.toString());
            } else {
                if (sp.width != -1) throw new IllegalFormatWidthException(sp.width);
                if (f != 0) throw new IllegalFormatFlagsException(flagString(f));
            }
        } else {
            throw ModelStuck.unsupported("Formatter: floating-point conversions");
        }
    }

    public Formatter format(String format, Object... args) {
        List<Spec> fsa = parse(format);
        int last = -1, lasto = -1;
        for (Spec sp : fsa) {
            if (sp.conv == 0) {
                out.append(sp.text);
                continue;
            }
            int index = sp.index;
            if (index == -2) {
                print(sp, null);
            } else if (index == -1) {
                if (last < 0 || (args != null && last > args.length - 1)) throw new MissingFormatArgumentException(sp.toString());
                print(sp, args == null ? null : args[last]);
            } else if (index == 0) {
                lasto++;
                last = lasto;
                if (args != null && lasto > args.length - 1) throw new MissingFormatArgumentException(sp.toString());
                print(sp, args == null ? null : args[lasto]);
            } else {
                last = index - 1;
                if (args != null && last > args.length - 1) throw new MissingFormatArgumentException(sp.toString());
                print(sp, args == null ? null : args[last]);
            }
        }
        return this;
    }

    private void justify(Spec sp, String s) {
        if (sp.width == -1 || s.length() >= sp.width) {
            out.append(s);
            return;
        }
        int pad = sp.width - s.length();
        if ((sp.flags & LEFT) != 0) {
            out.append(s);
            for (int k = 0; k < pad; k++) out.append(' ');
        } else {
            for (int k = 0; k < pad; k++) out.append(' ');
            out.append(s);
        }
    }

    private void printString(Spec sp, String s) {
        if (sp.precision != -1 && sp.precision < s.length()) s = s.substring(0, sp.precision);
        if ((sp.flags & UPPER) != 0) s = s.toUpperCase();
        justify(sp, s);
    }

    private static final String HEX = "0123456789abcdef";

    /** Unsigned digits of v (as a 64-bit two's complement value) in radix 8 or 16. */
    private static String unsigned(long v, int shift) {
        if (v == 0) return "0";
        char[] buf = new char[64];
        int pos = 64;
        int mask = (1 << shift) - 1;
        while (v != 0) {
            buf[--pos] = HEX.charAt((int) (v & mask));
            v >>>= shift;
        }
        StringBuilder b = new StringBuilder();
        for (int k = pos; k < 64; k++) b.append(buf[k]);
        return b.toString();
    }

    private void print(Spec sp, Object arg) {
        switch (sp.conv) {
            case 'n':
                out.append('\n');
                return;
            case '%':
                justify(sp, "%");
                return;
            case 'b':
                printString(sp, arg == null ? "false" : (arg instanceof Boolean) ? arg.toString() : "true");
                return;
            case 'h':
                printString(sp, arg == null ? "null" : unsigned(arg.hashCode() & 0xffffffffL, 4));
                return;
            case 's':
                if (arg instanceof Formattable) throw ModelStuck.unsupported("Formatter: Formattable argument");
                if ((sp.flags & ALT) != 0) throw new FormatFlagsConversionMismatchException("#", 's');
                printString(sp, String.valueOf(arg));
                return;
            case 'c':
                printChar(sp, arg);
                return;
            default:
                printInteger(sp, arg);
        }
    }

    private void printChar(Spec sp, Object arg) {
        String s;
        if (arg == null) {
            s = "null";
        } else if (arg instanceof Character) {
            s = String.valueOf(((Character) arg).charValue());
        } else if (arg instanceof Byte || arg instanceof Short || arg instanceof Integer) {
            int cp = (arg instanceof Byte) ? (Byte) arg : (arg instanceof Short) ? (Short) arg : (Integer) arg;
            if (cp < 0 || cp > 0x10FFFF) throw new IllegalFormatCodePointException(cp);
            if (cp < 0x10000) {
                s = String.valueOf((char) cp);
            } else {
                int v = cp - 0x10000;
                s = new StringBuilder().append((char) (0xD800 + (v >> 10))).append((char) (0xDC00 + (v & 0x3FF))).toString();
            }
        } else {
            throw new IllegalFormatConversionException(sp.conv, arg.getClass());
        }
        if ((sp.flags & UPPER) != 0) s = s.toUpperCase();
        justify(sp, s);
    }

    private void printInteger(Spec sp, Object arg) {
        if (arg == null) {
            printString(sp, "null");
            return;
        }
        long value;
        int bits;
        if (arg instanceof Byte) { value = (Byte) arg; bits = 8; }
        else if (arg instanceof Short) { value = (Short) arg; bits = 16; }
        else if (arg instanceof Integer) { value = (Integer) arg; bits = 32; }
        else if (arg instanceof Long) { value = (Long) arg; bits = 64; }
        else if (arg instanceof Number) throw ModelStuck.unsupported("Formatter: BigInteger and other Numbers");
        else throw new IllegalFormatConversionException(sp.conv, arg.getClass());
        StringBuilder sb = new StringBuilder();
        int f = sp.flags;
        int width = sp.width;
        if (sp.conv == 'd') {
            boolean neg = value < 0;
            if (!neg) {
                if ((f & PLUS) != 0) sb.append('+');
                else if ((f & SPACE) != 0) sb.append(' ');
            } else {
                if ((f & PAREN) != 0) sb.append('(');
                else sb.append('-');
            }
            String digits = String.valueOf(value);
            if (neg) digits = digits.substring(1);
            int w = (width != -1 && neg && (f & PAREN) != 0) ? width - 1 : width;
            int begin = sb.length();
            if ((f & GROUP) != 0) {
                int len = digits.length();
                for (int k = 0; k < len; k++) {
                    if (k > 0 && (len - k) % 3 == 0) sb.append(',');
                    sb.append(digits.charAt(k));
                }
            } else {
                sb.append(digits);
            }
            if (w != -1 && (f & ZERO) != 0) {
                StringBuilder z = new StringBuilder();
                for (int k = sb.length(); k < w; k++) z.append('0');
                sb.insert(begin, z.toString());
            }
            if (neg && (f & PAREN) != 0) sb.append(')');
        } else {
            badFlags(sp, PAREN | SPACE | PLUS);
            if (value < 0 && bits < 64) value += (1L << bits);
            boolean hex = sp.conv == 'x';
            String s = unsigned(value, hex ? 4 : 3);
            int len = s.length() + ((f & ALT) != 0 ? (hex ? 2 : 1) : 0);
            if ((f & ALT) != 0) sb.append(hex ? ((f & UPPER) != 0 ? "0X" : "0x") : "0");
            if ((f & ZERO) != 0) {
                for (int k = 0; k < width - len; k++) sb.append('0');
            }
            if ((f & UPPER) != 0) s = s.toUpperCase();
            sb.append(s);
        }
        justify(sp, sb.toString());
    }
}

/*
 * rocq-jvm model of java.util.Formatter (clean-room, Apache-2.0), from the class Javadoc
 * ("Format String Syntax", "Conversions", "Details"), for the default locale en / root (zero
 * digit '0', grouping ',' every 3 digits, ASCII case mapping) and line separator "\n".
 *
 * Supported: %[argument_index$][flags][width][.precision]conversion with the general (b B h H
 * s S), character (c C), integral (d o x X for Byte, Short, Integer, Long), floating-point
 * (e E f g G a A for Float and Double: JDK 21 rounds the decimal of Double.toString half up to the
 * precision, jdk.internal.math.FormattedFPDecimal; a A rounds the significand half-even) and text (n %) conversions, the flags - # +
 * space 0 , ( <, ordinary, explicit and relative indexing, and the exceptions the Javadoc gives
 * for bad specifiers, which are all detected while the whole format string is parsed, before any
 * output, as in the JDK.
 * BigInteger (d o x X) and BigDecimal (e f g) arguments follow JDK 21's print(BigInteger) /
 * print(BigDecimal) and BigDecimalLayout.
 * Not modelled (STUCK): date/time
 * (t T), Formattable arguments, explicit locales, index 0.
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

    /** An explicit locale: Locale.formatCheck$ admits those that format as this model (null, ROOT,
     *  en, en_US/GB/CA), else STUCK. */
    private Locale locale;
    private boolean hasLocale;

    public Formatter(Locale l) {
        Locale.formatCheck$(l);
        out = new StringBuilder();
        locale = l;
        hasLocale = true;
    }

    public Locale locale() {
        if (!hasLocale) throw ModelStuck.unsupported("Formatter.locale: the default locale");
        return locale;
    }

    public Formatter format(Locale l, String format, Object... args) {
        Locale.formatCheck$(l);
        return format(format, args);
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
            // checkFloat: checkNumeric, then the flags each conversion rejects
            if (sp.width == -1 && (sp.flags & (LEFT | ZERO)) != 0) throw new MissingFormatWidthException(sp.toString());
            if (((sp.flags & PLUS) != 0 && (sp.flags & SPACE) != 0) || ((sp.flags & LEFT) != 0 && (sp.flags & ZERO) != 0))
                throw new IllegalFormatFlagsException(flagString(sp.flags));
            if (c == 'a') badFlags(sp, PAREN | GROUP);
            else if (c == 'e') badFlags(sp, GROUP);
            else if (c == 'g') badFlags(sp, ALT);
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
            case 'e': case 'f': case 'g': case 'a':
                printFloat(sp, arg);
                return;
            default:
                printInteger(sp, arg);
        }
    }

    private void printFloat(Spec sp, Object arg) {
        if (arg == null) {
            printString(sp, "null");
            return;
        }
        double value;
        if (arg instanceof Float) value = ((Float) arg).floatValue();
        else if (arg instanceof Double) value = ((Double) arg).doubleValue();
        else if (arg instanceof java.math.BigDecimal) {
            if (sp.conv == 'a') throw new IllegalFormatConversionException(sp.conv, arg.getClass());
            java.math.BigDecimal bd = (java.math.BigDecimal) arg;
            StringBuilder sb = new StringBuilder();
            boolean neg = bd.signum() == -1;
            leadingSign(sb, sp.flags, neg);
            printDecimal(sp, sb, bd.abs(), sp.conv, sp.precision, neg);
            if (neg && (sp.flags & PAREN) != 0) sb.append(')');
            justify(sp, sb.toString());
            return;
        }
        else throw new IllegalFormatConversionException(sp.conv, arg.getClass());
        int f = sp.flags;
        StringBuilder sb = new StringBuilder();
        boolean neg = Double.compare(value, 0.0) == -1;
        if (!Double.isNaN(value)) {
            double v = Math.abs(value);
            leadingSign(sb, f, neg);
            if (!Double.isInfinite(v)) printFinite(sp, sb, v, neg);
            else sb.append((f & UPPER) != 0 ? "INFINITY" : "Infinity");
            if (neg && (f & PAREN) != 0) sb.append(')');
        } else {
            sb.append((f & UPPER) != 0 ? "NAN" : "NaN");
        }
        justify(sp, sb.toString());
    }

    private static void leadingSign(StringBuilder sb, int f, boolean neg) {
        if (!neg) {
            if ((f & PLUS) != 0) sb.append('+');
            else if ((f & SPACE) != 0) sb.append(' ');
        } else {
            if ((f & PAREN) != 0) sb.append('(');
            else sb.append('-');
        }
    }

    private static int adjustWidth(int width, int f, boolean neg) {
        return (width != -1 && neg && (f & PAREN) != 0) ? width - 1 : width;
    }

    /** Append zeros (and the point if needed) up to [prec] digits after the point. */
    private static void addZeros(StringBuilder sb, int prec) {
        int len = sb.length();
        int i = sb.indexOf(".");
        boolean needDot = i < 0;
        if (needDot) i = len;
        int outPrec = len - i - (needDot ? 0 : 1);
        if (outPrec == prec) return;
        if (needDot) sb.append('.');
        for (int k = outPrec; k < prec; k++) sb.append('0');
    }

    /** localizedMagnitude for the root locale: digits, ',' every 3 digits of the integer part
     *  with the GROUP flag, '.' as the point, zero padding to [width]. */
    private static void magnitude(StringBuilder sb, CharSequence value, int f, int width) {
        int begin = sb.length();
        int len = value.length();
        int dot = len;
        for (int j = 0; j < len; j++) {
            if (value.charAt(j) == '.') {
                dot = j;
                break;
            }
        }
        boolean grp = (f & GROUP) != 0;
        for (int j = 0; j < len; j++) {
            if (j == dot) {
                sb.append('.');
                grp = false;
                continue;
            }
            sb.append(value.charAt(j));
            if (grp && j != dot - 1 && ((dot - j) % 3 == 1)) sb.append(',');
        }
        if (width > sb.length() && (f & ZERO) != 0) {
            StringBuilder z = new StringBuilder();
            for (int k = sb.length(); k < width; k++) z.append('0');
            sb.insert(begin, z.toString());
        }
    }

    /** The hexadecimal significand and exponent of [d] (finite, >= 0) rounded half-even to
     *  [prec] hex digits (all digits for 0 or >= 13), as Double.toHexString without "0x". */
    private static String hexDouble(double d, int prec) {
        if (!Double.isFinite(d) || d == 0.0 || prec == 0 || prec >= 13) return Double.toHexString(d).substring(2);
        boolean subnormal = Math.getExponent(d) == Double.MIN_EXPONENT - 1;
        if (subnormal) d *= Math.scalb(1.0, 54);
        int shift = 53 - (1 + prec * 4);
        long bits = Double.doubleToLongBits(d);
        long kept = (bits & 0x7FFFFFFFFFFFFFFFL) >> shift;
        long dropped = bits & ~(~0L << shift);
        boolean odd = (kept & 1L) != 0;
        boolean half = ((1L << (shift - 1)) & dropped) != 0;
        boolean rest = shift > 1 && (~(1L << (shift - 1)) & dropped) != 0;
        if (half && (odd || rest)) kept++;
        double r = Double.longBitsToDouble((bits & 0x8000000000000000L) | (kept << shift));
        if (Double.isInfinite(r)) return "1.0p1024";
        String res = Double.toHexString(r).substring(2);
        if (!subnormal) return res;
        int p = res.indexOf('p');
        return res.substring(0, p) + "p" + Integer.toString(Integer.parseInt(res.substring(p + 1)) - 54);
    }

    private void printFinite(Spec sp, StringBuilder sb, double value, boolean neg) {
        int f = sp.flags;
        int width = sp.width;
        char c = sp.conv;
        if (c == 'a') {
            int prec = sp.precision == -1 ? 0 : sp.precision == 0 ? 1 : sp.precision;
            String s = hexDouble(value, prec);
            boolean upper = (f & UPPER) != 0;
            sb.append(upper ? "0X" : "0x");
            if ((f & ZERO) != 0) {
                int lead = ((f & SPACE) != 0 || (f & PLUS) != 0 || neg) ? 3 : 2;
                for (int k = width - s.length() - lead; k > 0; k--) sb.append('0');
            }
            int p = s.indexOf('p');
            StringBuilder va = new StringBuilder(upper ? s.substring(0, p).toUpperCase() : s.substring(0, p));
            if (prec != 0) addZeros(va, prec);
            sb.append(va).append(upper ? 'P' : 'p').append(s, p + 1, s.length());
        } else if (c == 'e') {
            int prec = (sp.precision == -1 ? 6 : sp.precision);
            Fpd fd = Fpd.valueOf(value, prec, 'e');
            StringBuilder mant = new StringBuilder().append(fd.digits);
            addZeros(mant, prec);
            if ((f & ALT) != 0 && prec == 0) mant.append('.');
            String exp = (value == 0.0) ? "+00" : fd.exp;
            int newW = width;
            if (width != -1) newW = adjustWidth(width - exp.length() - 1, f, neg);
            magnitude(sb, mant, f, newW);
            sb.append((f & UPPER) != 0 ? 'E' : 'e');
            sb.append(exp);
        } else if (c == 'f') {
            int prec = (sp.precision == -1 ? 6 : sp.precision);
            Fpd fd = Fpd.valueOf(value, prec, 'f');
            StringBuilder mant = new StringBuilder().append(fd.digits);
            addZeros(mant, prec);
            if ((f & ALT) != 0 && prec == 0) mant.append('.');
            int newW = width;
            if (width != -1) newW = adjustWidth(width, f, neg);
            magnitude(sb, mant, f, newW);
        } else {
            int prec = sp.precision;
            if (sp.precision == -1) prec = 6;
            else if (sp.precision == 0) prec = 1;
            String exp;
            StringBuilder mant = new StringBuilder();
            int expRounded;
            if (value == 0.0) {
                exp = null;
                mant.append('0');
                expRounded = 0;
            } else {
                Fpd fd = Fpd.valueOf(value, prec, 'g');
                exp = fd.exp;
                mant.append(fd.digits);
                expRounded = fd.n + fd.e - 1;
            }
            if (exp != null) prec -= 1;
            else prec -= expRounded + 1;
            addZeros(mant, prec);
            if ((f & ALT) != 0 && prec == 0) mant.append('.');
            int newW = width;
            if (width != -1) {
                if (exp != null) newW = adjustWidth(width - exp.length() - 1, f, neg);
                else newW = adjustWidth(width, f, neg);
            }
            magnitude(sb, mant, f, newW);
            if (exp != null) {
                sb.append((f & UPPER) != 0 ? 'E' : 'e');
                sb.append(exp);
            }
        }
    }

    /** jdk.internal.math.FormattedFPDecimal: the decimal f * 10^e of Double.toString(v) (v >= 0
     *  finite; n its number of digits, 0 for v = 0), rounded half up to the precision, and its
     *  digits in plain or scientific form ([exp]: sign and at least two digits). */
    private static final class Fpd {
        long f;
        int e;
        int n;
        String digits;
        String exp;

        static Fpd valueOf(double v, int prec, char form) {
            Fpd fd = new Fpd();
            if (v != 0.0) {
                fd.f = ModelEnv.decF(v);
                fd.e = ModelEnv.decE(v);
                fd.n = String.valueOf(fd.f).length();
            }
            if (form == 'e') {
                fd.round(prec + 1L);
                fd.scientificChars(prec);
            } else if (form == 'f') {
                fd.round(fd.n + fd.e + (long) prec);
                fd.plainChars();
            } else {
                fd.round(prec);
                int er = fd.n + fd.e - 1;
                if (-4 <= er && er < prec) fd.plainChars();
                else fd.scientificChars(prec - 1);
            }
            return fd;
        }

        private static long pow10(int k) {
            long r = 1;
            for (int i = 0; i < k; i++) r *= 10;
            return r;
        }

        void round(long pp) {
            if (n == 0 || pp < 0) {
                f = 0;
                e = 0;
                n = 1;
                return;
            }
            if (pp >= n) return;
            int p = (int) pp;
            e += n - p;
            long pw = pow10(n - p);
            f = (f + (pw >> 1)) / pw;
            if (p == 0) {
                n = 1;
                if (f == 0) e = 0;
                return;
            }
            n = p;
            if (f == pow10(p)) {
                f /= 10;
                e += 1;
            }
        }

        private static String zeros(int k) {
            StringBuilder b = new StringBuilder();
            for (int i = 0; i < k; i++) b.append('0');
            return b.toString();
        }

        /** The n digits of f (with leading zeros). */
        private String fdigits() {
            String s = String.valueOf(f);
            return zeros(n - s.length()) + s;
        }

        void plainChars() {
            String ds = fdigits();
            if (e >= 0) digits = ds + zeros(e);
            else if (n + e > 0) digits = ds.substring(0, n + e) + "." + ds.substring(n + e);
            else digits = "0." + zeros(-e - n) + ds;
        }

        void scientificChars(int prec) {
            String ds = fdigits();
            if (prec != 0) digits = ds.charAt(0) + "." + ds.substring(1);
            else digits = String.valueOf(ds.charAt(0));
            int er = n + e - 1;
            int aer = Math.abs(er);
            exp = (er >= 0 ? "+" : "-") + (aer < 10 ? "0" : "") + aer;
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
        else if (arg instanceof java.math.BigInteger) {
            printBigInteger(sp, (java.math.BigInteger) arg);
            return;
        }
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

    /** d o x X of a BigInteger: the sign (or parentheses) and the magnitude in the radix; the
     *  sign flags are allowed for o and x, unlike for the primitive types. */
    private void printBigInteger(Spec sp, java.math.BigInteger value) {
        StringBuilder sb = new StringBuilder();
        int f = sp.flags;
        int width = sp.width;
        boolean neg = value.signum() == -1;
        java.math.BigInteger v = value.abs();
        leadingSign(sb, f, neg);
        if (sp.conv == 'd') {
            magnitude(sb, v.toString(), f, adjustWidth(width, f, neg));
        } else {
            boolean hex = sp.conv == 'x';
            String s = v.toString(hex ? 16 : 8);
            int len = s.length() + sb.length();
            if (neg && (f & PAREN) != 0) len++;
            if ((f & ALT) != 0) {
                len += hex ? 2 : 1;
                sb.append(hex ? ((f & UPPER) != 0 ? "0X" : "0x") : "0");
            }
            if ((f & ZERO) != 0) for (int k = width - len; k > 0; k--) sb.append('0');
            if ((f & UPPER) != 0) s = s.toUpperCase();
            sb.append(s);
        }
        if (neg && (f & PAREN) != 0) sb.append(')');
        justify(sp, sb.toString());
    }

    private static void zeros(StringBuilder sb, int n) {
        for (int k = 0; k < n; k++) sb.append('0');
    }

    /** e f g of a BigDecimal (|value|): rounded HALF_UP to the precision through MathContext, laid
     *  out from the unscaled value and the scale (the JDK's BigDecimalLayout). */
    private void printDecimal(Spec sp, StringBuilder sb, java.math.BigDecimal value, char c, int precision, boolean neg) {
        int f = sp.flags;
        int width = sp.width;
        if (c == 'e') {
            int prec = precision == -1 ? 6 : precision;
            int scale = value.scale();
            int origPrec = value.precision();
            int nzeros = 0;
            int compPrec;
            if (prec > origPrec - 1) {
                compPrec = origPrec;
                nzeros = prec - (origPrec - 1);
            } else {
                compPrec = prec + 1;
            }
            java.math.BigDecimal v = new java.math.BigDecimal(value.unscaledValue(), scale, new java.math.MathContext(compPrec));
            String[] lay = layout(v.unscaledValue(), v.scale(), true);
            StringBuilder mant = new StringBuilder(lay[0]);
            if ((origPrec == 1 || lay[2].equals("n")) && (nzeros > 0 || (f & ALT) != 0)) mant.append('.');
            zeros(mant, nzeros);
            String exp = lay[1];
            int newW = width;
            if (width != -1) newW = adjustWidth(width - exp.length() - 1, f, neg);
            magnitude(sb, mant, f, newW);
            sb.append((f & UPPER) != 0 ? 'E' : 'e');
            sb.append(exp);
        } else if (c == 'f') {
            int prec = precision == -1 ? 6 : precision;
            int scale = value.scale();
            if (scale > prec) {
                int compPrec = value.precision();
                if (compPrec <= scale) {
                    value = value.setScale(prec, java.math.RoundingMode.HALF_UP);
                } else {
                    compPrec -= (scale - prec);
                    value = new java.math.BigDecimal(value.unscaledValue(), scale, new java.math.MathContext(compPrec));
                }
            }
            String[] lay = layout(value.unscaledValue(), value.scale(), false);
            StringBuilder mant = new StringBuilder(lay[0]);
            int lscale = Integer.parseInt(lay[3]);
            int nzeros = lscale < prec ? prec - lscale : 0;
            if (lscale == 0 && ((f & ALT) != 0 || nzeros > 0)) mant.append('.');
            zeros(mant, nzeros);
            magnitude(sb, mant, f, adjustWidth(width, f, neg));
        } else {
            int prec = precision;
            if (precision == -1) prec = 6;
            else if (precision == 0) prec = 1;
            value = value.round(new java.math.MathContext(prec));
            if (value.equals(java.math.BigDecimal.ZERO)
                || (value.compareTo(java.math.BigDecimal.valueOf(1, 4)) != -1
                    && value.compareTo(java.math.BigDecimal.valueOf(1, -prec)) == -1)) {
                int e = -value.scale() + (value.unscaledValue().toString().length() - 1);
                printDecimal(sp, sb, value, 'f', prec - e - 1, neg);
            } else {
                printDecimal(sp, sb, value, 'e', prec - 1, neg);
            }
        }
    }

    /** {mantissa, exponent with its sign (scientific), "d" if the mantissa has a point else "n",
     *  the layout's scale} of unscaled value [intVal] and [scale]. */
    private static String[] layout(java.math.BigInteger intVal, int scale, boolean sci) {
        String coeff = intVal.toString();
        int len = coeff.length();
        StringBuilder mant = new StringBuilder();
        String exp = null;
        boolean dot = false;
        int lscale = scale;
        if (scale == 0) {
            if (len > 1) {
                mant.append(coeff.charAt(0));
                if (sci) {
                    mant.append('.');
                    dot = true;
                    mant.append(coeff, 1, len);
                    exp = len < 10 ? "+0" + (len - 1) : "+" + (len - 1);
                } else {
                    mant.append(coeff, 1, len);
                }
            } else {
                mant.append(coeff);
                if (sci) exp = "+00";
            }
        } else if (!sci) {
            if (scale >= len) {
                mant.append("0.");
                dot = true;
                zeros(mant, scale - len);
                mant.append(coeff);
            } else if (scale > 0) {
                int pad = len - scale;
                mant.append(coeff, 0, pad);
                mant.append('.');
                dot = true;
                mant.append(coeff, pad, len);
            } else {
                mant.append(coeff, 0, len);
                if (intVal.signum() != 0) zeros(mant, -scale);
                lscale = 0;
            }
        } else {
            mant.append(coeff.charAt(0));
            if (len > 1) {
                mant.append('.');
                dot = true;
                mant.append(coeff, 1, len);
            }
            long adjusted = -(long) scale + (len - 1);
            if (adjusted != 0) {
                long abs = Math.abs(adjusted);
                exp = (adjusted < 0 ? "-" : "+") + (abs < 10 ? "0" : "") + abs;
            } else {
                exp = "+00";
            }
        }
        return new String[] {mant.toString(), exp, dot ? "d" : "n", Integer.toString(lscale)};
    }
}

/*
 * rocq-jvm model of java.time.format.DateTimeFormatterBuilder (clean-room, Apache-2.0): JDK 21's
 * builder and printer-parsers for the ISO calendar: composite/optional sections, padding, parse
 * settings, defaults, literals, numbers (sign styles, widths, adjacent value parsing with subsequent
 * widths, more than 18 digits via BigInteger), reduced values (yy, with a base value or base date),
 * fractions (NanosPrinterParser; FractionPrinterParser through BigDecimal), texts (English only, and
 * user-supplied maps), instants, offset ids, zone ids (formatting; parsing of offset-based ids and
 * the UTC/GMT/UT prefixes), with the JDK's exception texts and toString forms; appendPattern with the
 * JDK's letter rules and IllegalArgumentException texts.
 * STUCK: localized patterns and offsets ('O', "ZZZZ"), zone names ('z', 'v'), week-based fields
 * ('Y', 'w', 'W', 'e', 'c'), IsoFields and JulianFields ('Q', 'q', 'g'), day periods ('B'),
 * chronology names, parsing of region zone ids (tz database), the host's default locale where a text
 * needs it, getLocalizedDateTimePattern.
 */
package java.time.format;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.time.DateTimeException;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.ZoneId;
import java.time.ZoneOffset;
import java.time.chrono.ChronoLocalDate;
import java.time.chrono.Chronology;
import java.time.chrono.Era;
import java.time.chrono.IsoChronology;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalField;
import java.time.temporal.TemporalQueries;
import java.time.temporal.TemporalQuery;
import java.time.temporal.ValueRange;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Objects;

public final class DateTimeFormatterBuilder {
    private static final TemporalQuery<ZoneId> QUERY_REGION_ONLY = (temporal) -> {
        ZoneId zone = temporal.query(TemporalQueries.zoneId());
        return zone instanceof ZoneOffset ? null : zone;
    };

    private DateTimeFormatterBuilder active = this;
    private final DateTimeFormatterBuilder parent;
    private final List<DateTimePrinterParser> printerParsers = new ArrayList<>();
    private final boolean optional;
    private int padNextWidth;
    private char padNextChar;
    private int valueParserIndex = -1;

    public DateTimeFormatterBuilder() {
        parent = null;
        optional = false;
    }

    private DateTimeFormatterBuilder(DateTimeFormatterBuilder parent, boolean optional) {
        this.parent = parent;
        this.optional = optional;
    }

    public DateTimeFormatterBuilder parseCaseSensitive() {
        appendInternal(SettingsParser.SENSITIVE);
        return this;
    }

    public DateTimeFormatterBuilder parseCaseInsensitive() {
        appendInternal(SettingsParser.INSENSITIVE);
        return this;
    }

    public DateTimeFormatterBuilder parseStrict() {
        appendInternal(SettingsParser.STRICT);
        return this;
    }

    public DateTimeFormatterBuilder parseLenient() {
        appendInternal(SettingsParser.LENIENT);
        return this;
    }

    public DateTimeFormatterBuilder parseDefaulting(TemporalField field, long value) {
        Objects.requireNonNull(field, "field");
        appendInternal(new DefaultValueParser(field, value));
        return this;
    }

    public DateTimeFormatterBuilder appendValue(TemporalField field) {
        Objects.requireNonNull(field, "field");
        appendValue(new NumberPrinterParser(field, 1, 19, SignStyle.NORMAL));
        return this;
    }

    public DateTimeFormatterBuilder appendValue(TemporalField field, int width) {
        Objects.requireNonNull(field, "field");
        if (width < 1 || width > 19)
            throw new IllegalArgumentException("The width must be from 1 to 19 inclusive but was " + width);
        appendValue(new NumberPrinterParser(field, width, width, SignStyle.NOT_NEGATIVE));
        return this;
    }

    public DateTimeFormatterBuilder appendValue(TemporalField field, int minWidth, int maxWidth, SignStyle signStyle) {
        if (minWidth == maxWidth && signStyle == SignStyle.NOT_NEGATIVE) return appendValue(field, maxWidth);
        Objects.requireNonNull(field, "field");
        Objects.requireNonNull(signStyle, "signStyle");
        if (minWidth < 1 || minWidth > 19)
            throw new IllegalArgumentException("The minimum width must be from 1 to 19 inclusive but was " + minWidth);
        if (maxWidth < 1 || maxWidth > 19)
            throw new IllegalArgumentException("The maximum width must be from 1 to 19 inclusive but was " + maxWidth);
        if (maxWidth < minWidth)
            throw new IllegalArgumentException("The maximum width must exceed or equal the minimum width but "
                + maxWidth + " < " + minWidth);
        appendValue(new NumberPrinterParser(field, minWidth, maxWidth, signStyle));
        return this;
    }

    public DateTimeFormatterBuilder appendValueReduced(TemporalField field, int width, int maxWidth, int baseValue) {
        Objects.requireNonNull(field, "field");
        appendValue(new ReducedPrinterParser(field, width, maxWidth, baseValue, null));
        return this;
    }

    public DateTimeFormatterBuilder appendValueReduced(TemporalField field, int width, int maxWidth, ChronoLocalDate baseDate) {
        Objects.requireNonNull(field, "field");
        Objects.requireNonNull(baseDate, "baseDate");
        appendValue(new ReducedPrinterParser(field, width, maxWidth, 0, baseDate));
        return this;
    }

    private DateTimeFormatterBuilder appendValue(NumberPrinterParser pp) {
        if (active.valueParserIndex >= 0) {
            final int activeValueParser = active.valueParserIndex;
            NumberPrinterParser basePP = (NumberPrinterParser) active.printerParsers.get(activeValueParser);
            if (pp.minWidth == pp.maxWidth && pp.signStyle == SignStyle.NOT_NEGATIVE) {
                basePP = basePP.withSubsequentWidth(pp.maxWidth);
                appendInternal(pp.withFixedWidth());
                active.valueParserIndex = activeValueParser;
            } else {
                basePP = basePP.withFixedWidth();
                active.valueParserIndex = appendInternal(pp);
            }
            active.printerParsers.set(activeValueParser, basePP);
        } else {
            active.valueParserIndex = appendInternal(pp);
        }
        return this;
    }

    public DateTimeFormatterBuilder appendFraction(TemporalField field, int minWidth, int maxWidth, boolean decimalPoint) {
        if (field == ChronoField.NANO_OF_SECOND) {
            if (minWidth == maxWidth && !decimalPoint) {
                appendValue(new NanosPrinterParser(minWidth, maxWidth, decimalPoint));
            } else {
                appendInternal(new NanosPrinterParser(minWidth, maxWidth, decimalPoint));
            }
        } else {
            if (minWidth == maxWidth && !decimalPoint) {
                appendValue(new FractionPrinterParser(field, minWidth, maxWidth, decimalPoint));
            } else {
                appendInternal(new FractionPrinterParser(field, minWidth, maxWidth, decimalPoint));
            }
        }
        return this;
    }

    public DateTimeFormatterBuilder appendText(TemporalField field) {
        return appendText(field, TextStyle.FULL);
    }

    public DateTimeFormatterBuilder appendText(TemporalField field, TextStyle textStyle) {
        Objects.requireNonNull(field, "field");
        Objects.requireNonNull(textStyle, "textStyle");
        appendInternal(new TextPrinterParser(field, textStyle, DateTimeTextProvider.getInstance()));
        return this;
    }

    public DateTimeFormatterBuilder appendText(TemporalField field, Map<Long, String> textLookup) {
        Objects.requireNonNull(field, "field");
        Objects.requireNonNull(textLookup, "textLookup");
        Map<Long, String> copy = new LinkedHashMap<>(textLookup);
        Map<TextStyle, Map<Long, String>> map = new java.util.HashMap<>(); // the JDK's singletonMap: one entry
        map.put(TextStyle.FULL, copy);
        final DateTimeTextProvider.LocaleStore store = new DateTimeTextProvider.LocaleStore(map);
        DateTimeTextProvider provider = new DateTimeTextProvider() {
            @Override
            public String getText(Chronology chrono, TemporalField field, long value, TextStyle style, Locale locale) {
                return store.getText(value, style);
            }

            @Override
            public String getText(TemporalField field, long value, TextStyle style, Locale locale) {
                return store.getText(value, style);
            }

            @Override
            public Iterator<Entry<String, Long>> getTextIterator(Chronology chrono, TemporalField field, TextStyle style,
                                                                 Locale locale) {
                return store.getTextIterator(style);
            }

            @Override
            public Iterator<Entry<String, Long>> getTextIterator(TemporalField field, TextStyle style, Locale locale) {
                return store.getTextIterator(style);
            }
        };
        appendInternal(new TextPrinterParser(field, TextStyle.FULL, provider));
        return this;
    }

    public DateTimeFormatterBuilder appendInstant() {
        appendInternal(new InstantPrinterParser(-2));
        return this;
    }

    public DateTimeFormatterBuilder appendInstant(int fractionalDigits) {
        if (fractionalDigits < -1 || fractionalDigits > 9)
            throw new IllegalArgumentException("The fractional digits must be from -1 to 9 inclusive but was " + fractionalDigits);
        appendInternal(new InstantPrinterParser(fractionalDigits));
        return this;
    }

    public DateTimeFormatterBuilder appendOffsetId() {
        appendInternal(OffsetIdPrinterParser.INSTANCE_ID_Z);
        return this;
    }

    public DateTimeFormatterBuilder appendOffset(String pattern, String noOffsetText) {
        appendInternal(new OffsetIdPrinterParser(pattern, noOffsetText));
        return this;
    }

    public DateTimeFormatterBuilder appendLocalizedOffset(TextStyle style) {
        Objects.requireNonNull(style, "style");
        if (style != TextStyle.FULL && style != TextStyle.SHORT)
            throw new IllegalArgumentException("Style must be either full or short");
        throw ModelStuckFormat.unsupported("DateTimeFormatterBuilder.appendLocalizedOffset: locale resources");
    }

    public DateTimeFormatterBuilder appendZoneId() {
        appendInternal(new ZoneIdPrinterParser(TemporalQueries.zoneId(), "ZoneId()"));
        return this;
    }

    public DateTimeFormatterBuilder appendZoneRegionId() {
        appendInternal(new ZoneIdPrinterParser(QUERY_REGION_ONLY, "ZoneRegionId()"));
        return this;
    }

    public DateTimeFormatterBuilder appendZoneOrOffsetId() {
        appendInternal(new ZoneIdPrinterParser(TemporalQueries.zone(), "ZoneOrOffsetId()"));
        return this;
    }

    public DateTimeFormatterBuilder appendZoneText(TextStyle textStyle) {
        throw ModelStuckFormat.unsupported("DateTimeFormatterBuilder.appendZoneText: zone names");
    }

    public DateTimeFormatterBuilder appendGenericZoneText(TextStyle textStyle) {
        throw ModelStuckFormat.unsupported("DateTimeFormatterBuilder.appendGenericZoneText: zone names");
    }

    public DateTimeFormatterBuilder appendChronologyId() {
        throw ModelStuckFormat.unsupported("DateTimeFormatterBuilder.appendChronologyId: chronology registry");
    }

    public DateTimeFormatterBuilder appendChronologyText(TextStyle textStyle) {
        Objects.requireNonNull(textStyle, "textStyle");
        throw ModelStuckFormat.unsupported("DateTimeFormatterBuilder.appendChronologyText: locale resources");
    }

    public DateTimeFormatterBuilder appendLiteral(char literal) {
        appendInternal(new CharLiteralPrinterParser(literal));
        return this;
    }

    public DateTimeFormatterBuilder appendLiteral(String literal) {
        Objects.requireNonNull(literal, "literal");
        if (!literal.isEmpty()) {
            if (literal.length() == 1) {
                appendInternal(new CharLiteralPrinterParser(literal.charAt(0)));
            } else {
                appendInternal(new StringLiteralPrinterParser(literal));
            }
        }
        return this;
    }

    public DateTimeFormatterBuilder appendDayPeriodText(TextStyle style) {
        Objects.requireNonNull(style, "style");
        throw ModelStuckFormat.unsupported("DateTimeFormatterBuilder.appendDayPeriodText: day periods");
    }

    public DateTimeFormatterBuilder append(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        appendInternal(formatter.toPrinterParser(false));
        return this;
    }

    public DateTimeFormatterBuilder appendOptional(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        appendInternal(formatter.toPrinterParser(true));
        return this;
    }

    public DateTimeFormatterBuilder appendPattern(String pattern) {
        Objects.requireNonNull(pattern, "pattern");
        parsePattern(pattern);
        return this;
    }

    private static boolean isLetter(char c) {
        return (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z');
    }

    private static TemporalField patternField(char c) {
        switch (c) {
            case 'G': return ChronoField.ERA;
            case 'y': return ChronoField.YEAR_OF_ERA;
            case 'u': return ChronoField.YEAR;
            case 'M':
            case 'L': return ChronoField.MONTH_OF_YEAR;
            case 'D': return ChronoField.DAY_OF_YEAR;
            case 'd': return ChronoField.DAY_OF_MONTH;
            case 'F': return ChronoField.ALIGNED_WEEK_OF_MONTH;
            case 'E':
            case 'c':
            case 'e': return ChronoField.DAY_OF_WEEK;
            case 'a': return ChronoField.AMPM_OF_DAY;
            case 'H': return ChronoField.HOUR_OF_DAY;
            case 'k': return ChronoField.CLOCK_HOUR_OF_DAY;
            case 'K': return ChronoField.HOUR_OF_AMPM;
            case 'h': return ChronoField.CLOCK_HOUR_OF_AMPM;
            case 'm': return ChronoField.MINUTE_OF_HOUR;
            case 's': return ChronoField.SECOND_OF_MINUTE;
            case 'S':
            case 'n': return ChronoField.NANO_OF_SECOND;
            case 'A': return ChronoField.MILLI_OF_DAY;
            case 'N': return ChronoField.NANO_OF_DAY;
            case 'Q':
            case 'q': throw ModelStuckFormat.unsupported("pattern letter " + c + ": IsoFields");
            case 'g': throw ModelStuckFormat.unsupported("pattern letter g: JulianFields");
            default: return null;
        }
    }

    private void parsePattern(String pattern) {
        for (int pos = 0; pos < pattern.length(); pos++) {
            char cur = pattern.charAt(pos);
            if (isLetter(cur)) {
                int start = pos++;
                while (pos < pattern.length() && pattern.charAt(pos) == cur) pos++;
                int count = pos - start;
                if (cur == 'p') {
                    int pad = 0;
                    if (pos < pattern.length()) {
                        cur = pattern.charAt(pos);
                        if (isLetter(cur)) {
                            pad = count;
                            start = pos++;
                            while (pos < pattern.length() && pattern.charAt(pos) == cur) pos++;
                            count = pos - start;
                        }
                    }
                    if (pad == 0)
                        throw new IllegalArgumentException("Pad letter 'p' must be followed by valid pad pattern: " + pattern);
                    padNext(pad);
                }
                TemporalField field = patternField(cur);
                if (field != null) {
                    parseField(cur, count, field);
                } else if (cur == 'z') {
                    if (count > 4) throw new IllegalArgumentException("Too many pattern letters: " + cur);
                    appendZoneText(count == 4 ? TextStyle.FULL : TextStyle.SHORT);
                } else if (cur == 'V') {
                    if (count != 2) throw new IllegalArgumentException("Pattern letter count must be 2: " + cur);
                    appendZoneId();
                } else if (cur == 'v') {
                    if (count == 1) {
                        appendGenericZoneText(TextStyle.SHORT);
                    } else if (count == 4) {
                        appendGenericZoneText(TextStyle.FULL);
                    } else {
                        throw new IllegalArgumentException("Wrong number of pattern letters: " + cur);
                    }
                } else if (cur == 'Z') {
                    if (count < 4) {
                        appendOffset("+HHMM", "+0000");
                    } else if (count == 4) {
                        appendLocalizedOffset(TextStyle.FULL);
                    } else if (count == 5) {
                        appendOffset("+HH:MM:ss", "Z");
                    } else {
                        throw new IllegalArgumentException("Too many pattern letters: " + cur);
                    }
                } else if (cur == 'O') {
                    if (count == 1) {
                        appendLocalizedOffset(TextStyle.SHORT);
                    } else if (count == 4) {
                        appendLocalizedOffset(TextStyle.FULL);
                    } else {
                        throw new IllegalArgumentException("Pattern letter count must be 1 or 4: " + cur);
                    }
                } else if (cur == 'X') {
                    if (count > 5) throw new IllegalArgumentException("Too many pattern letters: " + cur);
                    appendOffset(OffsetIdPrinterParser.PATTERNS[count + (count == 1 ? 0 : 1)], "Z");
                } else if (cur == 'x') {
                    if (count > 5) throw new IllegalArgumentException("Too many pattern letters: " + cur);
                    String zero = count == 1 ? "+00" : (count % 2 == 0 ? "+0000" : "+00:00");
                    appendOffset(OffsetIdPrinterParser.PATTERNS[count + (count == 1 ? 0 : 1)], zero);
                } else if (cur == 'W') {
                    if (count > 1) throw new IllegalArgumentException("Too many pattern letters: " + cur);
                    throw ModelStuckFormat.unsupported("pattern letter W: WeekFields of the locale");
                } else if (cur == 'w') {
                    if (count > 2) throw new IllegalArgumentException("Too many pattern letters: " + cur);
                    throw ModelStuckFormat.unsupported("pattern letter w: WeekFields of the locale");
                } else if (cur == 'Y') {
                    throw ModelStuckFormat.unsupported("pattern letter Y: WeekFields of the locale");
                } else if (cur == 'B') {
                    if (count != 1 && count != 4 && count != 5)
                        throw new IllegalArgumentException("Wrong number of pattern letters: " + cur);
                    appendDayPeriodText(TextStyle.SHORT);
                } else {
                    throw new IllegalArgumentException("Unknown pattern letter: " + cur);
                }
                pos--;
            } else if (cur == '\'') {
                int start = pos++;
                for (; pos < pattern.length(); pos++) {
                    if (pattern.charAt(pos) == '\'') {
                        if (pos + 1 < pattern.length() && pattern.charAt(pos + 1) == '\'') {
                            pos++;
                        } else {
                            break;
                        }
                    }
                }
                if (pos >= pattern.length())
                    throw new IllegalArgumentException("Pattern ends with an incomplete string literal: " + pattern);
                String str = pattern.substring(start + 1, pos);
                if (str.isEmpty()) {
                    appendLiteral('\'');
                } else {
                    appendLiteral(str.replace("''", "'"));
                }
            } else if (cur == '[') {
                optionalStart();
            } else if (cur == ']') {
                if (active.parent == null)
                    throw new IllegalArgumentException("Pattern invalid as it contains ] without previous [");
                optionalEnd();
            } else if (cur == '{' || cur == '}' || cur == '#') {
                throw new IllegalArgumentException("Pattern includes reserved character: '" + cur + "'");
            } else {
                appendLiteral(cur);
            }
        }
    }

    private void parseField(char cur, int count, TemporalField field) {
        boolean standalone = false;
        switch (cur) {
            case 'u':
            case 'y':
                if (count == 2) {
                    appendValueReduced(field, 2, 2, ReducedPrinterParser.BASE_DATE);
                } else if (count < 4) {
                    appendValue(field, count, 19, SignStyle.NORMAL);
                } else {
                    appendValue(field, count, 19, SignStyle.EXCEEDS_PAD);
                }
                return;
            case 'c':
                if (count == 1) throw ModelStuckFormat.unsupported("pattern letter c: WeekFields of the locale");
                if (count == 2) throw new IllegalArgumentException("Invalid pattern \"cc\"");
                standalone = true;
                break;
            case 'L':
                standalone = true;
                break;
            case 'M':
            case 'E':
            case 'e':
                break;
            case 'a':
                if (count == 1) {
                    appendText(field, TextStyle.SHORT);
                } else {
                    throw new IllegalArgumentException("Too many pattern letters: " + cur);
                }
                return;
            case 'G':
                if (count <= 3) {
                    appendText(field, TextStyle.SHORT);
                } else if (count == 4) {
                    appendText(field, TextStyle.FULL);
                } else if (count == 5) {
                    appendText(field, TextStyle.NARROW);
                } else {
                    throw new IllegalArgumentException("Too many pattern letters: " + cur);
                }
                return;
            case 'S':
                appendFraction(ChronoField.NANO_OF_SECOND, count, count, false);
                return;
            case 'F':
                if (count == 1) {
                    appendValue(field);
                } else {
                    throw new IllegalArgumentException("Too many pattern letters: " + cur);
                }
                return;
            case 'd':
            case 'h':
            case 'H':
            case 'k':
            case 'K':
            case 'm':
            case 's':
                if (count == 1) {
                    appendValue(field);
                } else if (count == 2) {
                    appendValue(field, count);
                } else {
                    throw new IllegalArgumentException("Too many pattern letters: " + cur);
                }
                return;
            case 'D':
                if (count == 1) {
                    appendValue(field);
                } else if (count == 2 || count == 3) {
                    appendValue(field, count, 3, SignStyle.NOT_NEGATIVE);
                } else {
                    throw new IllegalArgumentException("Too many pattern letters: " + cur);
                }
                return;
            case 'A':
            case 'n':
            case 'N':
                appendValue(field, count, 19, SignStyle.NOT_NEGATIVE);
                return;
            default:
                if (count == 1) {
                    appendValue(field);
                } else {
                    appendValue(field, count);
                }
                return;
        }
        // M L E e c: numbers or texts by count
        switch (count) {
            case 1:
            case 2:
                if (cur == 'e') {
                    throw ModelStuckFormat.unsupported("pattern letter e: WeekFields of the locale");
                } else if (cur == 'E') {
                    appendText(field, TextStyle.SHORT);
                } else if (count == 1) {
                    appendValue(field);
                } else {
                    appendValue(field, 2);
                }
                break;
            case 3:
                appendText(field, standalone ? TextStyle.SHORT_STANDALONE : TextStyle.SHORT);
                break;
            case 4:
                appendText(field, standalone ? TextStyle.FULL_STANDALONE : TextStyle.FULL);
                break;
            case 5:
                appendText(field, standalone ? TextStyle.NARROW_STANDALONE : TextStyle.NARROW);
                break;
            default:
                throw new IllegalArgumentException("Too many pattern letters: " + cur);
        }
    }

    public DateTimeFormatterBuilder padNext(int padWidth) {
        return padNext(padWidth, ' ');
    }

    public DateTimeFormatterBuilder padNext(int padWidth, char padChar) {
        if (padWidth < 1) throw new IllegalArgumentException("The pad width must be at least one but was " + padWidth);
        active.padNextWidth = padWidth;
        active.padNextChar = padChar;
        active.valueParserIndex = -1;
        return this;
    }

    public DateTimeFormatterBuilder optionalStart() {
        active.valueParserIndex = -1;
        active = new DateTimeFormatterBuilder(active, true);
        return this;
    }

    public DateTimeFormatterBuilder optionalEnd() {
        if (active.parent == null)
            throw new IllegalStateException("Cannot call optionalEnd() as there was no previous call to optionalStart()");
        if (active.printerParsers.size() > 0) {
            CompositePrinterParser cpp = new CompositePrinterParser(active.printerParsers, active.optional);
            active = active.parent;
            appendInternal(cpp);
        } else {
            active = active.parent;
        }
        return this;
    }

    /** A printer-parser that the model does not have (it is STUCK when used). */
    DateTimeFormatterBuilder appendStuck(String what) {
        appendInternal(new StuckPrinterParser(what));
        return this;
    }

    private int appendInternal(DateTimePrinterParser pp) {
        Objects.requireNonNull(pp, "pp");
        if (active.padNextWidth > 0) {
            pp = new PadPrinterParserDecorator(pp, active.padNextWidth, active.padNextChar);
            active.padNextWidth = 0;
            active.padNextChar = 0;
        }
        active.printerParsers.add(pp);
        active.valueParserIndex = -1;
        return active.printerParsers.size() - 1;
    }

    /** The host's default locale is unknown to the model: the formatter's locale is null, and every
     *  use of it is STUCK (DateTimeFormatter.getLocale). */
    public DateTimeFormatter toFormatter() {
        return toFormatter0(null, ResolverStyle.SMART, null);
    }

    public DateTimeFormatter toFormatter(Locale locale) {
        Objects.requireNonNull(locale, "locale");
        return toFormatter0(locale, ResolverStyle.SMART, null);
    }

    DateTimeFormatter toFormatter(ResolverStyle resolverStyle, Chronology chrono) {
        return toFormatter0(null, resolverStyle, chrono);
    }

    private DateTimeFormatter toFormatter0(Locale locale, ResolverStyle resolverStyle, Chronology chrono) {
        while (active.parent != null) optionalEnd();
        CompositePrinterParser pp = new CompositePrinterParser(printerParsers, false);
        return new DateTimeFormatter(pp, locale, DecimalStyle.STANDARD, resolverStyle, null, chrono, null);
    }

    //-----------------------------------------------------------------------
    interface DateTimePrinterParser {
        boolean format(DateTimePrintContext context, StringBuilder buf);

        int parse(DateTimeParseContext context, CharSequence text, int position);
    }

    /** A placeholder for a JDK printer-parser that is not modelled (e.g. in ISO_WEEK_DATE). */
    static final class StuckPrinterParser implements DateTimePrinterParser {
        private final String what;

        StuckPrinterParser(String what) {
            this.what = what;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            throw ModelStuckFormat.unsupported(what);
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            throw ModelStuckFormat.unsupported(what);
        }

        @Override
        public String toString() {
            throw ModelStuckFormat.unsupported(what);
        }
    }

    static final class CompositePrinterParser implements DateTimePrinterParser {
        private final DateTimePrinterParser[] printerParsers;
        private final boolean optional;

        CompositePrinterParser(List<DateTimePrinterParser> printerParsers, boolean optional) {
            this(printerParsers.toArray(new DateTimePrinterParser[0]), optional);
        }

        CompositePrinterParser(DateTimePrinterParser[] printerParsers, boolean optional) {
            this.printerParsers = printerParsers;
            this.optional = optional;
        }

        public CompositePrinterParser withOptional(boolean optional) {
            if (optional == this.optional) return this;
            return new CompositePrinterParser(printerParsers, optional);
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            int length = buf.length();
            if (optional) context.startOptional();
            try {
                for (DateTimePrinterParser pp : printerParsers) {
                    if (!pp.format(context, buf)) {
                        buf.setLength(length);
                        return true;
                    }
                }
            } finally {
                if (optional) context.endOptional();
            }
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            if (optional) {
                context.startOptional();
                int pos = position;
                for (DateTimePrinterParser pp : printerParsers) {
                    pos = pp.parse(context, text, pos);
                    if (pos < 0) {
                        context.endOptional(false);
                        return position;
                    }
                }
                context.endOptional(true);
                return pos;
            }
            for (DateTimePrinterParser pp : printerParsers) {
                position = pp.parse(context, text, position);
                if (position < 0) break;
            }
            return position;
        }

        @Override
        public String toString() {
            StringBuilder buf = new StringBuilder();
            if (printerParsers != null) {
                buf.append(optional ? "[" : "(");
                for (DateTimePrinterParser pp : printerParsers) buf.append(pp);
                buf.append(optional ? "]" : ")");
            }
            return buf.toString();
        }
    }

    static final class PadPrinterParserDecorator implements DateTimePrinterParser {
        private final DateTimePrinterParser printerParser;
        private final int padWidth;
        private final char padChar;

        PadPrinterParserDecorator(DateTimePrinterParser printerParser, int padWidth, char padChar) {
            this.printerParser = printerParser;
            this.padWidth = padWidth;
            this.padChar = padChar;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            int preLen = buf.length();
            if (!printerParser.format(context, buf)) return false;
            int len = buf.length() - preLen;
            if (len > padWidth)
                throw new DateTimeException("Cannot print as output of " + len + " characters exceeds pad width of " + padWidth);
            int count = padWidth - len;
            if (count == 0) return true;
            if (count == 1) {
                buf.insert(preLen, padChar);
                return true;
            }
            buf.insert(preLen, String.valueOf(padChar).repeat(count));
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            final boolean strict = context.isStrict();
            if (position > text.length()) throw new IndexOutOfBoundsException();
            if (position == text.length()) return ~position;
            int endPos = position + padWidth;
            if (endPos > text.length()) {
                if (strict) return ~position;
                endPos = text.length();
            }
            int pos = position;
            while (pos < endPos && context.charEquals(text.charAt(pos), padChar)) pos++;
            text = text.subSequence(0, endPos);
            int resultPos = printerParser.parse(context, text, pos);
            if (resultPos != endPos && strict) return ~(position + pos);
            return resultPos;
        }

        @Override
        public String toString() {
            return "Pad(" + printerParser + "," + padWidth + (padChar == ' ' ? ")" : ",'" + padChar + "')");
        }
    }

    static enum SettingsParser implements DateTimePrinterParser {
        SENSITIVE,
        INSENSITIVE,
        STRICT,
        LENIENT;

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            switch (ordinal()) {
                case 0: context.setCaseSensitive(true); break;
                case 1: context.setCaseSensitive(false); break;
                case 2: context.setStrict(true); break;
                case 3: context.setStrict(false); break;
                default: break;
            }
            return position;
        }

        @Override
        public String toString() {
            switch (ordinal()) {
                case 0: return "ParseCaseSensitive(true)";
                case 1: return "ParseCaseSensitive(false)";
                case 2: return "ParseStrict(true)";
                case 3: return "ParseStrict(false)";
                default: throw new IllegalStateException("Unreachable");
            }
        }
    }

    static class DefaultValueParser implements DateTimePrinterParser {
        private final TemporalField field;
        private final long value;

        DefaultValueParser(TemporalField field, long value) {
            this.field = field;
            this.value = value;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            if (context.getParsed(field) == null) context.setParsedField(field, value, position, position);
            return position;
        }

        // no toString: Object.toString (class name and identity hash code), as in the JDK
    }

    static final class CharLiteralPrinterParser implements DateTimePrinterParser {
        private final char literal;

        CharLiteralPrinterParser(char literal) {
            this.literal = literal;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            buf.append(literal);
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            int length = text.length();
            if (position == length) return ~position;
            char ch = text.charAt(position);
            if (ch != literal) {
                if (context.isCaseSensitive() || (Character.toUpperCase(ch) != Character.toUpperCase(literal)
                    && Character.toLowerCase(ch) != Character.toLowerCase(literal))) return ~position;
            }
            return position + 1;
        }

        @Override
        public String toString() {
            if (literal == '\'') return "''";
            return "'" + literal + "'";
        }
    }

    static final class StringLiteralPrinterParser implements DateTimePrinterParser {
        private final String literal;

        StringLiteralPrinterParser(String literal) {
            this.literal = literal;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            buf.append(literal);
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            int length = text.length();
            if (position > length || position < 0) throw new IndexOutOfBoundsException();
            if (!context.subSequenceEquals(text, position, literal, 0, literal.length())) return ~position;
            return position + literal.length();
        }

        @Override
        public String toString() {
            return "'" + literal.replace("'", "''") + "'";
        }
    }

    static class NumberPrinterParser implements DateTimePrinterParser {
        static final long[] EXCEED_POINTS = {0L, 10L, 100L, 1000L, 10000L, 100000L, 1000000L, 10000000L, 100000000L,
            1000000000L, 10000000000L};

        final TemporalField field;
        final int minWidth;
        final int maxWidth;
        final SignStyle signStyle;
        final int subsequentWidth;

        NumberPrinterParser(TemporalField field, int minWidth, int maxWidth, SignStyle signStyle) {
            this(field, minWidth, maxWidth, signStyle, 0);
        }

        protected NumberPrinterParser(TemporalField field, int minWidth, int maxWidth, SignStyle signStyle, int subsequentWidth) {
            this.field = field;
            this.minWidth = minWidth;
            this.maxWidth = maxWidth;
            this.signStyle = signStyle;
            this.subsequentWidth = subsequentWidth;
        }

        NumberPrinterParser withFixedWidth() {
            if (subsequentWidth == -1) return this;
            return new NumberPrinterParser(field, minWidth, maxWidth, signStyle, -1);
        }

        NumberPrinterParser withSubsequentWidth(int subsequentWidth) {
            return new NumberPrinterParser(field, minWidth, maxWidth, signStyle, this.subsequentWidth + subsequentWidth);
        }

        private static int stringSize(long x) {
            int d = 1;
            if (x >= 0) {
                d = 0;
                x = -x;
            }
            long p = -10;
            for (int i = 1; i < 19; i++) {
                if (x > p) return i + d;
                p = 10 * p;
            }
            return 19 + d;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            Long valueLong = context.getValue(field);
            if (valueLong == null) return false;
            long value = getValue(context, valueLong);
            DecimalStyle decimalStyle = context.getDecimalStyle();
            int size = stringSize(value);
            if (value < 0) size--;
            if (size > maxWidth)
                throw new DateTimeException("Field " + field + " cannot be printed as the value " + value
                    + " exceeds the maximum print width of " + maxWidth);
            if (value >= 0) {
                if (signStyle == SignStyle.EXCEEDS_PAD) {
                    if (minWidth < 19 && size > minWidth) buf.append(decimalStyle.getPositiveSign());
                } else if (signStyle == SignStyle.ALWAYS) {
                    buf.append(decimalStyle.getPositiveSign());
                }
            } else {
                if (signStyle == SignStyle.NORMAL || signStyle == SignStyle.EXCEEDS_PAD || signStyle == SignStyle.ALWAYS) {
                    buf.append(decimalStyle.getNegativeSign());
                } else if (signStyle == SignStyle.NOT_NEGATIVE) {
                    throw new DateTimeException("Field " + field + " cannot be printed as the value " + value
                        + " cannot be negative according to the SignStyle");
                }
            }
            char zeroDigit = decimalStyle.getZeroDigit();
            for (int i = 0; i < minWidth - size; i++) buf.append(zeroDigit);
            if (zeroDigit == '0' && value != Long.MIN_VALUE) {
                buf.append(Math.abs(value));
            } else {
                String str = value == Long.MIN_VALUE ? "9223372036854775808" : Long.toString(Math.abs(value));
                buf.append(decimalStyle.convertNumberToI18N(str));
            }
            return true;
        }

        long getValue(DateTimePrintContext context, long value) {
            return value;
        }

        boolean isFixedWidth(DateTimeParseContext context) {
            return subsequentWidth == -1 || (subsequentWidth > 0 && minWidth == maxWidth && signStyle == SignStyle.NOT_NEGATIVE);
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            int length = text.length();
            if (position == length) return ~position;
            char sign = text.charAt(position);
            boolean negative = false;
            boolean positive = false;
            if (sign == context.getDecimalStyle().getPositiveSign()) {
                if (!signStyle.parse(true, context.isStrict(), minWidth == maxWidth)) return ~position;
                positive = true;
                position++;
            } else if (sign == context.getDecimalStyle().getNegativeSign()) {
                if (!signStyle.parse(false, context.isStrict(), minWidth == maxWidth)) return ~position;
                negative = true;
                position++;
            } else if (signStyle == SignStyle.ALWAYS && context.isStrict()) {
                return ~position;
            }
            int effMinWidth = (context.isStrict() || isFixedWidth(context)) ? minWidth : 1;
            int minEndPos = position + effMinWidth;
            if (minEndPos > length) return ~position;
            int effMaxWidth = ((context.isStrict() || isFixedWidth(context)) ? maxWidth : 9) + Math.max(subsequentWidth, 0);
            long total = 0;
            BigInteger totalBig = null;
            int pos = position;
            for (int pass = 0; pass < 2; pass++) {
                int maxEndPos = Math.min(pos + effMaxWidth, length);
                while (pos < maxEndPos) {
                    char ch = text.charAt(pos++);
                    int digit = context.getDecimalStyle().convertToDigit(ch);
                    if (digit < 0) {
                        pos--;
                        if (pos < minEndPos) return ~position;
                        break;
                    }
                    if ((pos - position) > 18) {
                        if (totalBig == null) totalBig = BigInteger.valueOf(total);
                        totalBig = totalBig.multiply(BigInteger.TEN).add(BigInteger.valueOf(digit));
                    } else {
                        total = total * 10 + digit;
                    }
                }
                if (subsequentWidth > 0 && pass == 0) {
                    int parseLen = pos - position;
                    effMaxWidth = Math.max(effMinWidth, parseLen - subsequentWidth);
                    pos = position;
                    total = 0;
                    totalBig = null;
                } else {
                    break;
                }
            }
            if (negative) {
                if (totalBig != null) {
                    if (totalBig.equals(BigInteger.ZERO) && context.isStrict()) return ~(position - 1);
                    totalBig = totalBig.negate();
                } else {
                    if (total == 0 && context.isStrict()) return ~(position - 1);
                    total = -total;
                }
            } else if (signStyle == SignStyle.EXCEEDS_PAD && context.isStrict()) {
                int parseLen = pos - position;
                if (positive) {
                    if (parseLen <= minWidth) return ~(position - 1);
                } else {
                    if (parseLen > minWidth) return ~position;
                }
            }
            if (totalBig != null) {
                if (totalBig.bitLength() > 63) {
                    totalBig = totalBig.divide(BigInteger.TEN);
                    pos--;
                }
                return setValue(context, totalBig.longValue(), position, pos);
            }
            return setValue(context, total, position, pos);
        }

        int setValue(DateTimeParseContext context, long value, int errorPos, int successPos) {
            return context.setParsedField(field, value, errorPos, successPos);
        }

        @Override
        public String toString() {
            if (minWidth == 1 && maxWidth == 19 && signStyle == SignStyle.NORMAL) return "Value(" + field + ")";
            if (minWidth == maxWidth && signStyle == SignStyle.NOT_NEGATIVE) return "Value(" + field + "," + minWidth + ")";
            return "Value(" + field + "," + minWidth + "," + maxWidth + "," + signStyle + ")";
        }
    }

    static final class ReducedPrinterParser extends NumberPrinterParser {
        static final LocalDate BASE_DATE = LocalDate.of(2000, 1, 1);
        private final int baseValue;
        private final ChronoLocalDate baseDate;

        ReducedPrinterParser(TemporalField field, int minWidth, int maxWidth, int baseValue, ChronoLocalDate baseDate) {
            this(field, minWidth, maxWidth, baseValue, baseDate, 0);
            if (minWidth < 1 || minWidth > 10)
                throw new IllegalArgumentException("The minWidth must be from 1 to 10 inclusive but was " + minWidth);
            if (maxWidth < 1 || maxWidth > 10)
                throw new IllegalArgumentException("The maxWidth must be from 1 to 10 inclusive but was " + minWidth);
            if (maxWidth < minWidth)
                throw new IllegalArgumentException("Maximum width must exceed or equal the minimum width but "
                    + maxWidth + " < " + minWidth);
            if (baseDate == null) {
                if (!field.range().isValidValue(baseValue))
                    throw new IllegalArgumentException("The base value must be within the range of the field");
                if ((((long) baseValue) + EXCEED_POINTS[maxWidth]) > Integer.MAX_VALUE)
                    throw new DateTimeException("Unable to add printer-parser as the range exceeds the capacity of an int");
            }
        }

        private ReducedPrinterParser(TemporalField field, int minWidth, int maxWidth, int baseValue, ChronoLocalDate baseDate,
                                     int subsequentWidth) {
            super(field, minWidth, maxWidth, SignStyle.NOT_NEGATIVE, subsequentWidth);
            this.baseValue = baseValue;
            this.baseDate = baseDate;
        }

        private static ChronoLocalDate isoBase(Chronology chrono, ChronoLocalDate baseDate) {
            if (chrono != IsoChronology.INSTANCE)
                throw ModelStuckFormat.unsupported("ReducedPrinterParser: base date in a non-ISO chronology");
            return chrono.date(baseDate);
        }

        @Override
        long getValue(DateTimePrintContext context, long value) {
            long absValue = Math.abs(value);
            int base = this.baseValue;
            if (baseDate != null) {
                Chronology chrono = Chronology.from(context.getTemporal());
                base = isoBase(chrono, baseDate).get(field);
            }
            if (value >= base && value < base + EXCEED_POINTS[minWidth]) return absValue % EXCEED_POINTS[minWidth];
            return absValue % EXCEED_POINTS[maxWidth];
        }

        @Override
        int setValue(DateTimeParseContext context, long value, int errorPos, int successPos) {
            int base = this.baseValue;
            if (baseDate != null) {
                Chronology chrono = context.getEffectiveChronology();
                base = isoBase(chrono, baseDate).get(field);
            }
            int parseLen = successPos - errorPos;
            if (parseLen == minWidth && value >= 0) {
                long range = EXCEED_POINTS[minWidth];
                long lastPart = base % range;
                long basePart = base - lastPart;
                if (base > 0) {
                    value = basePart + value;
                } else {
                    value = basePart - value;
                }
                if (value < base) value += range;
            }
            return context.setParsedField(field, value, errorPos, successPos);
        }

        @Override
        ReducedPrinterParser withFixedWidth() {
            if (subsequentWidth == -1) return this;
            return new ReducedPrinterParser(field, minWidth, maxWidth, baseValue, baseDate, -1);
        }

        @Override
        ReducedPrinterParser withSubsequentWidth(int subsequentWidth) {
            return new ReducedPrinterParser(field, minWidth, maxWidth, baseValue, baseDate, this.subsequentWidth + subsequentWidth);
        }

        @Override
        boolean isFixedWidth(DateTimeParseContext context) {
            if (!context.isStrict()) return false;
            return super.isFixedWidth(context);
        }

        @Override
        public String toString() {
            return "ReducedValue(" + field + "," + minWidth + "," + maxWidth + ","
                + (baseDate != null ? (Object) baseDate : (Object) baseValue) + ")";
        }
    }

    static final class NanosPrinterParser extends NumberPrinterParser {
        private final boolean decimalPoint;
        private static final int[] TENS = {1, 10, 100, 1000, 10000, 100000, 1000000, 10000000, 100000000};

        NanosPrinterParser(int minWidth, int maxWidth, boolean decimalPoint) {
            this(minWidth, maxWidth, decimalPoint, 0);
            if (minWidth < 0 || minWidth > 9)
                throw new IllegalArgumentException("Minimum width must be from 0 to 9 inclusive but was " + minWidth);
            if (maxWidth < 1 || maxWidth > 9)
                throw new IllegalArgumentException("Maximum width must be from 1 to 9 inclusive but was " + maxWidth);
            if (maxWidth < minWidth)
                throw new IllegalArgumentException("Maximum width must exceed or equal the minimum width but "
                    + maxWidth + " < " + minWidth);
        }

        private NanosPrinterParser(int minWidth, int maxWidth, boolean decimalPoint, int subsequentWidth) {
            super(ChronoField.NANO_OF_SECOND, minWidth, maxWidth, SignStyle.NOT_NEGATIVE, subsequentWidth);
            this.decimalPoint = decimalPoint;
        }

        @Override
        NanosPrinterParser withFixedWidth() {
            if (subsequentWidth == -1) return this;
            return new NanosPrinterParser(minWidth, maxWidth, decimalPoint, -1);
        }

        @Override
        NanosPrinterParser withSubsequentWidth(int subsequentWidth) {
            return new NanosPrinterParser(minWidth, maxWidth, decimalPoint, this.subsequentWidth + subsequentWidth);
        }

        @Override
        boolean isFixedWidth(DateTimeParseContext context) {
            return context.isStrict() && minWidth == maxWidth && !decimalPoint;
        }

        private static int stringSize(int x) {
            int p = 10;
            for (int i = 1; i < 10; i++) {
                if (x < p) return i;
                p = 10 * p;
            }
            return 10;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            Long value = context.getValue(field);
            if (value == null) return false;
            int val = field.range().checkValidIntValue(value, field);
            DecimalStyle decimalStyle = context.getDecimalStyle();
            int stringSize = stringSize(val);
            char zero = decimalStyle.getZeroDigit();
            if (val == 0 || stringSize < 10 - maxWidth) {
                int width = val == 0 ? minWidth : maxWidth;
                if (width > 0) {
                    if (decimalPoint) buf.append(decimalStyle.getDecimalSeparator());
                    for (int i = 0; i < width; i++) buf.append(zero);
                }
            } else {
                if (decimalPoint) buf.append(decimalStyle.getDecimalSeparator());
                for (int i = 9 - stringSize; i > 0; i--) buf.append(zero);
                if (maxWidth < 9) val /= TENS[9 - maxWidth];
                for (int i = maxWidth; i > minWidth; i--) {
                    if ((val % 10) != 0) break;
                    val /= 10;
                }
                if (zero == '0') {
                    buf.append(val);
                } else {
                    buf.append(decimalStyle.convertNumberToI18N(Integer.toString(val)));
                }
            }
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            int effectiveMin = (context.isStrict() || isFixedWidth(context)) ? minWidth : 0;
            int effectiveMax = (context.isStrict() || isFixedWidth(context)) ? maxWidth : 9;
            int length = text.length();
            if (position == length) return effectiveMin > 0 ? ~position : position;
            if (decimalPoint) {
                if (text.charAt(position) != context.getDecimalStyle().getDecimalSeparator())
                    return effectiveMin > 0 ? ~position : position;
                position++;
            }
            int minEndPos = position + effectiveMin;
            if (minEndPos > length) return ~position;
            int maxEndPos = Math.min(position + effectiveMax, length);
            int total = 0;
            int pos = position;
            while (pos < maxEndPos) {
                char ch = text.charAt(pos);
                int digit = context.getDecimalStyle().convertToDigit(ch);
                if (digit < 0) {
                    if (pos < minEndPos) return ~position;
                    break;
                }
                pos++;
                total = total * 10 + digit;
            }
            for (int i = 9 - (pos - position); i > 0; i--) total *= 10;
            return context.setParsedField(field, total, position, pos);
        }

        @Override
        public String toString() {
            return "Fraction(" + field + "," + minWidth + "," + maxWidth + (decimalPoint ? ",DecimalPoint" : "") + ")";
        }
    }

    static final class FractionPrinterParser extends NumberPrinterParser {
        private final boolean decimalPoint;
        private final BigDecimal minBD;
        private final BigDecimal rangeBD;

        FractionPrinterParser(TemporalField field, int minWidth, int maxWidth, boolean decimalPoint) {
            this(field, minWidth, maxWidth, decimalPoint, 0);
            Objects.requireNonNull(field, "field");
            if (!field.range().isFixed())
                throw new IllegalArgumentException("Field must have a fixed set of values: " + field);
            if (minWidth < 0 || minWidth > 9)
                throw new IllegalArgumentException("Minimum width must be from 0 to 9 inclusive but was " + minWidth);
            if (maxWidth < 1 || maxWidth > 9)
                throw new IllegalArgumentException("Maximum width must be from 1 to 9 inclusive but was " + maxWidth);
            if (maxWidth < minWidth)
                throw new IllegalArgumentException("Maximum width must exceed or equal the minimum width but "
                    + maxWidth + " < " + minWidth);
        }

        private FractionPrinterParser(TemporalField field, int minWidth, int maxWidth, boolean decimalPoint, int subsequentWidth) {
            super(field, minWidth, maxWidth, SignStyle.NOT_NEGATIVE, subsequentWidth);
            this.decimalPoint = decimalPoint;
            ValueRange range = field.range();
            this.minBD = BigDecimal.valueOf(range.getMinimum());
            this.rangeBD = BigDecimal.valueOf(range.getMaximum()).subtract(minBD).add(BigDecimal.ONE);
        }

        @Override
        FractionPrinterParser withFixedWidth() {
            if (subsequentWidth == -1) return this;
            return new FractionPrinterParser(field, minWidth, maxWidth, decimalPoint, -1);
        }

        @Override
        FractionPrinterParser withSubsequentWidth(int subsequentWidth) {
            return new FractionPrinterParser(field, minWidth, maxWidth, decimalPoint, this.subsequentWidth + subsequentWidth);
        }

        @Override
        boolean isFixedWidth(DateTimeParseContext context) {
            return context.isStrict() && minWidth == maxWidth && !decimalPoint;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            Long value = context.getValue(field);
            if (value == null) return false;
            DecimalStyle decimalStyle = context.getDecimalStyle();
            BigDecimal fraction = convertToFraction(value);
            if (fraction.scale() == 0) {
                if (minWidth > 0) {
                    if (decimalPoint) buf.append(decimalStyle.getDecimalSeparator());
                    for (int i = 0; i < minWidth; i++) buf.append(decimalStyle.getZeroDigit());
                }
            } else {
                int outputScale = Math.min(Math.max(fraction.scale(), minWidth), maxWidth);
                fraction = fraction.setScale(outputScale, RoundingMode.FLOOR);
                if (decimalPoint) buf.append(decimalStyle.getDecimalSeparator());
                String str = decimalStyle.convertNumberToI18N(fraction.toPlainString());
                buf.append(str, 2, str.length());
            }
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            int effectiveMin = (context.isStrict() || isFixedWidth(context)) ? minWidth : 0;
            int effectiveMax = (context.isStrict() || isFixedWidth(context)) ? maxWidth : 9;
            int length = text.length();
            if (position == length) return effectiveMin > 0 ? ~position : position;
            if (decimalPoint) {
                if (text.charAt(position) != context.getDecimalStyle().getDecimalSeparator())
                    return effectiveMin > 0 ? ~position : position;
                position++;
            }
            int minEndPos = position + effectiveMin;
            if (minEndPos > length) return ~position;
            int maxEndPos = Math.min(position + effectiveMax, length);
            int total = 0;
            int pos = position;
            while (pos < maxEndPos) {
                char ch = text.charAt(pos++);
                int digit = context.getDecimalStyle().convertToDigit(ch);
                if (digit < 0) {
                    if (pos <= minEndPos) return ~position;
                    pos--;
                    break;
                }
                total = total * 10 + digit;
            }
            BigDecimal fraction = new BigDecimal(total).movePointLeft(pos - position);
            long value = convertFromFraction(fraction);
            return context.setParsedField(field, value, position, pos);
        }

        private BigDecimal convertToFraction(long value) {
            field.range().checkValidValue(value, field);
            BigDecimal valueBD = BigDecimal.valueOf(value).subtract(minBD);
            BigDecimal fraction = valueBD.divide(rangeBD, 9, RoundingMode.FLOOR);
            return fraction.compareTo(BigDecimal.ZERO) == 0 ? BigDecimal.ZERO : fraction.stripTrailingZeros();
        }

        private long convertFromFraction(BigDecimal fraction) {
            BigDecimal valueBD = fraction.multiply(rangeBD).setScale(0, RoundingMode.FLOOR).add(minBD);
            return valueBD.longValueExact();
        }

        @Override
        public String toString() {
            return "Fraction(" + field + "," + minWidth + "," + maxWidth + (decimalPoint ? ",DecimalPoint" : "") + ")";
        }
    }

    static final class TextPrinterParser implements DateTimePrinterParser {
        private final TemporalField field;
        private final TextStyle textStyle;
        private final DateTimeTextProvider provider;
        private NumberPrinterParser numberPrinterParser;

        TextPrinterParser(TemporalField field, TextStyle textStyle, DateTimeTextProvider provider) {
            this.field = field;
            this.textStyle = textStyle;
            this.provider = provider;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            Long value = context.getValue(field);
            if (value == null) return false;
            String text;
            Chronology chrono = context.getTemporal().query(TemporalQueries.chronology());
            if (chrono == null || chrono == IsoChronology.INSTANCE) {
                text = provider.getText(field, value, textStyle, context.getLocale());
            } else {
                text = provider.getText(chrono, field, value, textStyle, context.getLocale());
            }
            if (text == null) return numberPrinterParser().format(context, buf);
            buf.append(text);
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence parseText, int position) {
            int length = parseText.length();
            if (position < 0 || position > length) throw new IndexOutOfBoundsException();
            TextStyle style = context.isStrict() ? textStyle : null;
            Chronology chrono = context.getEffectiveChronology();
            Iterator<Entry<String, Long>> it;
            if (chrono == null || chrono == IsoChronology.INSTANCE) {
                it = provider.getTextIterator(field, style, context.getLocale());
            } else {
                it = provider.getTextIterator(chrono, field, style, context.getLocale());
            }
            if (it != null) {
                while (it.hasNext()) {
                    Entry<String, Long> entry = it.next();
                    String itText = entry.getKey();
                    if (context.subSequenceEquals(itText, 0, parseText, position, itText.length()))
                        return context.setParsedField(field, entry.getValue(), position, position + itText.length());
                }
                if (field == ChronoField.ERA && !context.isStrict()) {
                    List<Era> eras = chrono.eras();
                    for (Era era : eras) {
                        String name = era.toString();
                        if (context.subSequenceEquals(name, 0, parseText, position, name.length()))
                            return context.setParsedField(field, era.getValue(), position, position + name.length());
                    }
                }
                if (context.isStrict()) return ~position;
            }
            return numberPrinterParser().parse(context, parseText, position);
        }

        private NumberPrinterParser numberPrinterParser() {
            if (numberPrinterParser == null) numberPrinterParser = new NumberPrinterParser(field, 1, 19, SignStyle.NORMAL);
            return numberPrinterParser;
        }

        @Override
        public String toString() {
            if (textStyle == TextStyle.FULL) return "Text(" + field + ")";
            return "Text(" + field + "," + textStyle + ")";
        }
    }

    static final class InstantPrinterParser implements DateTimePrinterParser {
        private static final long SECONDS_PER_10000_YEARS = 146097L * 25L * 86400L;
        private static final long SECONDS_0000_TO_1970 = ((146097L * 5L) - (30L * 365L + 7L)) * 86400L;
        private final int fractionalDigits;

        InstantPrinterParser(int fractionalDigits) {
            this.fractionalDigits = fractionalDigits;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            Long inSecs = context.getValue(ChronoField.INSTANT_SECONDS);
            Long inNanos = null;
            if (context.getTemporal().isSupported(ChronoField.NANO_OF_SECOND))
                inNanos = context.getTemporal().getLong(ChronoField.NANO_OF_SECOND);
            if (inSecs == null) return false;
            long inSec = inSecs;
            int inNano = ChronoField.NANO_OF_SECOND.checkValidIntValue(inNanos != null ? inNanos : 0);
            if (inSec >= -SECONDS_0000_TO_1970) {
                long zeroSecs = inSec - SECONDS_PER_10000_YEARS + SECONDS_0000_TO_1970;
                long hi = Math.floorDiv(zeroSecs, SECONDS_PER_10000_YEARS) + 1;
                long lo = Math.floorMod(zeroSecs, SECONDS_PER_10000_YEARS);
                LocalDateTime ldt = LocalDateTime.ofEpochSecond(lo - SECONDS_0000_TO_1970, 0, ZoneOffset.UTC);
                if (hi > 0) buf.append('+').append(hi);
                buf.append(ldt);
                if (ldt.getSecond() == 0) buf.append(":00");
            } else {
                long zeroSecs = inSec + SECONDS_0000_TO_1970;
                long hi = zeroSecs / SECONDS_PER_10000_YEARS;
                long lo = zeroSecs % SECONDS_PER_10000_YEARS;
                LocalDateTime ldt = LocalDateTime.ofEpochSecond(lo - SECONDS_0000_TO_1970, 0, ZoneOffset.UTC);
                int pos = buf.length();
                buf.append(ldt);
                if (ldt.getSecond() == 0) buf.append(":00");
                if (hi < 0) {
                    if (ldt.getYear() == -10_000) {
                        buf.replace(pos, pos + 2, Long.toString(hi - 1));
                    } else if (lo == 0) {
                        buf.insert(pos, hi);
                    } else {
                        buf.insert(pos + 1, Math.abs(hi));
                    }
                }
            }
            if ((fractionalDigits < 0 && inNano > 0) || fractionalDigits > 0) {
                buf.append('.');
                int div = 100_000_000;
                for (int i = 0; ((fractionalDigits == -1 && inNano > 0) || (fractionalDigits == -2 && (inNano > 0 || (i % 3) != 0))
                    || i < fractionalDigits); i++) {
                    int digit = inNano / div;
                    buf.append((char) (digit + '0'));
                    inNano = inNano - (digit * div);
                    div = div / 10;
                }
            }
            buf.append('Z');
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            int minDigits = fractionalDigits < 0 ? 0 : fractionalDigits;
            int maxDigits = fractionalDigits < 0 ? 9 : fractionalDigits;
            CompositePrinterParser parser = new DateTimeFormatterBuilder()
                .append(DateTimeFormatter.ISO_LOCAL_DATE).appendLiteral('T')
                .appendValue(ChronoField.HOUR_OF_DAY, 2).appendLiteral(':')
                .appendValue(ChronoField.MINUTE_OF_HOUR, 2).appendLiteral(':')
                .appendValue(ChronoField.SECOND_OF_MINUTE, 2)
                .appendFraction(ChronoField.NANO_OF_SECOND, minDigits, maxDigits, true)
                .appendOffsetId()
                .toFormatter().toPrinterParser(false);
            DateTimeParseContext newContext = context.copy();
            int pos = parser.parse(newContext, text, position);
            if (pos < 0) return pos;
            long yearParsed = newContext.getParsed(ChronoField.YEAR);
            int month = newContext.getParsed(ChronoField.MONTH_OF_YEAR).intValue();
            int day = newContext.getParsed(ChronoField.DAY_OF_MONTH).intValue();
            int hour = newContext.getParsed(ChronoField.HOUR_OF_DAY).intValue();
            int min = newContext.getParsed(ChronoField.MINUTE_OF_HOUR).intValue();
            Long secVal = newContext.getParsed(ChronoField.SECOND_OF_MINUTE);
            Long nanoVal = newContext.getParsed(ChronoField.NANO_OF_SECOND);
            int sec = secVal != null ? secVal.intValue() : 0;
            int nano = nanoVal != null ? nanoVal.intValue() : 0;
            int offset = newContext.getParsed(ChronoField.OFFSET_SECONDS).intValue();
            int days = 0;
            if (hour == 24 && min == 0 && sec == 0 && nano == 0) {
                hour = 0;
                days = 1;
            } else if (hour == 23 && min == 59 && sec == 60) {
                context.setParsedLeapSecond();
                sec = 59;
            }
            int year = (int) yearParsed % 10_000;
            long instantSecs;
            try {
                LocalDateTime ldt = LocalDateTime.of(year, month, day, hour, min, sec, 0).plusDays(days);
                instantSecs = ldt.toEpochSecond(ZoneOffset.ofTotalSeconds(offset));
                instantSecs += Math.multiplyExact(yearParsed / 10_000L, SECONDS_PER_10000_YEARS);
            } catch (RuntimeException ex) {
                return ~position;
            }
            int successPos = pos;
            successPos = context.setParsedField(ChronoField.INSTANT_SECONDS, instantSecs, position, successPos);
            return context.setParsedField(ChronoField.NANO_OF_SECOND, nano, position, successPos);
        }

        @Override
        public String toString() {
            return "Instant()";
        }
    }

    static final class OffsetIdPrinterParser implements DateTimePrinterParser {
        static final String[] PATTERNS = {
            "+HH", "+HHmm", "+HH:mm", "+HHMM", "+HH:MM", "+HHMMss", "+HH:MM:ss", "+HHMMSS", "+HH:MM:SS", "+HHmmss", "+HH:mm:ss",
            "+H", "+Hmm", "+H:mm", "+HMM", "+H:MM", "+HMMss", "+H:MM:ss", "+HMMSS", "+H:MM:SS", "+Hmmss", "+H:mm:ss",
        };
        static final OffsetIdPrinterParser INSTANCE_ID_Z = new OffsetIdPrinterParser("+HH:MM:ss", "Z");
        static final OffsetIdPrinterParser INSTANCE_ID_ZERO = new OffsetIdPrinterParser("+HH:MM:ss", "0");

        private final String noOffsetText;
        private final int type;
        private final int style;

        OffsetIdPrinterParser(String pattern, String noOffsetText) {
            Objects.requireNonNull(pattern, "pattern");
            Objects.requireNonNull(noOffsetText, "noOffsetText");
            this.type = checkPattern(pattern);
            this.style = type % 11;
            this.noOffsetText = noOffsetText;
        }

        private int checkPattern(String pattern) {
            for (int i = 0; i < PATTERNS.length; i++) {
                if (PATTERNS[i].equals(pattern)) return i;
            }
            throw new IllegalArgumentException("Invalid zone offset pattern: " + pattern);
        }

        private boolean isPaddedHour() {
            return type < 11;
        }

        private boolean isColon() {
            return style > 0 && (style % 2) == 0;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            Long offsetSecs = context.getValue(ChronoField.OFFSET_SECONDS);
            if (offsetSecs == null) return false;
            int totalSecs = Math.toIntExact(offsetSecs);
            if (totalSecs == 0) {
                buf.append(noOffsetText);
            } else {
                int absHours = Math.abs((totalSecs / 3600) % 100);
                int absMinutes = Math.abs((totalSecs / 60) % 60);
                int absSeconds = Math.abs(totalSecs % 60);
                int bufPos = buf.length();
                int output = absHours;
                buf.append(totalSecs < 0 ? "-" : "+");
                if (isPaddedHour() || absHours >= 10) {
                    formatZeroPad(false, absHours, buf);
                } else {
                    buf.append((char) (absHours + '0'));
                }
                if ((style >= 3 && style <= 8) || (style >= 9 && absSeconds > 0) || (style >= 1 && absMinutes > 0)) {
                    formatZeroPad(isColon(), absMinutes, buf);
                    output += absMinutes;
                    if (style == 7 || style == 8 || (style >= 5 && absSeconds > 0)) {
                        formatZeroPad(isColon(), absSeconds, buf);
                        output += absSeconds;
                    }
                }
                if (output == 0) {
                    buf.setLength(bufPos);
                    buf.append(noOffsetText);
                }
            }
            return true;
        }

        private void formatZeroPad(boolean colon, int value, StringBuilder buf) {
            buf.append(colon ? ":" : "").append((char) (value / 10 + '0')).append((char) (value % 10 + '0'));
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            int length = text.length();
            int noOffsetLen = noOffsetText.length();
            if (noOffsetLen == 0) {
                if (position == length) return context.setParsedField(ChronoField.OFFSET_SECONDS, 0, position, position);
            } else {
                if (position == length) return ~position;
                if (context.subSequenceEquals(text, position, noOffsetText, 0, noOffsetLen))
                    return context.setParsedField(ChronoField.OFFSET_SECONDS, 0, position, position + noOffsetLen);
            }
            char sign = text.charAt(position);
            if (sign == '+' || sign == '-') {
                int negative = sign == '-' ? -1 : 1;
                boolean isColon = isColon();
                boolean paddedHour = isPaddedHour();
                int[] array = new int[4];
                array[0] = position + 1;
                int parseType = type;
                if (!context.isStrict()) {
                    if (paddedHour) {
                        if (isColon || (parseType == 0 && length > position + 3 && text.charAt(position + 3) == ':')) {
                            isColon = true;
                            parseType = 10;
                        } else {
                            parseType = 9;
                        }
                    } else {
                        if (isColon || (parseType == 11 && length > position + 3
                            && (text.charAt(position + 2) == ':' || text.charAt(position + 3) == ':'))) {
                            isColon = true;
                            parseType = 21;
                        } else {
                            parseType = 20;
                        }
                    }
                }
                switch (parseType) {
                    case 0:
                    case 11:
                        parseHour(text, paddedHour, array);
                        break;
                    case 1:
                    case 2:
                    case 13:
                        parseHour(text, paddedHour, array);
                        parseMinute(text, isColon, false, array);
                        break;
                    case 3:
                    case 4:
                    case 15:
                        parseHour(text, paddedHour, array);
                        parseMinute(text, isColon, true, array);
                        break;
                    case 5:
                    case 6:
                    case 17:
                        parseHour(text, paddedHour, array);
                        parseMinute(text, isColon, true, array);
                        parseSecond(text, isColon, false, array);
                        break;
                    case 7:
                    case 8:
                    case 19:
                        parseHour(text, paddedHour, array);
                        parseMinute(text, isColon, true, array);
                        parseSecond(text, isColon, true, array);
                        break;
                    case 9:
                    case 10:
                    case 21:
                        parseHour(text, paddedHour, array);
                        parseOptionalMinuteSecond(text, isColon, array);
                        break;
                    case 12:
                        parseVariableWidthDigits(text, 1, 4, array);
                        break;
                    case 14:
                        parseVariableWidthDigits(text, 3, 4, array);
                        break;
                    case 16:
                        parseVariableWidthDigits(text, 3, 6, array);
                        break;
                    case 18:
                        parseVariableWidthDigits(text, 5, 6, array);
                        break;
                    case 20:
                        parseVariableWidthDigits(text, 1, 6, array);
                        break;
                    default:
                        break;
                }
                if (array[0] > 0) {
                    if (array[1] > 23 || array[2] > 59 || array[3] > 59)
                        throw new DateTimeException("Value out of range: Hour[0-23], Minute[0-59], Second[0-59]");
                    long offsetSecs = negative * (array[1] * 3600L + array[2] * 60L + array[3]);
                    return context.setParsedField(ChronoField.OFFSET_SECONDS, offsetSecs, position, array[0]);
                }
            }
            if (noOffsetLen == 0) return context.setParsedField(ChronoField.OFFSET_SECONDS, 0, position, position);
            return ~position;
        }

        private void parseHour(CharSequence parseText, boolean paddedHour, int[] array) {
            if (paddedHour) {
                if (!parseDigits(parseText, false, 1, array)) array[0] = ~array[0];
            } else {
                parseVariableWidthDigits(parseText, 1, 2, array);
            }
        }

        private void parseMinute(CharSequence parseText, boolean isColon, boolean mandatory, int[] array) {
            if (!parseDigits(parseText, isColon, 2, array)) {
                if (mandatory) array[0] = ~array[0];
            }
        }

        private void parseSecond(CharSequence parseText, boolean isColon, boolean mandatory, int[] array) {
            if (!parseDigits(parseText, isColon, 3, array)) {
                if (mandatory) array[0] = ~array[0];
            }
        }

        private void parseOptionalMinuteSecond(CharSequence parseText, boolean isColon, int[] array) {
            if (parseDigits(parseText, isColon, 2, array)) parseDigits(parseText, isColon, 3, array);
        }

        private boolean parseDigits(CharSequence parseText, boolean isColon, int arrayIndex, int[] array) {
            int pos = array[0];
            if (pos < 0) return true;
            if (isColon && arrayIndex != 1) {
                if (pos + 1 > parseText.length() || parseText.charAt(pos) != ':') return false;
                pos++;
            }
            if (pos + 2 > parseText.length()) return false;
            char ch1 = parseText.charAt(pos++);
            char ch2 = parseText.charAt(pos++);
            if (ch1 < '0' || ch1 > '9' || ch2 < '0' || ch2 > '9') return false;
            int value = (ch1 - 48) * 10 + (ch2 - 48);
            if (value < 0 || value > 59) return false;
            array[arrayIndex] = value;
            array[0] = pos;
            return true;
        }

        private void parseVariableWidthDigits(CharSequence parseText, int minDigits, int maxDigits, int[] array) {
            int pos = array[0];
            int available = 0;
            char[] chars = new char[maxDigits];
            for (int i = 0; i < maxDigits; i++) {
                if (pos + 1 > parseText.length()) break;
                char ch = parseText.charAt(pos++);
                if (ch < '0' || ch > '9') {
                    pos--;
                    break;
                }
                chars[i] = ch;
                available++;
            }
            if (available < minDigits) {
                array[0] = ~array[0];
                return;
            }
            switch (available) {
                case 1:
                    array[1] = chars[0] - 48;
                    break;
                case 2:
                    array[1] = (chars[0] - 48) * 10 + (chars[1] - 48);
                    break;
                case 3:
                    array[1] = chars[0] - 48;
                    array[2] = (chars[1] - 48) * 10 + (chars[2] - 48);
                    break;
                case 4:
                    array[1] = (chars[0] - 48) * 10 + (chars[1] - 48);
                    array[2] = (chars[2] - 48) * 10 + (chars[3] - 48);
                    break;
                case 5:
                    array[1] = chars[0] - 48;
                    array[2] = (chars[1] - 48) * 10 + (chars[2] - 48);
                    array[3] = (chars[3] - 48) * 10 + (chars[4] - 48);
                    break;
                case 6:
                    array[1] = (chars[0] - 48) * 10 + (chars[1] - 48);
                    array[2] = (chars[2] - 48) * 10 + (chars[3] - 48);
                    array[3] = (chars[4] - 48) * 10 + (chars[5] - 48);
                    break;
                default:
                    break;
            }
            array[0] = pos;
        }

        @Override
        public String toString() {
            return "Offset(" + PATTERNS[type] + ",'" + noOffsetText.replace("'", "''") + "')";
        }
    }

    static class ZoneIdPrinterParser implements DateTimePrinterParser {
        private final TemporalQuery<ZoneId> query;
        private final String description;

        ZoneIdPrinterParser(TemporalQuery<ZoneId> query, String description) {
            this.query = query;
            this.description = description;
        }

        @Override
        public boolean format(DateTimePrintContext context, StringBuilder buf) {
            ZoneId zone = context.getValue(query);
            if (zone == null) return false;
            buf.append(zone.getId());
            return true;
        }

        @Override
        public int parse(DateTimeParseContext context, CharSequence text, int position) {
            int length = text.length();
            if (position > length) throw new IndexOutOfBoundsException();
            if (position == length) return ~position;
            char nextChar = text.charAt(position);
            if (nextChar == '+' || nextChar == '-') {
                return parseOffsetBased(context, text, position, position, OffsetIdPrinterParser.INSTANCE_ID_Z);
            } else if (length >= position + 2) {
                char nextNextChar = text.charAt(position + 1);
                if (context.charEquals(nextChar, 'U') && context.charEquals(nextNextChar, 'T')) {
                    if (length >= position + 3 && context.charEquals(text.charAt(position + 2), 'C')) {
                        if (length == position + 3 || context.charEquals(text.charAt(position + 3), '+')
                            || context.charEquals(text.charAt(position + 3), '-'))
                            return parseOffsetBased(context, text, position, position + 3, OffsetIdPrinterParser.INSTANCE_ID_ZERO);
                    } else {
                        return parseOffsetBased(context, text, position, position + 2, OffsetIdPrinterParser.INSTANCE_ID_ZERO);
                    }
                } else if (context.charEquals(nextChar, 'G') && length >= position + 3
                    && context.charEquals(nextNextChar, 'M') && context.charEquals(text.charAt(position + 2), 'T')) {
                    if (length >= position + 4 && context.charEquals(text.charAt(position + 3), '0'))
                        throw ModelStuckFormat.unsupported("zone id GMT0: tz database");
                    return parseOffsetBased(context, text, position, position + 3, OffsetIdPrinterParser.INSTANCE_ID_ZERO);
                }
            }
            // The JDK matches the longest available region id (ZoneRulesProvider) here. Every JDK 21 tzdb id starts
            // with an upper-case ASCII letter; only "UTC" starts with "UTC" and only "Zulu" with 'Z'. So these
            // cases are decided without the id list: no id can start with a character that is not an ASCII letter
            // (an upper-case one when case-sensitive; non-ASCII letters may match ignoring case: STUCK).
            boolean noRegion = context.isCaseSensitive() ? (nextChar < 'A' || nextChar > 'Z')
                : (nextChar < 128 && !((nextChar >= 'A' && nextChar <= 'Z') || (nextChar >= 'a' && nextChar <= 'z')));
            if (noRegion) return ~position;
            if (length >= position + 3 && context.charEquals(nextChar, 'U') && context.charEquals(text.charAt(position + 1), 'T')
                && context.charEquals(text.charAt(position + 2), 'C')) {
                context.setParsed(ZoneId.of("UTC"));
                return position + 3;
            }
            if (context.charEquals(nextChar, 'Z')) {
                if (!context.subSequenceEquals(text, position, "Zulu", 0, 4)) {
                    context.setParsed(ZoneOffset.UTC);
                    return position + 1;
                }
            }
            throw ModelStuckFormat.unsupported("parsing a region zone id: tz database");
        }

        private int parseOffsetBased(DateTimeParseContext context, CharSequence text, int prefixPos, int position,
                                     OffsetIdPrinterParser parser) {
            String prefix = text.subSequence(prefixPos, position).toString().toUpperCase();
            if (position >= text.length()) {
                context.setParsed(ZoneId.of(prefix));
                return position;
            }
            if (text.charAt(position) == '0' || context.charEquals(text.charAt(position), 'Z')) {
                context.setParsed(ZoneId.of(prefix));
                return position;
            }
            DateTimeParseContext newContext = context.copy();
            int endPos = parser.parse(newContext, text, position);
            try {
                if (endPos < 0) {
                    if (parser == OffsetIdPrinterParser.INSTANCE_ID_Z) return ~prefixPos;
                    context.setParsed(ZoneId.of(prefix));
                    return position;
                }
                int offset = (int) newContext.getParsed(ChronoField.OFFSET_SECONDS).longValue();
                ZoneOffset zoneOffset = ZoneOffset.ofTotalSeconds(offset);
                context.setParsed(ZoneId.ofOffset(prefix, zoneOffset));
                return endPos;
            } catch (DateTimeException dte) {
                return ~prefixPos;
            }
        }

        @Override
        public String toString() {
            return description;
        }
    }
}

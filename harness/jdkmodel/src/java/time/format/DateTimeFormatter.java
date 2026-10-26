/*
 * rocq-jvm model of java.time.format.DateTimeFormatter (clean-room, Apache-2.0): JDK 21's formatter
 * over the model printer-parsers: the predefined ISO formatters (ISO_LOCAL_DATE, ISO_OFFSET_DATE,
 * ISO_DATE, ISO_LOCAL_TIME, ISO_OFFSET_TIME, ISO_TIME, ISO_LOCAL_DATE_TIME, ISO_OFFSET_DATE_TIME,
 * ISO_ZONED_DATE_TIME, ISO_DATE_TIME, ISO_ORDINAL_DATE, ISO_INSTANT, BASIC_ISO_DATE,
 * RFC_1123_DATE_TIME) built as in the JDK, ofPattern, format/formatTo, parse (with the JDK's
 * DateTimeParseException texts: "could not be parsed at index", "unparsed text found at index", the
 * resolver's message, the 64-character abbreviation), parseBest, the with* copies and toString.
 * The predefined formatters and ofPattern(String) use the host's default locale in the JDK; the
 * model records it as unknown, so getLocale/withLocale of such a formatter, and texts that need it,
 * are STUCK (numbers and ISO texts never need it). STUCK: ISO_WEEK_DATE (IsoFields), localized
 * formatters (ofLocalized*), localizedBy, parse with a ParsePosition, parseUnresolved, toFormat.
 */
package java.time.format;

import java.io.IOException;
import java.time.DateTimeException;
import java.time.Period;
import java.time.ZoneId;
import java.time.chrono.Chronology;
import java.time.chrono.IsoChronology;
import java.time.format.DateTimeFormatterBuilder.CompositePrinterParser;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalField;
import java.time.temporal.TemporalQuery;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public final class DateTimeFormatter {
    private final CompositePrinterParser printerParser;
    private final Locale locale;
    private final boolean hostLocale;
    private final DecimalStyle decimalStyle;
    private final ResolverStyle resolverStyle;
    private final Set<TemporalField> resolverFields;
    private final Chronology chrono;
    private final ZoneId zone;

    public static DateTimeFormatter ofPattern(String pattern) {
        return new DateTimeFormatterBuilder().appendPattern(pattern).toFormatter();
    }

    public static DateTimeFormatter ofPattern(String pattern, Locale locale) {
        return new DateTimeFormatterBuilder().appendPattern(pattern).toFormatter(locale);
    }

    public static final DateTimeFormatter ISO_LOCAL_DATE;
    static {
        ISO_LOCAL_DATE = new DateTimeFormatterBuilder()
            .appendValue(ChronoField.YEAR, 4, 10, SignStyle.EXCEEDS_PAD)
            .appendLiteral('-')
            .appendValue(ChronoField.MONTH_OF_YEAR, 2)
            .appendLiteral('-')
            .appendValue(ChronoField.DAY_OF_MONTH, 2)
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_OFFSET_DATE;
    static {
        ISO_OFFSET_DATE = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .append(ISO_LOCAL_DATE)
            .appendOffsetId()
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_DATE;
    static {
        ISO_DATE = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .append(ISO_LOCAL_DATE)
            .optionalStart()
            .appendOffsetId()
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_LOCAL_TIME;
    static {
        ISO_LOCAL_TIME = new DateTimeFormatterBuilder()
            .appendValue(ChronoField.HOUR_OF_DAY, 2)
            .appendLiteral(':')
            .appendValue(ChronoField.MINUTE_OF_HOUR, 2)
            .optionalStart()
            .appendLiteral(':')
            .appendValue(ChronoField.SECOND_OF_MINUTE, 2)
            .optionalStart()
            .appendFraction(ChronoField.NANO_OF_SECOND, 0, 9, true)
            .toFormatter(ResolverStyle.STRICT, null);
    }

    public static final DateTimeFormatter ISO_OFFSET_TIME;
    static {
        ISO_OFFSET_TIME = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .append(ISO_LOCAL_TIME)
            .appendOffsetId()
            .toFormatter(ResolverStyle.STRICT, null);
    }

    public static final DateTimeFormatter ISO_TIME;
    static {
        ISO_TIME = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .append(ISO_LOCAL_TIME)
            .optionalStart()
            .appendOffsetId()
            .toFormatter(ResolverStyle.STRICT, null);
    }

    public static final DateTimeFormatter ISO_LOCAL_DATE_TIME;
    static {
        ISO_LOCAL_DATE_TIME = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .append(ISO_LOCAL_DATE)
            .appendLiteral('T')
            .append(ISO_LOCAL_TIME)
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_OFFSET_DATE_TIME;
    static {
        ISO_OFFSET_DATE_TIME = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .append(ISO_LOCAL_DATE_TIME)
            .parseLenient()
            .appendOffsetId()
            .parseStrict()
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_ZONED_DATE_TIME;
    static {
        ISO_ZONED_DATE_TIME = new DateTimeFormatterBuilder()
            .append(ISO_OFFSET_DATE_TIME)
            .optionalStart()
            .appendLiteral('[')
            .parseCaseSensitive()
            .appendZoneRegionId()
            .appendLiteral(']')
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_DATE_TIME;
    static {
        ISO_DATE_TIME = new DateTimeFormatterBuilder()
            .append(ISO_LOCAL_DATE_TIME)
            .optionalStart()
            .appendOffsetId()
            .optionalStart()
            .appendLiteral('[')
            .parseCaseSensitive()
            .appendZoneRegionId()
            .appendLiteral(']')
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_ORDINAL_DATE;
    static {
        ISO_ORDINAL_DATE = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .appendValue(ChronoField.YEAR, 4, 10, SignStyle.EXCEEDS_PAD)
            .appendLiteral('-')
            .appendValue(ChronoField.DAY_OF_YEAR, 3)
            .optionalStart()
            .appendOffsetId()
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_WEEK_DATE;
    static {
        ISO_WEEK_DATE = new DateTimeFormatterBuilder()
            .appendStuck("ISO_WEEK_DATE: IsoFields are not modelled")
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter ISO_INSTANT;
    static {
        ISO_INSTANT = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .appendInstant()
            .toFormatter(ResolverStyle.STRICT, null);
    }

    public static final DateTimeFormatter BASIC_ISO_DATE;
    static {
        BASIC_ISO_DATE = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .appendValue(ChronoField.YEAR, 4)
            .appendValue(ChronoField.MONTH_OF_YEAR, 2)
            .appendValue(ChronoField.DAY_OF_MONTH, 2)
            .optionalStart()
            .parseLenient()
            .appendOffset("+HHMMss", "Z")
            .parseStrict()
            .toFormatter(ResolverStyle.STRICT, IsoChronology.INSTANCE);
    }

    public static final DateTimeFormatter RFC_1123_DATE_TIME;
    static {
        Map<Long, String> dow = new HashMap<>();
        dow.put(1L, "Mon");
        dow.put(2L, "Tue");
        dow.put(3L, "Wed");
        dow.put(4L, "Thu");
        dow.put(5L, "Fri");
        dow.put(6L, "Sat");
        dow.put(7L, "Sun");
        Map<Long, String> moy = new HashMap<>();
        moy.put(1L, "Jan");
        moy.put(2L, "Feb");
        moy.put(3L, "Mar");
        moy.put(4L, "Apr");
        moy.put(5L, "May");
        moy.put(6L, "Jun");
        moy.put(7L, "Jul");
        moy.put(8L, "Aug");
        moy.put(9L, "Sep");
        moy.put(10L, "Oct");
        moy.put(11L, "Nov");
        moy.put(12L, "Dec");
        RFC_1123_DATE_TIME = new DateTimeFormatterBuilder()
            .parseCaseInsensitive()
            .parseLenient()
            .optionalStart()
            .appendText(ChronoField.DAY_OF_WEEK, dow)
            .appendLiteral(", ")
            .optionalEnd()
            .appendValue(ChronoField.DAY_OF_MONTH, 1, 2, SignStyle.NOT_NEGATIVE)
            .appendLiteral(' ')
            .appendText(ChronoField.MONTH_OF_YEAR, moy)
            .appendLiteral(' ')
            .appendValue(ChronoField.YEAR, 4)
            .appendLiteral(' ')
            .appendValue(ChronoField.HOUR_OF_DAY, 2)
            .appendLiteral(':')
            .appendValue(ChronoField.MINUTE_OF_HOUR, 2)
            .optionalStart()
            .appendLiteral(':')
            .appendValue(ChronoField.SECOND_OF_MINUTE, 2)
            .optionalEnd()
            .appendLiteral(' ')
            .appendOffset("+HHMM", "GMT")
            .toFormatter(ResolverStyle.SMART, IsoChronology.INSTANCE);
    }

    public static final TemporalQuery<Period> parsedExcessDays() {
        return PARSED_EXCESS_DAYS;
    }

    private static final TemporalQuery<Period> PARSED_EXCESS_DAYS = t -> {
        if (t instanceof Parsed) return ((Parsed) t).excessDays;
        return Period.ZERO;
    };

    public static final TemporalQuery<Boolean> parsedLeapSecond() {
        return PARSED_LEAP_SECOND;
    }

    private static final TemporalQuery<Boolean> PARSED_LEAP_SECOND = t -> {
        if (t instanceof Parsed) return ((Parsed) t).leapSecond;
        return Boolean.FALSE;
    };

    DateTimeFormatter(CompositePrinterParser printerParser, Locale locale, DecimalStyle decimalStyle,
                      ResolverStyle resolverStyle, Set<TemporalField> resolverFields, Chronology chrono, ZoneId zone) {
        this(printerParser, locale, locale == null, decimalStyle, resolverStyle, resolverFields, chrono, zone);
    }

    private DateTimeFormatter(CompositePrinterParser printerParser, Locale locale, boolean hostLocale,
                              DecimalStyle decimalStyle, ResolverStyle resolverStyle, Set<TemporalField> resolverFields,
                              Chronology chrono, ZoneId zone) {
        this.printerParser = Objects.requireNonNull(printerParser, "printerParser");
        this.resolverFields = resolverFields;
        if (!hostLocale) Objects.requireNonNull(locale, "locale");
        this.locale = locale;
        this.hostLocale = hostLocale;
        this.decimalStyle = Objects.requireNonNull(decimalStyle, "decimalStyle");
        this.resolverStyle = Objects.requireNonNull(resolverStyle, "resolverStyle");
        this.chrono = chrono;
        this.zone = zone;
    }

    private DateTimeFormatter copy(DecimalStyle ds, ResolverStyle rs, Set<TemporalField> rf, Chronology c, ZoneId z) {
        return new DateTimeFormatter(printerParser, locale, hostLocale, ds, rs, rf, c, z);
    }

    public Locale getLocale() {
        if (hostLocale) throw ModelStuckFormat.unsupported("DateTimeFormatter: the host's default locale");
        return locale;
    }

    /** The locale for the printer-parsers: null for the host's default locale, which only the locale-based
     *  text provider consults (and is STUCK on). */
    Locale locale0() {
        return locale;
    }

    public DateTimeFormatter withLocale(Locale locale) {
        if (getLocale().equals(locale)) return this;
        return new DateTimeFormatter(printerParser, locale, false, decimalStyle, resolverStyle, resolverFields, chrono, zone);
    }

    public DateTimeFormatter localizedBy(Locale locale) {
        throw ModelStuckFormat.unsupported("DateTimeFormatter.localizedBy: locale data");
    }

    public DecimalStyle getDecimalStyle() {
        return decimalStyle;
    }

    public DateTimeFormatter withDecimalStyle(DecimalStyle decimalStyle) {
        if (this.decimalStyle.equals(decimalStyle)) return this;
        return copy(decimalStyle, resolverStyle, resolverFields, chrono, zone);
    }

    public Chronology getChronology() {
        return chrono;
    }

    public DateTimeFormatter withChronology(Chronology chrono) {
        if (Objects.equals(this.chrono, chrono)) return this;
        return copy(decimalStyle, resolverStyle, resolverFields, chrono, zone);
    }

    public ZoneId getZone() {
        return zone;
    }

    public DateTimeFormatter withZone(ZoneId zone) {
        if (Objects.equals(this.zone, zone)) return this;
        return copy(decimalStyle, resolverStyle, resolverFields, chrono, zone);
    }

    public ResolverStyle getResolverStyle() {
        return resolverStyle;
    }

    public DateTimeFormatter withResolverStyle(ResolverStyle resolverStyle) {
        Objects.requireNonNull(resolverStyle, "resolverStyle");
        if (Objects.equals(this.resolverStyle, resolverStyle)) return this;
        return copy(decimalStyle, resolverStyle, resolverFields, chrono, zone);
    }

    public Set<TemporalField> getResolverFields() {
        return resolverFields;
    }

    public DateTimeFormatter withResolverFields(TemporalField... resolverFields) {
        Set<TemporalField> fields = null;
        if (resolverFields != null) fields = Collections.unmodifiableSet(new HashSet<>(Arrays.asList(resolverFields)));
        if (Objects.equals(this.resolverFields, fields)) return this;
        return copy(decimalStyle, resolverStyle, fields, chrono, zone);
    }

    public DateTimeFormatter withResolverFields(Set<TemporalField> resolverFields) {
        if (Objects.equals(this.resolverFields, resolverFields)) return this;
        if (resolverFields != null) resolverFields = Collections.unmodifiableSet(new HashSet<>(resolverFields));
        return copy(decimalStyle, resolverStyle, resolverFields, chrono, zone);
    }

    public String format(TemporalAccessor temporal) {
        StringBuilder buf = new StringBuilder(32);
        formatTo(temporal, buf);
        return buf.toString();
    }

    public void formatTo(TemporalAccessor temporal, Appendable appendable) {
        Objects.requireNonNull(temporal, "temporal");
        Objects.requireNonNull(appendable, "appendable");
        try {
            DateTimePrintContext context = new DateTimePrintContext(temporal, this);
            if (appendable instanceof StringBuilder) {
                printerParser.format(context, (StringBuilder) appendable);
            } else {
                StringBuilder buf = new StringBuilder(32);
                printerParser.format(context, buf);
                appendable.append(buf);
            }
        } catch (IOException ex) {
            throw new DateTimeException(ex.getMessage(), ex);
        }
    }

    public TemporalAccessor parse(CharSequence text) {
        Objects.requireNonNull(text, "text");
        try {
            return parseResolved0(text);
        } catch (DateTimeParseException ex) {
            throw ex;
        } catch (RuntimeException ex) {
            throw createError(text, ex);
        }
    }

    public <T> T parse(CharSequence text, TemporalQuery<T> query) {
        Objects.requireNonNull(text, "text");
        Objects.requireNonNull(query, "query");
        try {
            return parseResolved0(text).query(query);
        } catch (DateTimeParseException ex) {
            throw ex;
        } catch (RuntimeException ex) {
            throw createError(text, ex);
        }
    }

    public TemporalAccessor parseBest(CharSequence text, TemporalQuery<?>... queries) {
        Objects.requireNonNull(text, "text");
        Objects.requireNonNull(queries, "queries");
        if (queries.length < 2) throw new IllegalArgumentException("At least two queries must be specified");
        try {
            TemporalAccessor resolved = parseResolved0(text);
            for (TemporalQuery<?> query : queries) {
                try {
                    return (TemporalAccessor) resolved.query(query);
                } catch (RuntimeException ex) {
                    // continue
                }
            }
            throw new DateTimeException("Unable to convert parsed text using any of the specified queries");
        } catch (DateTimeParseException ex) {
            throw ex;
        } catch (RuntimeException ex) {
            throw createError(text, ex);
        }
    }

    private static String abbreviate(CharSequence text) {
        if (text.length() > 64) return text.subSequence(0, 64).toString() + "...";
        return text.toString();
    }

    private DateTimeParseException createError(CharSequence text, RuntimeException ex) {
        return new DateTimeParseException("Text '" + abbreviate(text) + "' could not be parsed: " + ex.getMessage(), text, 0, ex);
    }

    private TemporalAccessor parseResolved0(final CharSequence text) {
        Objects.requireNonNull(text, "text");
        DateTimeParseContext context = new DateTimeParseContext(this);
        int pos = printerParser.parse(context, text, 0);
        if (pos < 0) {
            int errorIndex = ~pos;
            throw new DateTimeParseException("Text '" + abbreviate(text) + "' could not be parsed at index " + errorIndex,
                text, errorIndex);
        }
        if (pos < text.length())
            throw new DateTimeParseException("Text '" + abbreviate(text) + "' could not be parsed, unparsed text found at index "
                + pos, text, pos);
        return context.toResolved(resolverStyle, resolverFields);
    }

    CompositePrinterParser toPrinterParser(boolean optional) {
        return printerParser.withOptional(optional);
    }

    @Override
    public String toString() {
        String pattern = printerParser.toString();
        return pattern.startsWith("[") ? pattern : pattern.substring(1, pattern.length() - 1);
    }
}

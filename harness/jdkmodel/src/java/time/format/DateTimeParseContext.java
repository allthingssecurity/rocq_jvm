/* rocq-jvm model of java.time.format.DateTimeParseContext (clean-room, Apache-2.0): JDK 21's parse
 * state (case sensitivity, strictness, the stack of Parsed for optional sections, effective
 * chronology). Chronology listeners (ReducedPrinterParser with a base date) are not modelled. */
package java.time.format;

import java.time.ZoneId;
import java.time.chrono.Chronology;
import java.time.chrono.IsoChronology;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalField;
import java.util.ArrayList;
import java.util.Locale;
import java.util.Objects;
import java.util.Set;

final class DateTimeParseContext {
    private DateTimeFormatter formatter;
    private boolean caseSensitive = true;
    private boolean strict = true;
    private final ArrayList<Parsed> parsed = new ArrayList<>();

    DateTimeParseContext(DateTimeFormatter formatter) {
        this.formatter = formatter;
        parsed.add(new Parsed());
    }

    DateTimeParseContext copy() {
        DateTimeParseContext c = new DateTimeParseContext(formatter);
        c.caseSensitive = caseSensitive;
        c.strict = strict;
        return c;
    }

    Locale getLocale() {
        return formatter.locale0();
    }

    DecimalStyle getDecimalStyle() {
        return formatter.getDecimalStyle();
    }

    Chronology getEffectiveChronology() {
        Chronology chrono = currentParsed().chrono;
        if (chrono == null) {
            chrono = formatter.getChronology();
            if (chrono == null) chrono = IsoChronology.INSTANCE;
        }
        return chrono;
    }

    boolean isCaseSensitive() {
        return caseSensitive;
    }

    void setCaseSensitive(boolean caseSensitive) {
        this.caseSensitive = caseSensitive;
    }

    boolean subSequenceEquals(CharSequence cs1, int offset1, CharSequence cs2, int offset2, int length) {
        if (offset1 + length > cs1.length() || offset2 + length > cs2.length()) return false;
        if (isCaseSensitive()) {
            for (int i = 0; i < length; i++) {
                if (cs1.charAt(offset1 + i) != cs2.charAt(offset2 + i)) return false;
            }
        } else {
            for (int i = 0; i < length; i++) {
                char ch1 = cs1.charAt(offset1 + i);
                char ch2 = cs2.charAt(offset2 + i);
                if (ch1 != ch2 && Character.toUpperCase(ch1) != Character.toUpperCase(ch2)
                    && Character.toLowerCase(ch1) != Character.toLowerCase(ch2)) return false;
            }
        }
        return true;
    }

    boolean charEquals(char ch1, char ch2) {
        if (isCaseSensitive()) return ch1 == ch2;
        return charEqualsIgnoreCase(ch1, ch2);
    }

    static boolean charEqualsIgnoreCase(char c1, char c2) {
        return c1 == c2 || Character.toUpperCase(c1) == Character.toUpperCase(c2)
            || Character.toLowerCase(c1) == Character.toLowerCase(c2);
    }

    boolean isStrict() {
        return strict;
    }

    void setStrict(boolean strict) {
        this.strict = strict;
    }

    void startOptional() {
        parsed.add(currentParsed().copy());
    }

    void endOptional(boolean successful) {
        if (successful) {
            parsed.remove(parsed.size() - 2);
        } else {
            parsed.remove(parsed.size() - 1);
        }
    }

    private Parsed currentParsed() {
        return parsed.get(parsed.size() - 1);
    }

    Parsed toUnresolved() {
        return currentParsed();
    }

    TemporalAccessor toResolved(ResolverStyle resolverStyle, Set<TemporalField> resolverFields) {
        Parsed p = currentParsed();
        p.chrono = getEffectiveChronology();
        p.zone = p.zone != null ? p.zone : formatter.getZone();
        return p.resolve(resolverStyle, resolverFields);
    }

    Long getParsed(TemporalField field) {
        return currentParsed().fieldValues.get(field);
    }

    int setParsedField(TemporalField field, long value, int errorPos, int successPos) {
        Objects.requireNonNull(field, "field");
        Long old = currentParsed().fieldValues.put(field, value);
        return (old != null && old.longValue() != value) ? ~errorPos : successPos;
    }

    void setParsed(Chronology chrono) {
        Objects.requireNonNull(chrono, "chrono");
        currentParsed().chrono = chrono;
    }

    void setParsed(ZoneId zone) {
        Objects.requireNonNull(zone, "zone");
        currentParsed().zone = zone;
    }

    void setParsedLeapSecond() {
        currentParsed().leapSecond = true;
    }

    @Override
    public String toString() {
        return currentParsed().toString();
    }
}

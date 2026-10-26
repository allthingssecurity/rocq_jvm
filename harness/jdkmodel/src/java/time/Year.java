/*
 * rocq-jvm model of java.time.Year (clean-room, Apache-2.0): JDK 21's year with its leap rule, field
 * access, arithmetic, until, parse (the JDK's lenient 1-10 digit parser) and toString. STUCK: now() and now(ZoneId)
 * (host clock: absent; now(Clock) is modelled), MonthDay (not modelled: atMonthDay/isValidMonthDay absent), serialization.
 */
package java.time;

import java.time.chrono.Chronology;
import java.time.chrono.IsoChronology;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeFormatterBuilder;
import java.time.format.SignStyle;
import java.time.temporal.ChronoField;
import java.time.temporal.ChronoUnit;
import java.time.temporal.Temporal;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalAdjuster;
import java.time.temporal.TemporalAmount;
import java.time.temporal.TemporalField;
import java.time.temporal.TemporalQueries;
import java.time.temporal.TemporalQuery;
import java.time.temporal.TemporalUnit;
import java.time.temporal.UnsupportedTemporalTypeException;
import java.time.temporal.ValueRange;
import java.util.Objects;

public final class Year implements Temporal, TemporalAdjuster, Comparable<Year>, java.io.Serializable {
    private static final long serialVersionUID = -23038383694477807L;

    public static final int MIN_VALUE = -999_999_999;
    public static final int MAX_VALUE = 999_999_999;

    private static final DateTimeFormatter PARSER = new DateTimeFormatterBuilder()
        .parseLenient()
        .appendValue(ChronoField.YEAR, 1, 10, SignStyle.NORMAL)
        .toFormatter();

    private final int year;

    private Year(int year) {
        this.year = year;
    }

    public static Year now(Clock clock) {
        final LocalDate now = LocalDate.now(clock);
        return Year.of(now.getYear());
    }

    public static Year of(int isoYear) {
        ChronoField.YEAR.checkValidValue(isoYear);
        return new Year(isoYear);
    }

    public static Year from(TemporalAccessor temporal) {
        if (temporal instanceof Year) return (Year) temporal;
        Objects.requireNonNull(temporal, "temporal");
        try {
            if (!IsoChronology.INSTANCE.equals(Chronology.from(temporal))) temporal = LocalDate.from(temporal);
            return of(temporal.get(ChronoField.YEAR));
        } catch (DateTimeException ex) {
            throw new DateTimeException("Unable to obtain Year from TemporalAccessor: " + temporal + " of type "
                + temporal.getClass().getName(), ex);
        }
    }

    public static Year parse(CharSequence text) {
        return parse(text, PARSER);
    }

    public static Year parse(CharSequence text, DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.parse(text, Year::from);
    }

    public static boolean isLeap(long year) {
        return ((year & 3) == 0) && ((year % 100) != 0 || (year % 400) == 0);
    }

    public int getValue() {
        return year;
    }

    @Override
    public boolean isSupported(TemporalField field) {
        if (field instanceof ChronoField) return field == ChronoField.YEAR || field == ChronoField.YEAR_OF_ERA || field == ChronoField.ERA;
        return field != null && field.isSupportedBy(this);
    }

    @Override
    public boolean isSupported(TemporalUnit unit) {
        if (unit instanceof ChronoUnit)
            return unit == ChronoUnit.YEARS || unit == ChronoUnit.DECADES || unit == ChronoUnit.CENTURIES
                || unit == ChronoUnit.MILLENNIA || unit == ChronoUnit.ERAS;
        return unit != null && unit.isSupportedBy(this);
    }

    @Override
    public ValueRange range(TemporalField field) {
        if (field == ChronoField.YEAR_OF_ERA) return year <= 0 ? ValueRange.of(1, MAX_VALUE + 1) : ValueRange.of(1, MAX_VALUE);
        return Temporal.super.range(field);
    }

    @Override
    public int get(TemporalField field) {
        return range(field).checkValidIntValue(getLong(field), field);
    }

    @Override
    public long getLong(TemporalField field) {
        if (field instanceof ChronoField) {
            switch ((ChronoField) field) {
                case YEAR_OF_ERA: return year < 1 ? 1 - year : year;
                case YEAR: return year;
                case ERA: return year < 1 ? 0 : 1;
                default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            }
        }
        return field.getFrom(this);
    }

    public boolean isLeap() {
        return Year.isLeap(year);
    }

    public int length() {
        return isLeap() ? 366 : 365;
    }

    @Override
    public Year with(TemporalAdjuster adjuster) {
        return (Year) adjuster.adjustInto(this);
    }

    @Override
    public Year with(TemporalField field, long newValue) {
        if (field instanceof ChronoField) {
            ChronoField f = (ChronoField) field;
            f.checkValidValue(newValue);
            switch (f) {
                case YEAR_OF_ERA: return Year.of((int) (year < 1 ? 1 - newValue : newValue));
                case YEAR: return Year.of((int) newValue);
                case ERA: return getLong(ChronoField.ERA) == newValue ? this : Year.of(1 - year);
                default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            }
        }
        return field.adjustInto(this, newValue);
    }

    @Override
    public Year plus(TemporalAmount amountToAdd) {
        return (Year) amountToAdd.addTo(this);
    }

    @Override
    public Year plus(long amountToAdd, TemporalUnit unit) {
        if (unit instanceof ChronoUnit) {
            switch ((ChronoUnit) unit) {
                case YEARS: return plusYears(amountToAdd);
                case DECADES: return plusYears(Math.multiplyExact(amountToAdd, 10));
                case CENTURIES: return plusYears(Math.multiplyExact(amountToAdd, 100));
                case MILLENNIA: return plusYears(Math.multiplyExact(amountToAdd, 1000));
                case ERAS: return with(ChronoField.ERA, Math.addExact(getLong(ChronoField.ERA), amountToAdd));
                default: throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
            }
        }
        return unit.addTo(this, amountToAdd);
    }

    public Year plusYears(long yearsToAdd) {
        if (yearsToAdd == 0) return this;
        return of(ChronoField.YEAR.checkValidIntValue(year + yearsToAdd));
    }

    @Override
    public Year minus(TemporalAmount amountToSubtract) {
        return (Year) amountToSubtract.subtractFrom(this);
    }

    @Override
    public Year minus(long amountToSubtract, TemporalUnit unit) {
        return amountToSubtract == Long.MIN_VALUE ? plus(Long.MAX_VALUE, unit).plus(1, unit) : plus(-amountToSubtract, unit);
    }

    public Year minusYears(long n) {
        return n == Long.MIN_VALUE ? plusYears(Long.MAX_VALUE).plusYears(1) : plusYears(-n);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.chronology()) return (R) IsoChronology.INSTANCE;
        if (query == TemporalQueries.precision()) return (R) ChronoUnit.YEARS;
        return Temporal.super.query(query);
    }

    @Override
    public Temporal adjustInto(Temporal temporal) {
        if (!Chronology.from(temporal).equals(IsoChronology.INSTANCE))
            throw new DateTimeException("Adjustment only supported on ISO date-time");
        return temporal.with(ChronoField.YEAR, year);
    }

    @Override
    public long until(Temporal endExclusive, TemporalUnit unit) {
        Year end = Year.from(endExclusive);
        if (unit instanceof ChronoUnit) {
            long yearsUntil = ((long) end.year) - year;
            switch ((ChronoUnit) unit) {
                case YEARS: return yearsUntil;
                case DECADES: return yearsUntil / 10;
                case CENTURIES: return yearsUntil / 100;
                case MILLENNIA: return yearsUntil / 1000;
                case ERAS: return end.getLong(ChronoField.ERA) - getLong(ChronoField.ERA);
                default: throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
            }
        }
        return unit.between(this, end);
    }

    public String format(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.format(this);
    }

    public LocalDate atDay(int dayOfYear) {
        return LocalDate.ofYearDay(year, dayOfYear);
    }

    public YearMonth atMonth(Month month) {
        return YearMonth.of(year, month);
    }

    public YearMonth atMonth(int month) {
        return YearMonth.of(year, month);
    }

    @Override
    public int compareTo(Year other) {
        return year - other.year;
    }

    public boolean isAfter(Year other) {
        return year > other.year;
    }

    public boolean isBefore(Year other) {
        return year < other.year;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj instanceof Year) return year == ((Year) obj).year;
        return false;
    }

    @Override
    public int hashCode() {
        return year;
    }

    @Override
    public String toString() {
        return Integer.toString(year);
    }
}

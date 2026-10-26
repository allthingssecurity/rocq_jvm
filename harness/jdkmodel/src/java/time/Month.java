/* rocq-jvm model of java.time.Month (clean-room, Apache-2.0): JDK 21's arithmetic, lengths, field
 * access and texts; getDisplayName goes through the model formatter (English text only). */
package java.time;

import java.time.chrono.Chronology;
import java.time.chrono.IsoChronology;
import java.time.format.DateTimeFormatterBuilder;
import java.time.format.TextStyle;
import java.time.temporal.ChronoField;
import java.time.temporal.ChronoUnit;
import java.time.temporal.Temporal;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalAdjuster;
import java.time.temporal.TemporalField;
import java.time.temporal.TemporalQueries;
import java.time.temporal.TemporalQuery;
import java.time.temporal.UnsupportedTemporalTypeException;
import java.time.temporal.ValueRange;
import java.util.Locale;

public enum Month implements TemporalAccessor, TemporalAdjuster {
    JANUARY,
    FEBRUARY,
    MARCH,
    APRIL,
    MAY,
    JUNE,
    JULY,
    AUGUST,
    SEPTEMBER,
    OCTOBER,
    NOVEMBER,
    DECEMBER;

    private static final Month[] ENUMS = Month.values();

    public static Month of(int month) {
        if (month < 1 || month > 12) throw new DateTimeException("Invalid value for MonthOfYear: " + month);
        return ENUMS[month - 1];
    }

    public static Month from(TemporalAccessor temporal) {
        if (temporal instanceof Month) return (Month) temporal;
        try {
            if (!IsoChronology.INSTANCE.equals(Chronology.from(temporal))) temporal = LocalDate.from(temporal);
            return of(temporal.get(ChronoField.MONTH_OF_YEAR));
        } catch (DateTimeException ex) {
            throw new DateTimeException("Unable to obtain Month from TemporalAccessor: " + temporal + " of type "
                + temporal.getClass().getName(), ex);
        }
    }

    public int getValue() {
        return ordinal() + 1;
    }

    public String getDisplayName(TextStyle style, Locale locale) {
        return new DateTimeFormatterBuilder().appendText(ChronoField.MONTH_OF_YEAR, style).toFormatter(locale).format(this);
    }

    @Override
    public boolean isSupported(TemporalField field) {
        if (field instanceof ChronoField) return field == ChronoField.MONTH_OF_YEAR;
        return field != null && field.isSupportedBy(this);
    }

    @Override
    public ValueRange range(TemporalField field) {
        if (field == ChronoField.MONTH_OF_YEAR) return field.range();
        return TemporalAccessor.super.range(field);
    }

    @Override
    public int get(TemporalField field) {
        if (field == ChronoField.MONTH_OF_YEAR) return getValue();
        return TemporalAccessor.super.get(field);
    }

    @Override
    public long getLong(TemporalField field) {
        if (field == ChronoField.MONTH_OF_YEAR) return getValue();
        if (field instanceof ChronoField) throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
        return field.getFrom(this);
    }

    public Month plus(long months) {
        int amount = (int) (months % 12);
        return ENUMS[(ordinal() + (amount + 12)) % 12];
    }

    public Month minus(long months) {
        return plus(-(months % 12));
    }

    public int length(boolean leapYear) {
        switch (this) {
            case FEBRUARY: return leapYear ? 29 : 28;
            case APRIL: case JUNE: case SEPTEMBER: case NOVEMBER: return 30;
            default: return 31;
        }
    }

    public int minLength() {
        return this == FEBRUARY ? 28 : length(false);
    }

    public int maxLength() {
        return this == FEBRUARY ? 29 : length(false);
    }

    /** Day of the year (1-based) on which the month starts. */
    public int firstDayOfYear(boolean leapYear) {
        int leap = leapYear ? 1 : 0;
        switch (this) {
            case JANUARY: return 1;
            case FEBRUARY: return 32;
            case MARCH: return 60 + leap;
            case APRIL: return 91 + leap;
            case MAY: return 121 + leap;
            case JUNE: return 152 + leap;
            case JULY: return 182 + leap;
            case AUGUST: return 213 + leap;
            case SEPTEMBER: return 244 + leap;
            case OCTOBER: return 274 + leap;
            case NOVEMBER: return 305 + leap;
            default: return 335 + leap;
        }
    }

    public Month firstMonthOfQuarter() {
        return ENUMS[(ordinal() / 3) * 3];
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.chronology()) return (R) IsoChronology.INSTANCE;
        if (query == TemporalQueries.precision()) return (R) ChronoUnit.MONTHS;
        return TemporalAccessor.super.query(query);
    }

    @Override
    public Temporal adjustInto(Temporal temporal) {
        if (!Chronology.from(temporal).equals(IsoChronology.INSTANCE))
            throw new DateTimeException("Adjustment only supported on ISO date-time");
        return temporal.with(ChronoField.MONTH_OF_YEAR, getValue());
    }
}

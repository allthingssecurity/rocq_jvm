/* rocq-jvm model of java.time.chrono.ChronoLocalDate (clean-room, Apache-2.0): JDK 21's default
 * methods; the ones the JDK implements with ChronoLocalDateImpl's chronology check do the same check
 * (ChronoHelp.ensureDate). atTime of a non-ISO date (ChronoLocalDateTimeImpl) is STUCK. */
package java.time.chrono;

import java.io.Serializable;
import java.time.DateTimeException;
import java.time.LocalTime;
import java.time.format.DateTimeFormatter;
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
import java.util.Comparator;
import java.util.Objects;

public interface ChronoLocalDate extends Temporal, TemporalAdjuster, Comparable<ChronoLocalDate> {
    static Comparator<ChronoLocalDate> timeLineOrder() {
        return (Comparator<ChronoLocalDate> & Serializable) (d1, d2) -> Long.compare(d1.toEpochDay(), d2.toEpochDay());
    }

    static ChronoLocalDate from(TemporalAccessor temporal) {
        if (temporal instanceof ChronoLocalDate) return (ChronoLocalDate) temporal;
        Objects.requireNonNull(temporal, "temporal");
        Chronology chrono = temporal.query(TemporalQueries.chronology());
        if (chrono == null)
            throw new DateTimeException("Unable to obtain ChronoLocalDate from TemporalAccessor: " + temporal.getClass());
        return chrono.date(temporal);
    }

    Chronology getChronology();

    default Era getEra() {
        return getChronology().eraOf(get(ChronoField.ERA));
    }

    default boolean isLeapYear() {
        return getChronology().isLeapYear(getLong(ChronoField.YEAR));
    }

    int lengthOfMonth();

    default int lengthOfYear() {
        return isLeapYear() ? 366 : 365;
    }

    @Override
    default boolean isSupported(TemporalField field) {
        if (field instanceof ChronoField) return field.isDateBased();
        return field != null && field.isSupportedBy(this);
    }

    @Override
    default boolean isSupported(TemporalUnit unit) {
        if (unit instanceof ChronoUnit) return unit.isDateBased();
        return unit != null && unit.isSupportedBy(this);
    }

    @Override
    default ChronoLocalDate with(TemporalAdjuster adjuster) {
        return ChronoHelp.ensureDate(getChronology(), Temporal.super.with(adjuster));
    }

    @Override
    default ChronoLocalDate with(TemporalField field, long newValue) {
        if (field instanceof ChronoField) throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
        return ChronoHelp.ensureDate(getChronology(), field.adjustInto(this, newValue));
    }

    @Override
    default ChronoLocalDate plus(TemporalAmount amount) {
        return ChronoHelp.ensureDate(getChronology(), Temporal.super.plus(amount));
    }

    @Override
    default ChronoLocalDate plus(long amountToAdd, TemporalUnit unit) {
        if (unit instanceof ChronoUnit) throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
        return ChronoHelp.ensureDate(getChronology(), unit.addTo(this, amountToAdd));
    }

    @Override
    default ChronoLocalDate minus(TemporalAmount amount) {
        return ChronoHelp.ensureDate(getChronology(), Temporal.super.minus(amount));
    }

    @Override
    default ChronoLocalDate minus(long amountToSubtract, TemporalUnit unit) {
        return ChronoHelp.ensureDate(getChronology(), Temporal.super.minus(amountToSubtract, unit));
    }

    @Override
    @SuppressWarnings("unchecked")
    default <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.zoneId() || query == TemporalQueries.zone() || query == TemporalQueries.offset())
            return null;
        if (query == TemporalQueries.localTime()) return null;
        if (query == TemporalQueries.chronology()) return (R) getChronology();
        if (query == TemporalQueries.precision()) return (R) ChronoUnit.DAYS;
        return query.queryFrom(this);
    }

    @Override
    default Temporal adjustInto(Temporal temporal) {
        return temporal.with(ChronoField.EPOCH_DAY, toEpochDay());
    }

    @Override
    long until(Temporal endExclusive, TemporalUnit unit);

    ChronoPeriod until(ChronoLocalDate endDateExclusive);

    default String format(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.format(this);
    }

    default ChronoLocalDateTime<?> atTime(LocalTime localTime) {
        throw ModelStuckChrono.unsupported("ChronoLocalDate.atTime: ChronoLocalDateTimeImpl");
    }

    default long toEpochDay() {
        return getLong(ChronoField.EPOCH_DAY);
    }

    @Override
    default int compareTo(ChronoLocalDate other) {
        int cmp = Long.compare(toEpochDay(), other.toEpochDay());
        if (cmp == 0) cmp = getChronology().compareTo(other.getChronology());
        return cmp;
    }

    default boolean isAfter(ChronoLocalDate other) {
        return this.toEpochDay() > other.toEpochDay();
    }

    default boolean isBefore(ChronoLocalDate other) {
        return this.toEpochDay() < other.toEpochDay();
    }

    default boolean isEqual(ChronoLocalDate other) {
        return this.toEpochDay() == other.toEpochDay();
    }

    @Override
    boolean equals(Object obj);

    @Override
    int hashCode();

    @Override
    String toString();
}

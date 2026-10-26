/* rocq-jvm model of java.time.chrono.Chronology (clean-room, Apache-2.0): only the ISO calendar is
 * modelled. of("ISO") is IsoChronology.INSTANCE; other ids, ofLocale, getAvailableChronologies, the
 * dateNow defaults (host clock), getDisplayName and the defaults that need ChronoLocalDateTimeImpl /
 * ChronoZonedDateTimeImpl / ChronoPeriodImpl are STUCK. */
package java.time.chrono;

import java.time.DateTimeException;
import java.time.Instant;
import java.time.LocalTime;
import java.time.ZoneId;
import java.time.ZoneOffset;
import java.time.format.ResolverStyle;
import java.time.format.TextStyle;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalField;
import java.time.temporal.TemporalQueries;
import java.time.temporal.ValueRange;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public interface Chronology extends Comparable<Chronology> {
    static Chronology from(TemporalAccessor temporal) {
        Objects.requireNonNull(temporal, "temporal");
        Chronology obj = temporal.query(TemporalQueries.chronology());
        return obj != null ? obj : IsoChronology.INSTANCE;
    }

    static Chronology ofLocale(Locale locale) {
        Objects.requireNonNull(locale, "locale");
        throw ModelStuckChrono.unsupported("Chronology.ofLocale");
    }

    static Chronology of(String id) {
        Objects.requireNonNull(id, "id");
        if (id.equals("ISO") || id.equals("iso8601")) return IsoChronology.INSTANCE;
        throw ModelStuckChrono.unsupported("Chronology.of: non-ISO chronologies");
    }

    static Set<Chronology> getAvailableChronologies() {
        throw ModelStuckChrono.unsupported("Chronology.getAvailableChronologies");
    }

    String getId();

    String getCalendarType();

    default ChronoLocalDate date(Era era, int yearOfEra, int month, int dayOfMonth) {
        return date(prolepticYear(era, yearOfEra), month, dayOfMonth);
    }

    ChronoLocalDate date(int prolepticYear, int month, int dayOfMonth);

    default ChronoLocalDate dateYearDay(Era era, int yearOfEra, int dayOfYear) {
        return dateYearDay(prolepticYear(era, yearOfEra), dayOfYear);
    }

    ChronoLocalDate dateYearDay(int prolepticYear, int dayOfYear);

    ChronoLocalDate dateEpochDay(long epochDay);

    default ChronoLocalDate dateNow() {
        throw ModelStuckChrono.unsupported("Chronology.dateNow: host clock");
    }

    default ChronoLocalDate dateNow(ZoneId zone) {
        throw ModelStuckChrono.unsupported("Chronology.dateNow: host clock");
    }

    default ChronoLocalDate dateNow(java.time.Clock clock) {
        Objects.requireNonNull(clock, "clock");
        return date(java.time.LocalDate.now(clock));
    }

    ChronoLocalDate date(TemporalAccessor temporal);

    default ChronoLocalDateTime<? extends ChronoLocalDate> localDateTime(TemporalAccessor temporal) {
        try {
            return date(temporal).atTime(LocalTime.from(temporal));
        } catch (DateTimeException ex) {
            throw new DateTimeException("Unable to obtain ChronoLocalDateTime from TemporalAccessor: " + temporal.getClass(), ex);
        }
    }

    default ChronoZonedDateTime<? extends ChronoLocalDate> zonedDateTime(TemporalAccessor temporal) {
        throw ModelStuckChrono.unsupported("Chronology.zonedDateTime: ChronoZonedDateTimeImpl");
    }

    default ChronoZonedDateTime<? extends ChronoLocalDate> zonedDateTime(Instant instant, ZoneId zone) {
        throw ModelStuckChrono.unsupported("Chronology.zonedDateTime: ChronoZonedDateTimeImpl");
    }

    boolean isLeapYear(long prolepticYear);

    int prolepticYear(Era era, int yearOfEra);

    Era eraOf(int eraValue);

    List<Era> eras();

    ValueRange range(ChronoField field);

    default String getDisplayName(TextStyle style, Locale locale) {
        throw ModelStuckChrono.unsupported("Chronology.getDisplayName: locale resources");
    }

    ChronoLocalDate resolveDate(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle);

    default ChronoPeriod period(int years, int months, int days) {
        throw ModelStuckChrono.unsupported("Chronology.period: ChronoPeriodImpl");
    }

    default long epochSecond(int prolepticYear, int month, int dayOfMonth, int hour, int minute, int second,
                             ZoneOffset zoneOffset) {
        Objects.requireNonNull(zoneOffset, "zoneOffset");
        ChronoField.HOUR_OF_DAY.checkValidValue(hour);
        ChronoField.MINUTE_OF_HOUR.checkValidValue(minute);
        ChronoField.SECOND_OF_MINUTE.checkValidValue(second);
        long daysInSec = Math.multiplyExact(date(prolepticYear, month, dayOfMonth).toEpochDay(), 86400);
        long timeinSec = (hour * 60 + minute) * 60 + second;
        return Math.addExact(daysInSec, timeinSec - zoneOffset.getTotalSeconds());
    }

    default long epochSecond(Era era, int yearOfEra, int month, int dayOfMonth, int hour, int minute, int second,
                             ZoneOffset zoneOffset) {
        Objects.requireNonNull(era, "era");
        return epochSecond(prolepticYear(era, yearOfEra), month, dayOfMonth, hour, minute, second, zoneOffset);
    }

    default boolean isIsoBased() {
        return false;
    }

    @Override
    int compareTo(Chronology other);

    @Override
    boolean equals(Object obj);

    @Override
    int hashCode();

    @Override
    String toString();
}

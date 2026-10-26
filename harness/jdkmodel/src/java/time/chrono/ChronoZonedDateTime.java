/* rocq-jvm model of java.time.chrono.ChronoZonedDateTime (clean-room, Apache-2.0): JDK 21's default
 * methods; with/plus/minus defaults (checked by the JDK through ChronoZonedDateTimeImpl, not
 * modelled) are STUCK. */
package java.time.chrono;

import java.io.Serializable;
import java.time.DateTimeException;
import java.time.Instant;
import java.time.LocalTime;
import java.time.ZoneId;
import java.time.ZoneOffset;
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
import java.time.temporal.ValueRange;
import java.util.Comparator;
import java.util.Objects;

public interface ChronoZonedDateTime<D extends ChronoLocalDate> extends Temporal, Comparable<ChronoZonedDateTime<?>> {
    static Comparator<ChronoZonedDateTime<?>> timeLineOrder() {
        return (Comparator<ChronoZonedDateTime<?>> & Serializable) (a, b) -> {
            int cmp = Long.compare(a.toEpochSecond(), b.toEpochSecond());
            if (cmp == 0) cmp = Long.compare(a.toLocalTime().getNano(), b.toLocalTime().getNano());
            return cmp;
        };
    }

    static ChronoZonedDateTime<?> from(TemporalAccessor temporal) {
        if (temporal instanceof ChronoZonedDateTime) return (ChronoZonedDateTime<?>) temporal;
        Objects.requireNonNull(temporal, "temporal");
        Chronology chrono = temporal.query(TemporalQueries.chronology());
        if (chrono == null)
            throw new DateTimeException("Unable to obtain ChronoZonedDateTime from TemporalAccessor: " + temporal.getClass());
        return chrono.zonedDateTime(temporal);
    }

    @Override
    default ValueRange range(TemporalField field) {
        if (field instanceof ChronoField) {
            if (field == ChronoField.INSTANT_SECONDS || field == ChronoField.OFFSET_SECONDS) return field.range();
            return toLocalDateTime().range(field);
        }
        return field.rangeRefinedBy(this);
    }

    @Override
    default int get(TemporalField field) {
        if (field instanceof ChronoField) {
            if (field == ChronoField.INSTANT_SECONDS)
                throw new UnsupportedTemporalTypeException("Invalid field 'InstantSeconds' for get() method, use getLong() instead");
            if (field == ChronoField.OFFSET_SECONDS) return getOffset().getTotalSeconds();
            return toLocalDateTime().get(field);
        }
        return Temporal.super.get(field);
    }

    @Override
    default long getLong(TemporalField field) {
        if (field instanceof ChronoField) {
            if (field == ChronoField.INSTANT_SECONDS) return toEpochSecond();
            if (field == ChronoField.OFFSET_SECONDS) return getOffset().getTotalSeconds();
            return toLocalDateTime().getLong(field);
        }
        return field.getFrom(this);
    }

    default D toLocalDate() {
        return toLocalDateTime().toLocalDate();
    }

    default LocalTime toLocalTime() {
        return toLocalDateTime().toLocalTime();
    }

    ChronoLocalDateTime<D> toLocalDateTime();

    default Chronology getChronology() {
        return toLocalDate().getChronology();
    }

    ZoneOffset getOffset();

    ZoneId getZone();

    ChronoZonedDateTime<D> withEarlierOffsetAtOverlap();

    ChronoZonedDateTime<D> withLaterOffsetAtOverlap();

    ChronoZonedDateTime<D> withZoneSameLocal(ZoneId zone);

    ChronoZonedDateTime<D> withZoneSameInstant(ZoneId zone);

    @Override
    boolean isSupported(TemporalField field);

    @Override
    default boolean isSupported(TemporalUnit unit) {
        if (unit instanceof ChronoUnit) return unit != ChronoUnit.FOREVER;
        return unit != null && unit.isSupportedBy(this);
    }

    @Override
    default ChronoZonedDateTime<D> with(TemporalAdjuster adjuster) {
        throw ModelStuckChrono.unsupported("ChronoZonedDateTime.with: ChronoZonedDateTimeImpl");
    }

    @Override
    ChronoZonedDateTime<D> with(TemporalField field, long newValue);

    @Override
    default ChronoZonedDateTime<D> plus(TemporalAmount amount) {
        throw ModelStuckChrono.unsupported("ChronoZonedDateTime.plus: ChronoZonedDateTimeImpl");
    }

    @Override
    ChronoZonedDateTime<D> plus(long amountToAdd, TemporalUnit unit);

    @Override
    default ChronoZonedDateTime<D> minus(TemporalAmount amount) {
        throw ModelStuckChrono.unsupported("ChronoZonedDateTime.minus: ChronoZonedDateTimeImpl");
    }

    @Override
    default ChronoZonedDateTime<D> minus(long amountToSubtract, TemporalUnit unit) {
        throw ModelStuckChrono.unsupported("ChronoZonedDateTime.minus: ChronoZonedDateTimeImpl");
    }

    @Override
    @SuppressWarnings("unchecked")
    default <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.zone() || query == TemporalQueries.zoneId()) return (R) getZone();
        if (query == TemporalQueries.offset()) return (R) getOffset();
        if (query == TemporalQueries.localTime()) return (R) toLocalTime();
        if (query == TemporalQueries.chronology()) return (R) getChronology();
        if (query == TemporalQueries.precision()) return (R) ChronoUnit.NANOS;
        return query.queryFrom(this);
    }

    default String format(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.format(this);
    }

    default Instant toInstant() {
        return Instant.ofEpochSecond(toEpochSecond(), toLocalTime().getNano());
    }

    default long toEpochSecond() {
        long epochDay = toLocalDate().toEpochDay();
        long secs = epochDay * 86400 + toLocalTime().toSecondOfDay();
        secs -= getOffset().getTotalSeconds();
        return secs;
    }

    @Override
    default int compareTo(ChronoZonedDateTime<?> other) {
        int cmp = Long.compare(toEpochSecond(), other.toEpochSecond());
        if (cmp == 0) {
            cmp = toLocalTime().getNano() - other.toLocalTime().getNano();
            if (cmp == 0) {
                cmp = toLocalDateTime().compareTo(other.toLocalDateTime());
                if (cmp == 0) {
                    cmp = getZone().getId().compareTo(other.getZone().getId());
                    if (cmp == 0) cmp = getChronology().compareTo(other.getChronology());
                }
            }
        }
        return cmp;
    }

    default boolean isBefore(ChronoZonedDateTime<?> other) {
        long a = toEpochSecond(), b = other.toEpochSecond();
        return a < b || (a == b && toLocalTime().getNano() < other.toLocalTime().getNano());
    }

    default boolean isAfter(ChronoZonedDateTime<?> other) {
        long a = toEpochSecond(), b = other.toEpochSecond();
        return a > b || (a == b && toLocalTime().getNano() > other.toLocalTime().getNano());
    }

    default boolean isEqual(ChronoZonedDateTime<?> other) {
        return toEpochSecond() == other.toEpochSecond() && toLocalTime().getNano() == other.toLocalTime().getNano();
    }

    @Override
    boolean equals(Object obj);

    @Override
    int hashCode();

    @Override
    String toString();
}

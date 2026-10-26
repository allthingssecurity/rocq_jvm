/* rocq-jvm model of java.time.chrono.ChronoLocalDateTime (clean-room, Apache-2.0): JDK 21's default
 * methods; with/plus/minus defaults (the JDK checks them through ChronoLocalDateTimeImpl, not
 * modelled) and from() of a non-ISO chronology are STUCK. */
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
import java.util.Comparator;
import java.util.Objects;

public interface ChronoLocalDateTime<D extends ChronoLocalDate>
        extends Temporal, TemporalAdjuster, Comparable<ChronoLocalDateTime<?>> {
    static Comparator<ChronoLocalDateTime<?>> timeLineOrder() {
        return (Comparator<ChronoLocalDateTime<? extends ChronoLocalDate>> & Serializable) (a, b) -> {
            int cmp = Long.compare(a.toLocalDate().toEpochDay(), b.toLocalDate().toEpochDay());
            if (cmp == 0) cmp = Long.compare(a.toLocalTime().toNanoOfDay(), b.toLocalTime().toNanoOfDay());
            return cmp;
        };
    }

    static ChronoLocalDateTime<?> from(TemporalAccessor temporal) {
        if (temporal instanceof ChronoLocalDateTime) return (ChronoLocalDateTime<?>) temporal;
        Objects.requireNonNull(temporal, "temporal");
        Chronology chrono = temporal.query(TemporalQueries.chronology());
        if (chrono == null)
            throw new DateTimeException("Unable to obtain ChronoLocalDateTime from TemporalAccessor: " + temporal.getClass());
        return chrono.localDateTime(temporal);
    }

    default Chronology getChronology() {
        return toLocalDate().getChronology();
    }

    D toLocalDate();

    LocalTime toLocalTime();

    @Override
    boolean isSupported(TemporalField field);

    @Override
    default boolean isSupported(TemporalUnit unit) {
        if (unit instanceof ChronoUnit) return unit != ChronoUnit.FOREVER;
        return unit != null && unit.isSupportedBy(this);
    }

    @Override
    default ChronoLocalDateTime<D> with(TemporalAdjuster adjuster) {
        throw ModelStuckChrono.unsupported("ChronoLocalDateTime.with: ChronoLocalDateTimeImpl");
    }

    @Override
    ChronoLocalDateTime<D> with(TemporalField field, long newValue);

    @Override
    default ChronoLocalDateTime<D> plus(TemporalAmount amount) {
        throw ModelStuckChrono.unsupported("ChronoLocalDateTime.plus: ChronoLocalDateTimeImpl");
    }

    @Override
    ChronoLocalDateTime<D> plus(long amountToAdd, TemporalUnit unit);

    @Override
    default ChronoLocalDateTime<D> minus(TemporalAmount amount) {
        throw ModelStuckChrono.unsupported("ChronoLocalDateTime.minus: ChronoLocalDateTimeImpl");
    }

    @Override
    default ChronoLocalDateTime<D> minus(long amountToSubtract, TemporalUnit unit) {
        throw ModelStuckChrono.unsupported("ChronoLocalDateTime.minus: ChronoLocalDateTimeImpl");
    }

    @Override
    @SuppressWarnings("unchecked")
    default <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.zoneId() || query == TemporalQueries.zone() || query == TemporalQueries.offset())
            return null;
        if (query == TemporalQueries.localTime()) return (R) toLocalTime();
        if (query == TemporalQueries.chronology()) return (R) getChronology();
        if (query == TemporalQueries.precision()) return (R) ChronoUnit.NANOS;
        return query.queryFrom(this);
    }

    @Override
    default Temporal adjustInto(Temporal temporal) {
        return temporal.with(ChronoField.EPOCH_DAY, toLocalDate().toEpochDay())
            .with(ChronoField.NANO_OF_DAY, toLocalTime().toNanoOfDay());
    }

    default String format(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.format(this);
    }

    ChronoZonedDateTime<D> atZone(ZoneId zone);

    default Instant toInstant(ZoneOffset offset) {
        return Instant.ofEpochSecond(toEpochSecond(offset), toLocalTime().getNano());
    }

    default long toEpochSecond(ZoneOffset offset) {
        Objects.requireNonNull(offset, "offset");
        long epochDay = toLocalDate().toEpochDay();
        long secs = epochDay * 86400 + toLocalTime().toSecondOfDay();
        secs -= offset.getTotalSeconds();
        return secs;
    }

    @Override
    default int compareTo(ChronoLocalDateTime<?> other) {
        int cmp = toLocalDate().compareTo(other.toLocalDate());
        if (cmp == 0) {
            cmp = toLocalTime().compareTo(other.toLocalTime());
            if (cmp == 0) cmp = getChronology().compareTo(other.getChronology());
        }
        return cmp;
    }

    default boolean isAfter(ChronoLocalDateTime<?> other) {
        long a = this.toLocalDate().toEpochDay(), b = other.toLocalDate().toEpochDay();
        return a > b || (a == b && this.toLocalTime().toNanoOfDay() > other.toLocalTime().toNanoOfDay());
    }

    default boolean isBefore(ChronoLocalDateTime<?> other) {
        long a = this.toLocalDate().toEpochDay(), b = other.toLocalDate().toEpochDay();
        return a < b || (a == b && this.toLocalTime().toNanoOfDay() < other.toLocalTime().toNanoOfDay());
    }

    default boolean isEqual(ChronoLocalDateTime<?> other) {
        return this.toLocalTime().toNanoOfDay() == other.toLocalTime().toNanoOfDay()
            && this.toLocalDate().toEpochDay() == other.toLocalDate().toEpochDay();
    }

    @Override
    boolean equals(Object obj);

    @Override
    int hashCode();

    @Override
    String toString();
}

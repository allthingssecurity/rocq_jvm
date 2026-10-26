/*
 * rocq-jvm model of java.time.Instant (clean-room, Apache-2.0): epoch seconds + nanos as in JDK 21
 * with the JDK's range check ("Instant exceeds minimum or maximum instant"), Math.*Exact overflow
 * errors, truncation, until per unit, toEpochMilli, field access and texts, hashCode; toString and
 * parse go through the model ISO_INSTANT (years beyond 9999 and negative years as the JDK prints
 * them). STUCK: now() and now(ZoneId) (host clock: absent; now(Clock) is modelled), serialization.
 */
package java.time;

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
import java.util.Objects;

public final class Instant implements Temporal, TemporalAdjuster, Comparable<Instant>, java.io.Serializable {
    private static final long serialVersionUID = -665713676816604388L;

    public static final Instant EPOCH = new Instant(0, 0);
    private static final long MIN_SECOND = -31557014167219200L;
    private static final long MAX_SECOND = 31556889864403199L;
    public static final Instant MIN = Instant.ofEpochSecond(MIN_SECOND, 0);
    public static final Instant MAX = Instant.ofEpochSecond(MAX_SECOND, 999_999_999);

    private final long seconds;
    private final int nanos;

    private Instant(long epochSecond, int nanos) {
        this.seconds = epochSecond;
        this.nanos = nanos;
    }

    public static Instant now(Clock clock) {
        Objects.requireNonNull(clock, "clock");
        return clock.instant();
    }

    public static Instant ofEpochSecond(long epochSecond) {
        return create(epochSecond, 0);
    }

    public static Instant ofEpochSecond(long epochSecond, long nanoAdjustment) {
        long secs = Math.addExact(epochSecond, Math.floorDiv(nanoAdjustment, LocalTime.NANOS_PER_SECOND));
        int nos = (int) Math.floorMod(nanoAdjustment, LocalTime.NANOS_PER_SECOND);
        return create(secs, nos);
    }

    public static Instant ofEpochMilli(long epochMilli) {
        long secs = Math.floorDiv(epochMilli, 1000);
        int mos = Math.floorMod(epochMilli, 1000);
        return create(secs, mos * 1000_000);
    }

    public static Instant from(TemporalAccessor temporal) {
        if (temporal instanceof Instant) return (Instant) temporal;
        Objects.requireNonNull(temporal, "temporal");
        try {
            long instantSecs = temporal.getLong(ChronoField.INSTANT_SECONDS);
            int nanoOfSecond = temporal.get(ChronoField.NANO_OF_SECOND);
            return Instant.ofEpochSecond(instantSecs, nanoOfSecond);
        } catch (DateTimeException ex) {
            throw new DateTimeException("Unable to obtain Instant from TemporalAccessor: " + temporal + " of type "
                + temporal.getClass().getName(), ex);
        }
    }

    public static Instant parse(final CharSequence text) {
        return DateTimeFormatter.ISO_INSTANT.parse(text, Instant::from);
    }

    private static Instant create(long seconds, int nanoOfSecond) {
        if ((seconds | nanoOfSecond) == 0) return EPOCH;
        if (seconds < MIN_SECOND || seconds > MAX_SECOND)
            throw new DateTimeException("Instant exceeds minimum or maximum instant");
        return new Instant(seconds, nanoOfSecond);
    }

    @Override
    public boolean isSupported(TemporalField field) {
        if (field instanceof ChronoField)
            return field == ChronoField.INSTANT_SECONDS || field == ChronoField.NANO_OF_SECOND
                || field == ChronoField.MICRO_OF_SECOND || field == ChronoField.MILLI_OF_SECOND;
        return field != null && field.isSupportedBy(this);
    }

    @Override
    public boolean isSupported(TemporalUnit unit) {
        if (unit instanceof ChronoUnit) return unit.isTimeBased() || unit == ChronoUnit.DAYS;
        return unit != null && unit.isSupportedBy(this);
    }

    @Override
    public ValueRange range(TemporalField field) {
        return Temporal.super.range(field);
    }

    @Override
    public int get(TemporalField field) {
        if (field instanceof ChronoField) {
            switch ((ChronoField) field) {
                case NANO_OF_SECOND: return nanos;
                case MICRO_OF_SECOND: return nanos / 1000;
                case MILLI_OF_SECOND: return nanos / 1000_000;
                default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            }
        }
        return range(field).checkValidIntValue(field.getFrom(this), field);
    }

    @Override
    public long getLong(TemporalField field) {
        if (field instanceof ChronoField) {
            switch ((ChronoField) field) {
                case NANO_OF_SECOND: return nanos;
                case MICRO_OF_SECOND: return nanos / 1000;
                case MILLI_OF_SECOND: return nanos / 1000_000;
                case INSTANT_SECONDS: return seconds;
                default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            }
        }
        return field.getFrom(this);
    }

    public long getEpochSecond() {
        return seconds;
    }

    public int getNano() {
        return nanos;
    }

    @Override
    public Instant with(TemporalAdjuster adjuster) {
        return (Instant) adjuster.adjustInto(this);
    }

    @Override
    public Instant with(TemporalField field, long newValue) {
        if (field instanceof ChronoField) {
            ChronoField f = (ChronoField) field;
            f.checkValidValue(newValue);
            switch (f) {
                case MILLI_OF_SECOND: {
                    int nval = (int) newValue * 1000_000;
                    return nval != nanos ? create(seconds, nval) : this;
                }
                case MICRO_OF_SECOND: {
                    int nval = (int) newValue * 1000;
                    return nval != nanos ? create(seconds, nval) : this;
                }
                case NANO_OF_SECOND: return newValue != nanos ? create(seconds, (int) newValue) : this;
                case INSTANT_SECONDS: return newValue != seconds ? create(newValue, nanos) : this;
                default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            }
        }
        return field.adjustInto(this, newValue);
    }

    public Instant truncatedTo(TemporalUnit unit) {
        if (unit == ChronoUnit.NANOS) return this;
        Duration unitDur = unit.getDuration();
        if (unitDur.getSeconds() > LocalTime.SECONDS_PER_DAY)
            throw new UnsupportedTemporalTypeException("Unit is too large to be used for truncation");
        long dur = unitDur.toNanos();
        if ((LocalTime.NANOS_PER_DAY % dur) != 0)
            throw new UnsupportedTemporalTypeException("Unit must divide into a standard day without remainder");
        long nod = (seconds % LocalTime.SECONDS_PER_DAY) * LocalTime.NANOS_PER_SECOND + nanos;
        long result = Math.floorDiv(nod, dur) * dur;
        return plusNanos(result - nod);
    }

    @Override
    public Instant plus(TemporalAmount amountToAdd) {
        return (Instant) amountToAdd.addTo(this);
    }

    @Override
    public Instant plus(long amountToAdd, TemporalUnit unit) {
        if (unit instanceof ChronoUnit) {
            switch ((ChronoUnit) unit) {
                case NANOS: return plusNanos(amountToAdd);
                case MICROS: return plus(amountToAdd / 1000_000, (amountToAdd % 1000_000) * 1000);
                case MILLIS: return plusMillis(amountToAdd);
                case SECONDS: return plusSeconds(amountToAdd);
                case MINUTES: return plusSeconds(Math.multiplyExact(amountToAdd, LocalTime.SECONDS_PER_MINUTE));
                case HOURS: return plusSeconds(Math.multiplyExact(amountToAdd, LocalTime.SECONDS_PER_HOUR));
                case HALF_DAYS: return plusSeconds(Math.multiplyExact(amountToAdd, LocalTime.SECONDS_PER_DAY / 2));
                case DAYS: return plusSeconds(Math.multiplyExact(amountToAdd, LocalTime.SECONDS_PER_DAY));
                default: throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
            }
        }
        return unit.addTo(this, amountToAdd);
    }

    public Instant plusSeconds(long secondsToAdd) {
        if (secondsToAdd == 0) return this;
        return create(Math.addExact(seconds, secondsToAdd), nanos);
    }

    public Instant plusMillis(long millisToAdd) {
        return plus(millisToAdd / 1000, (millisToAdd % 1000) * 1000_000);
    }

    public Instant plusNanos(long nanosToAdd) {
        return plus(0, nanosToAdd);
    }

    private Instant plus(long secondsToAdd, long nanosToAdd) {
        if ((secondsToAdd | nanosToAdd) == 0) return this;
        long epochSec = Math.addExact(seconds, secondsToAdd);
        epochSec = Math.addExact(epochSec, nanosToAdd / LocalTime.NANOS_PER_SECOND);
        nanosToAdd = nanosToAdd % LocalTime.NANOS_PER_SECOND;
        return ofEpochSecond(epochSec, nanos + nanosToAdd);
    }

    @Override
    public Instant minus(TemporalAmount amountToSubtract) {
        return (Instant) amountToSubtract.subtractFrom(this);
    }

    @Override
    public Instant minus(long amountToSubtract, TemporalUnit unit) {
        return amountToSubtract == Long.MIN_VALUE ? plus(Long.MAX_VALUE, unit).plus(1, unit) : plus(-amountToSubtract, unit);
    }

    public Instant minusSeconds(long n) {
        if (n == Long.MIN_VALUE) return plusSeconds(Long.MAX_VALUE).plusSeconds(1);
        return plusSeconds(-n);
    }

    public Instant minusMillis(long n) {
        if (n == Long.MIN_VALUE) return plusMillis(Long.MAX_VALUE).plusMillis(1);
        return plusMillis(-n);
    }

    public Instant minusNanos(long n) {
        if (n == Long.MIN_VALUE) return plusNanos(Long.MAX_VALUE).plusNanos(1);
        return plusNanos(-n);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.precision()) return (R) ChronoUnit.NANOS;
        if (query == TemporalQueries.chronology() || query == TemporalQueries.zoneId() || query == TemporalQueries.zone()
            || query == TemporalQueries.offset() || query == TemporalQueries.localDate()
            || query == TemporalQueries.localTime()) return null;
        return query.queryFrom(this);
    }

    @Override
    public Temporal adjustInto(Temporal temporal) {
        return temporal.with(ChronoField.INSTANT_SECONDS, seconds).with(ChronoField.NANO_OF_SECOND, nanos);
    }

    @Override
    public long until(Temporal endExclusive, TemporalUnit unit) {
        Instant end = Instant.from(endExclusive);
        if (unit instanceof ChronoUnit) {
            switch ((ChronoUnit) unit) {
                case NANOS: return nanosUntil(end);
                case MICROS: return microsUntil(end);
                case MILLIS: return millisUntil(end);
                case SECONDS: return secondsUntil(end);
                case MINUTES: return secondsUntil(end) / LocalTime.SECONDS_PER_MINUTE;
                case HOURS: return secondsUntil(end) / LocalTime.SECONDS_PER_HOUR;
                case HALF_DAYS: return secondsUntil(end) / (12 * LocalTime.SECONDS_PER_HOUR);
                case DAYS: return secondsUntil(end) / LocalTime.SECONDS_PER_DAY;
                default: throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
            }
        }
        return unit.between(this, end);
    }

    private long nanosUntil(Instant end) {
        long secsDiff = Math.subtractExact(end.seconds, seconds);
        long totalNanos = Math.multiplyExact(secsDiff, LocalTime.NANOS_PER_SECOND);
        return Math.addExact(totalNanos, end.nanos - nanos);
    }

    private long microsUntil(Instant end) {
        long microsDiff = Math.multiplyExact(end.seconds - seconds, LocalTime.MICROS_PER_SECOND);
        int nanosDiff = end.nanos - nanos;
        if (microsDiff > 0 && nanosDiff < 0) return (microsDiff - 1_000_000) + (nanosDiff + 1_000_000_000) / 1_000;
        if (microsDiff < 0 && nanosDiff > 0) return (microsDiff + 1_000_000) + (nanosDiff - 1_000_000_000) / 1_000;
        return Math.addExact(microsDiff, nanosDiff / 1_000);
    }

    private long millisUntil(Instant end) {
        long millisDiff = Math.multiplyExact(end.seconds - seconds, LocalTime.MILLIS_PER_SECOND);
        int nanosDiff = end.nanos - nanos;
        if (millisDiff > 0 && nanosDiff < 0) return (millisDiff - 1_000) + (nanosDiff + 1_000_000_000) / 1_000_000;
        if (millisDiff < 0 && nanosDiff > 0) return (millisDiff + 1_000) + (nanosDiff - 1_000_000_000) / 1_000_000;
        return Math.addExact(millisDiff, nanosDiff / 1_000_000);
    }

    private long secondsUntil(Instant end) {
        long secsDiff = Math.subtractExact(end.seconds, seconds);
        int nanosDiff = end.nanos - nanos;
        if (secsDiff > 0 && nanosDiff < 0) {
            secsDiff--;
        } else if (secsDiff < 0 && nanosDiff > 0) {
            secsDiff++;
        }
        return secsDiff;
    }

    public OffsetDateTime atOffset(ZoneOffset offset) {
        return OffsetDateTime.ofInstant(this, offset);
    }

    public ZonedDateTime atZone(ZoneId zone) {
        return ZonedDateTime.ofInstant(this, zone);
    }

    public long toEpochMilli() {
        if (seconds < 0 && nanos > 0) {
            long millis = Math.multiplyExact(seconds + 1, 1000);
            long adjustment = nanos / 1000_000 - 1000;
            return Math.addExact(millis, adjustment);
        }
        long millis = Math.multiplyExact(seconds, 1000);
        return Math.addExact(millis, nanos / 1000_000);
    }

    @Override
    public int compareTo(Instant otherInstant) {
        int cmp = Long.compare(seconds, otherInstant.seconds);
        if (cmp != 0) return cmp;
        return nanos - otherInstant.nanos;
    }

    public boolean isAfter(Instant otherInstant) {
        return compareTo(otherInstant) > 0;
    }

    public boolean isBefore(Instant otherInstant) {
        return compareTo(otherInstant) < 0;
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) return true;
        if (!(other instanceof Instant)) return false;
        Instant o = (Instant) other;
        return seconds == o.seconds && nanos == o.nanos;
    }

    @Override
    public int hashCode() {
        return ((int) (seconds ^ (seconds >>> 32))) + 51 * nanos;
    }

    @Override
    public String toString() {
        return DateTimeFormatter.ISO_INSTANT.format(this);
    }
}

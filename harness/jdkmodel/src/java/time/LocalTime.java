/*
 * rocq-jvm model of java.time.LocalTime (clean-room, Apache-2.0): hour/minute/second/nano as in
 * JDK 21, the cached hour instances (identity of of(h, 0) etc.), wrap-around arithmetic, truncation,
 * until, field access and texts, hashCode (Long.hashCode of the nano-of-day) and toString (seconds
 * and 3/6/9 fraction digits only when non-zero). STUCK: now() and now(ZoneId) (host clock: absent; now(Clock) is modelled), atOffset (OffsetTime is not
 * modelled: absent), serialization.
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

public final class LocalTime implements Temporal, TemporalAdjuster, Comparable<LocalTime>, java.io.Serializable {
    private static final long serialVersionUID = 6414437269572265201L;

    public static final LocalTime MIN;
    public static final LocalTime MAX;
    public static final LocalTime MIDNIGHT;
    public static final LocalTime NOON;
    private static final LocalTime[] HOURS = new LocalTime[24];

    static {
        for (int i = 0; i < HOURS.length; i++) HOURS[i] = new LocalTime(i, 0, 0, 0);
        MIDNIGHT = HOURS[0];
        NOON = HOURS[12];
        MIN = HOURS[0];
        MAX = new LocalTime(23, 59, 59, 999_999_999);
    }

    static final int HOURS_PER_DAY = 24;
    static final int MINUTES_PER_HOUR = 60;
    static final int MINUTES_PER_DAY = MINUTES_PER_HOUR * HOURS_PER_DAY;
    static final int SECONDS_PER_MINUTE = 60;
    static final int SECONDS_PER_HOUR = SECONDS_PER_MINUTE * MINUTES_PER_HOUR;
    static final int SECONDS_PER_DAY = SECONDS_PER_HOUR * HOURS_PER_DAY;
    static final long MILLIS_PER_SECOND = 1000L;
    static final long MILLIS_PER_DAY = MILLIS_PER_SECOND * SECONDS_PER_DAY;
    static final long MICROS_PER_SECOND = 1000_000L;
    static final long MICROS_PER_DAY = MICROS_PER_SECOND * SECONDS_PER_DAY;
    static final long NANOS_PER_MILLI = 1000_000L;
    static final long NANOS_PER_SECOND = 1000_000_000L;
    static final long NANOS_PER_MINUTE = NANOS_PER_SECOND * SECONDS_PER_MINUTE;
    static final long NANOS_PER_HOUR = NANOS_PER_MINUTE * MINUTES_PER_HOUR;
    static final long NANOS_PER_DAY = NANOS_PER_HOUR * HOURS_PER_DAY;

    private final byte hour;
    private final byte minute;
    private final byte second;
    private final int nano;

    private LocalTime(int hour, int minute, int second, int nanoOfSecond) {
        this.hour = (byte) hour;
        this.minute = (byte) minute;
        this.second = (byte) second;
        this.nano = nanoOfSecond;
    }

    public static LocalTime now(Clock clock) {
        Objects.requireNonNull(clock, "clock");
        final Instant now = clock.instant();
        return ofInstant(now, clock.getZone());
    }

    public static LocalTime of(int hour, int minute) {
        ChronoField.HOUR_OF_DAY.checkValidValue(hour);
        if (minute == 0) return HOURS[hour];
        ChronoField.MINUTE_OF_HOUR.checkValidValue(minute);
        return new LocalTime(hour, minute, 0, 0);
    }

    public static LocalTime of(int hour, int minute, int second) {
        ChronoField.HOUR_OF_DAY.checkValidValue(hour);
        if ((minute | second) == 0) return HOURS[hour];
        ChronoField.MINUTE_OF_HOUR.checkValidValue(minute);
        ChronoField.SECOND_OF_MINUTE.checkValidValue(second);
        return new LocalTime(hour, minute, second, 0);
    }

    public static LocalTime of(int hour, int minute, int second, int nanoOfSecond) {
        ChronoField.HOUR_OF_DAY.checkValidValue(hour);
        ChronoField.MINUTE_OF_HOUR.checkValidValue(minute);
        ChronoField.SECOND_OF_MINUTE.checkValidValue(second);
        ChronoField.NANO_OF_SECOND.checkValidValue(nanoOfSecond);
        return create(hour, minute, second, nanoOfSecond);
    }

    public static LocalTime ofInstant(Instant instant, ZoneId zone) {
        Objects.requireNonNull(instant, "instant");
        Objects.requireNonNull(zone, "zone");
        ZoneOffset offset = zone.getRules().getOffset(instant);
        long localSecond = instant.getEpochSecond() + offset.getTotalSeconds();
        int secsOfDay = Math.floorMod(localSecond, SECONDS_PER_DAY);
        return ofNanoOfDay(secsOfDay * NANOS_PER_SECOND + instant.getNano());
    }

    public static LocalTime ofSecondOfDay(long secondOfDay) {
        ChronoField.SECOND_OF_DAY.checkValidValue(secondOfDay);
        int hours = (int) (secondOfDay / SECONDS_PER_HOUR);
        secondOfDay -= hours * SECONDS_PER_HOUR;
        int minutes = (int) (secondOfDay / SECONDS_PER_MINUTE);
        secondOfDay -= minutes * SECONDS_PER_MINUTE;
        return create(hours, minutes, (int) secondOfDay, 0);
    }

    public static LocalTime ofNanoOfDay(long nanoOfDay) {
        ChronoField.NANO_OF_DAY.checkValidValue(nanoOfDay);
        int hours = (int) (nanoOfDay / NANOS_PER_HOUR);
        nanoOfDay -= hours * NANOS_PER_HOUR;
        int minutes = (int) (nanoOfDay / NANOS_PER_MINUTE);
        nanoOfDay -= minutes * NANOS_PER_MINUTE;
        int seconds = (int) (nanoOfDay / NANOS_PER_SECOND);
        nanoOfDay -= seconds * NANOS_PER_SECOND;
        return create(hours, minutes, seconds, (int) nanoOfDay);
    }

    public static LocalTime from(TemporalAccessor temporal) {
        Objects.requireNonNull(temporal, "temporal");
        LocalTime time = temporal.query(TemporalQueries.localTime());
        if (time == null)
            throw new DateTimeException("Unable to obtain LocalTime from TemporalAccessor: " + temporal + " of type "
                + temporal.getClass().getName());
        return time;
    }

    public static LocalTime parse(CharSequence text) {
        return parse(text, DateTimeFormatter.ISO_LOCAL_TIME);
    }

    public static LocalTime parse(CharSequence text, DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.parse(text, LocalTime::from);
    }

    private static LocalTime create(int hour, int minute, int second, int nanoOfSecond) {
        if ((minute | second | nanoOfSecond) == 0) return HOURS[hour];
        return new LocalTime(hour, minute, second, nanoOfSecond);
    }

    @Override
    public boolean isSupported(TemporalField field) {
        if (field instanceof ChronoField) return field.isTimeBased();
        return field != null && field.isSupportedBy(this);
    }

    @Override
    public boolean isSupported(TemporalUnit unit) {
        if (unit instanceof ChronoUnit) return unit.isTimeBased();
        return unit != null && unit.isSupportedBy(this);
    }

    @Override
    public ValueRange range(TemporalField field) {
        return Temporal.super.range(field);
    }

    @Override
    public int get(TemporalField field) {
        if (field instanceof ChronoField) return get0(field);
        return Temporal.super.get(field);
    }

    @Override
    public long getLong(TemporalField field) {
        if (field instanceof ChronoField) {
            if (field == ChronoField.NANO_OF_DAY) return toNanoOfDay();
            if (field == ChronoField.MICRO_OF_DAY) return toNanoOfDay() / 1000;
            return get0(field);
        }
        return field.getFrom(this);
    }

    private int get0(TemporalField field) {
        switch ((ChronoField) field) {
            case NANO_OF_SECOND: return nano;
            case NANO_OF_DAY:
                throw new UnsupportedTemporalTypeException("Invalid field 'NanoOfDay' for get() method, use getLong() instead");
            case MICRO_OF_SECOND: return nano / 1000;
            case MICRO_OF_DAY:
                throw new UnsupportedTemporalTypeException("Invalid field 'MicroOfDay' for get() method, use getLong() instead");
            case MILLI_OF_SECOND: return nano / 1000_000;
            case MILLI_OF_DAY: return (int) (toNanoOfDay() / 1000_000);
            case SECOND_OF_MINUTE: return second;
            case SECOND_OF_DAY: return toSecondOfDay();
            case MINUTE_OF_HOUR: return minute;
            case MINUTE_OF_DAY: return hour * 60 + minute;
            case HOUR_OF_AMPM: return hour % 12;
            case CLOCK_HOUR_OF_AMPM: {
                int ham = hour % 12;
                return ham % 12 == 0 ? 12 : ham;
            }
            case HOUR_OF_DAY: return hour;
            case CLOCK_HOUR_OF_DAY: return hour == 0 ? 24 : hour;
            case AMPM_OF_DAY: return hour / 12;
            default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
        }
    }

    public int getHour() {
        return hour;
    }

    public int getMinute() {
        return minute;
    }

    public int getSecond() {
        return second;
    }

    public int getNano() {
        return nano;
    }

    @Override
    public LocalTime with(TemporalAdjuster adjuster) {
        if (adjuster instanceof LocalTime) return (LocalTime) adjuster;
        return (LocalTime) adjuster.adjustInto(this);
    }

    @Override
    public LocalTime with(TemporalField field, long newValue) {
        if (field instanceof ChronoField) {
            ChronoField f = (ChronoField) field;
            f.checkValidValue(newValue);
            switch (f) {
                case NANO_OF_SECOND: return withNano((int) newValue);
                case NANO_OF_DAY: return LocalTime.ofNanoOfDay(newValue);
                case MICRO_OF_SECOND: return withNano((int) newValue * 1000);
                case MICRO_OF_DAY: return LocalTime.ofNanoOfDay(newValue * 1000);
                case MILLI_OF_SECOND: return withNano((int) newValue * 1000_000);
                case MILLI_OF_DAY: return LocalTime.ofNanoOfDay(newValue * 1000_000);
                case SECOND_OF_MINUTE: return withSecond((int) newValue);
                case SECOND_OF_DAY: return plusSeconds(newValue - toSecondOfDay());
                case MINUTE_OF_HOUR: return withMinute((int) newValue);
                case MINUTE_OF_DAY: return plusMinutes(newValue - (hour * 60 + minute));
                case HOUR_OF_AMPM: return plusHours(newValue - (hour % 12));
                case CLOCK_HOUR_OF_AMPM: return plusHours((newValue == 12 ? 0 : newValue) - (hour % 12));
                case HOUR_OF_DAY: return withHour((int) newValue);
                case CLOCK_HOUR_OF_DAY: return withHour((int) (newValue == 24 ? 0 : newValue));
                case AMPM_OF_DAY: return plusHours((newValue - (hour / 12)) * 12);
                default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            }
        }
        return field.adjustInto(this, newValue);
    }

    public LocalTime withHour(int hour) {
        if (this.hour == hour) return this;
        ChronoField.HOUR_OF_DAY.checkValidValue(hour);
        return create(hour, minute, second, nano);
    }

    public LocalTime withMinute(int minute) {
        if (this.minute == minute) return this;
        ChronoField.MINUTE_OF_HOUR.checkValidValue(minute);
        return create(hour, minute, second, nano);
    }

    public LocalTime withSecond(int second) {
        if (this.second == second) return this;
        ChronoField.SECOND_OF_MINUTE.checkValidValue(second);
        return create(hour, minute, second, nano);
    }

    public LocalTime withNano(int nanoOfSecond) {
        if (this.nano == nanoOfSecond) return this;
        ChronoField.NANO_OF_SECOND.checkValidValue(nanoOfSecond);
        return create(hour, minute, second, nanoOfSecond);
    }

    public LocalTime truncatedTo(TemporalUnit unit) {
        if (unit == ChronoUnit.NANOS) return this;
        Duration unitDur = unit.getDuration();
        if (unitDur.getSeconds() > SECONDS_PER_DAY)
            throw new UnsupportedTemporalTypeException("Unit is too large to be used for truncation");
        long dur = unitDur.toNanos();
        if ((NANOS_PER_DAY % dur) != 0)
            throw new UnsupportedTemporalTypeException("Unit must divide into a standard day without remainder");
        long nod = toNanoOfDay();
        return ofNanoOfDay((nod / dur) * dur);
    }

    @Override
    public LocalTime plus(TemporalAmount amountToAdd) {
        return (LocalTime) amountToAdd.addTo(this);
    }

    @Override
    public LocalTime plus(long amountToAdd, TemporalUnit unit) {
        if (unit instanceof ChronoUnit) {
            switch ((ChronoUnit) unit) {
                case NANOS: return plusNanos(amountToAdd);
                case MICROS: return plusNanos((amountToAdd % MICROS_PER_DAY) * 1000);
                case MILLIS: return plusNanos((amountToAdd % MILLIS_PER_DAY) * 1000_000);
                case SECONDS: return plusSeconds(amountToAdd);
                case MINUTES: return plusMinutes(amountToAdd);
                case HOURS: return plusHours(amountToAdd);
                case HALF_DAYS: return plusHours((amountToAdd % 2) * 12);
                default: throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
            }
        }
        return unit.addTo(this, amountToAdd);
    }

    public LocalTime plusHours(long hoursToAdd) {
        if (hoursToAdd == 0) return this;
        int newHour = ((int) (hoursToAdd % HOURS_PER_DAY) + hour + HOURS_PER_DAY) % HOURS_PER_DAY;
        return create(newHour, minute, second, nano);
    }

    public LocalTime plusMinutes(long minutesToAdd) {
        if (minutesToAdd == 0) return this;
        int mofd = hour * MINUTES_PER_HOUR + minute;
        int newMofd = ((int) (minutesToAdd % MINUTES_PER_DAY) + mofd + MINUTES_PER_DAY) % MINUTES_PER_DAY;
        if (mofd == newMofd) return this;
        return create(newMofd / MINUTES_PER_HOUR, newMofd % MINUTES_PER_HOUR, second, nano);
    }

    public LocalTime plusSeconds(long secondsToAdd) {
        if (secondsToAdd == 0) return this;
        int sofd = hour * SECONDS_PER_HOUR + minute * SECONDS_PER_MINUTE + second;
        int newSofd = ((int) (secondsToAdd % SECONDS_PER_DAY) + sofd + SECONDS_PER_DAY) % SECONDS_PER_DAY;
        if (sofd == newSofd) return this;
        return create(newSofd / SECONDS_PER_HOUR, (newSofd / SECONDS_PER_MINUTE) % MINUTES_PER_HOUR,
            newSofd % SECONDS_PER_MINUTE, nano);
    }

    public LocalTime plusNanos(long nanosToAdd) {
        if (nanosToAdd == 0) return this;
        long nofd = toNanoOfDay();
        long newNofd = ((nanosToAdd % NANOS_PER_DAY) + nofd + NANOS_PER_DAY) % NANOS_PER_DAY;
        if (nofd == newNofd) return this;
        return create((int) (newNofd / NANOS_PER_HOUR), (int) ((newNofd / NANOS_PER_MINUTE) % MINUTES_PER_HOUR),
            (int) ((newNofd / NANOS_PER_SECOND) % SECONDS_PER_MINUTE), (int) (newNofd % NANOS_PER_SECOND));
    }

    @Override
    public LocalTime minus(TemporalAmount amountToSubtract) {
        return (LocalTime) amountToSubtract.subtractFrom(this);
    }

    @Override
    public LocalTime minus(long amountToSubtract, TemporalUnit unit) {
        return amountToSubtract == Long.MIN_VALUE ? plus(Long.MAX_VALUE, unit).plus(1, unit) : plus(-amountToSubtract, unit);
    }

    public LocalTime minusHours(long hoursToSubtract) {
        return plusHours(-(hoursToSubtract % HOURS_PER_DAY));
    }

    public LocalTime minusMinutes(long minutesToSubtract) {
        return plusMinutes(-(minutesToSubtract % MINUTES_PER_DAY));
    }

    public LocalTime minusSeconds(long secondsToSubtract) {
        return plusSeconds(-(secondsToSubtract % SECONDS_PER_DAY));
    }

    public LocalTime minusNanos(long nanosToSubtract) {
        return plusNanos(-(nanosToSubtract % NANOS_PER_DAY));
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.chronology() || query == TemporalQueries.zoneId() || query == TemporalQueries.zone()
            || query == TemporalQueries.offset()) return null;
        if (query == TemporalQueries.localTime()) return (R) this;
        if (query == TemporalQueries.localDate()) return null;
        if (query == TemporalQueries.precision()) return (R) ChronoUnit.NANOS;
        return query.queryFrom(this);
    }

    @Override
    public Temporal adjustInto(Temporal temporal) {
        return temporal.with(ChronoField.NANO_OF_DAY, toNanoOfDay());
    }

    @Override
    public long until(Temporal endExclusive, TemporalUnit unit) {
        LocalTime end = LocalTime.from(endExclusive);
        if (unit instanceof ChronoUnit) {
            long nanosUntil = end.toNanoOfDay() - toNanoOfDay();
            switch ((ChronoUnit) unit) {
                case NANOS: return nanosUntil;
                case MICROS: return nanosUntil / 1000;
                case MILLIS: return nanosUntil / 1000_000;
                case SECONDS: return nanosUntil / NANOS_PER_SECOND;
                case MINUTES: return nanosUntil / NANOS_PER_MINUTE;
                case HOURS: return nanosUntil / NANOS_PER_HOUR;
                case HALF_DAYS: return nanosUntil / (12 * NANOS_PER_HOUR);
                default: throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
            }
        }
        return unit.between(this, end);
    }

    public String format(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.format(this);
    }

    public LocalDateTime atDate(LocalDate date) {
        return LocalDateTime.of(date, this);
    }

    public int toSecondOfDay() {
        return hour * SECONDS_PER_HOUR + minute * SECONDS_PER_MINUTE + second;
    }

    public long toNanoOfDay() {
        long total = hour * NANOS_PER_HOUR;
        total += minute * NANOS_PER_MINUTE;
        total += second * NANOS_PER_SECOND;
        total += nano;
        return total;
    }

    public long toEpochSecond(LocalDate date, ZoneOffset offset) {
        Objects.requireNonNull(date, "date");
        Objects.requireNonNull(offset, "offset");
        long secs = date.toEpochDay() * 86400 + toSecondOfDay();
        return secs - offset.getTotalSeconds();
    }

    @Override
    public int compareTo(LocalTime other) {
        int cmp = Integer.compare(hour, other.hour);
        if (cmp == 0) {
            cmp = Integer.compare(minute, other.minute);
            if (cmp == 0) {
                cmp = Integer.compare(second, other.second);
                if (cmp == 0) cmp = Integer.compare(nano, other.nano);
            }
        }
        return cmp;
    }

    public boolean isAfter(LocalTime other) {
        return compareTo(other) > 0;
    }

    public boolean isBefore(LocalTime other) {
        return compareTo(other) < 0;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof LocalTime)) return false;
        LocalTime o = (LocalTime) obj;
        return hour == o.hour && minute == o.minute && second == o.second && nano == o.nano;
    }

    @Override
    public int hashCode() {
        long nod = toNanoOfDay();
        return (int) (nod ^ (nod >>> 32));
    }

    @Override
    public String toString() {
        StringBuilder buf = new StringBuilder(18);
        int h = hour, m = minute, s = second, n = nano;
        buf.append(h < 10 ? "0" : "").append(h).append(m < 10 ? ":0" : ":").append(m);
        if (s > 0 || n > 0) {
            buf.append(s < 10 ? ":0" : ":").append(s);
            if (n > 0) {
                buf.append('.');
                if (n % 1000_000 == 0) {
                    buf.append(Integer.toString((n / 1000_000) + 1000).substring(1));
                } else if (n % 1000 == 0) {
                    buf.append(Integer.toString((n / 1000) + 1000_000).substring(1));
                } else {
                    buf.append(Integer.toString(n + 1000_000_000).substring(1));
                }
            }
        }
        return buf.toString();
    }
}

/*
 * rocq-jvm model of java.time.LocalDateTime (clean-room, Apache-2.0): a LocalDate and a LocalTime as
 * in JDK 21; the JDK's overflow-safe time arithmetic (plusWithOverflow), until (time-based units
 * through days and nano-of-day, date-based units with the end-date adjustment), from(), hashCode and
 * toString. STUCK: now() and now(ZoneId) (host clock: absent; now(Clock) is modelled), serialization.
 */
package java.time;

import java.time.chrono.ChronoLocalDateTime;
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
import java.time.temporal.ValueRange;
import java.util.Objects;

public final class LocalDateTime implements Temporal, TemporalAdjuster, ChronoLocalDateTime<LocalDate>, java.io.Serializable {
    private static final long serialVersionUID = 6207766400415563566L;

    public static final LocalDateTime MIN = LocalDateTime.of(LocalDate.MIN, LocalTime.MIN);
    public static final LocalDateTime MAX = LocalDateTime.of(LocalDate.MAX, LocalTime.MAX);

    private final LocalDate date;
    private final LocalTime time;

    private LocalDateTime(LocalDate date, LocalTime time) {
        this.date = date;
        this.time = time;
    }

    public static LocalDateTime now(Clock clock) {
        Objects.requireNonNull(clock, "clock");
        final Instant now = clock.instant();
        ZoneOffset offset = clock.getZone().getRules().getOffset(now);
        return ofEpochSecond(now.getEpochSecond(), now.getNano(), offset);
    }

    public static LocalDateTime of(int year, Month month, int dayOfMonth, int hour, int minute) {
        LocalDate d = LocalDate.of(year, month, dayOfMonth);
        return new LocalDateTime(d, LocalTime.of(hour, minute));
    }

    public static LocalDateTime of(int year, Month month, int dayOfMonth, int hour, int minute, int second) {
        LocalDate d = LocalDate.of(year, month, dayOfMonth);
        return new LocalDateTime(d, LocalTime.of(hour, minute, second));
    }

    public static LocalDateTime of(int year, Month month, int dayOfMonth, int hour, int minute, int second, int nanoOfSecond) {
        LocalDate d = LocalDate.of(year, month, dayOfMonth);
        return new LocalDateTime(d, LocalTime.of(hour, minute, second, nanoOfSecond));
    }

    public static LocalDateTime of(int year, int month, int dayOfMonth, int hour, int minute) {
        LocalDate d = LocalDate.of(year, month, dayOfMonth);
        return new LocalDateTime(d, LocalTime.of(hour, minute));
    }

    public static LocalDateTime of(int year, int month, int dayOfMonth, int hour, int minute, int second) {
        LocalDate d = LocalDate.of(year, month, dayOfMonth);
        return new LocalDateTime(d, LocalTime.of(hour, minute, second));
    }

    public static LocalDateTime of(int year, int month, int dayOfMonth, int hour, int minute, int second, int nanoOfSecond) {
        LocalDate d = LocalDate.of(year, month, dayOfMonth);
        return new LocalDateTime(d, LocalTime.of(hour, minute, second, nanoOfSecond));
    }

    public static LocalDateTime of(LocalDate date, LocalTime time) {
        Objects.requireNonNull(date, "date");
        Objects.requireNonNull(time, "time");
        return new LocalDateTime(date, time);
    }

    public static LocalDateTime ofInstant(Instant instant, ZoneId zone) {
        Objects.requireNonNull(instant, "instant");
        Objects.requireNonNull(zone, "zone");
        ZoneOffset offset = zone.getRules().getOffset(instant);
        return ofEpochSecond(instant.getEpochSecond(), instant.getNano(), offset);
    }

    public static LocalDateTime ofEpochSecond(long epochSecond, int nanoOfSecond, ZoneOffset offset) {
        Objects.requireNonNull(offset, "offset");
        ChronoField.NANO_OF_SECOND.checkValidValue(nanoOfSecond);
        long localSecond = epochSecond + offset.getTotalSeconds();
        long localEpochDay = Math.floorDiv(localSecond, LocalTime.SECONDS_PER_DAY);
        int secsOfDay = Math.floorMod(localSecond, LocalTime.SECONDS_PER_DAY);
        LocalDate d = LocalDate.ofEpochDay(localEpochDay);
        LocalTime t = LocalTime.ofNanoOfDay(secsOfDay * LocalTime.NANOS_PER_SECOND + nanoOfSecond);
        return new LocalDateTime(d, t);
    }

    public static LocalDateTime from(TemporalAccessor temporal) {
        if (temporal instanceof LocalDateTime) return (LocalDateTime) temporal;
        if (temporal instanceof ZonedDateTime) return ((ZonedDateTime) temporal).toLocalDateTime();
        if (temporal instanceof OffsetDateTime) return ((OffsetDateTime) temporal).toLocalDateTime();
        try {
            LocalDate d = LocalDate.from(temporal);
            LocalTime t = LocalTime.from(temporal);
            return new LocalDateTime(d, t);
        } catch (DateTimeException ex) {
            throw new DateTimeException("Unable to obtain LocalDateTime from TemporalAccessor: " + temporal + " of type "
                + temporal.getClass().getName(), ex);
        }
    }

    public static LocalDateTime parse(CharSequence text) {
        return parse(text, DateTimeFormatter.ISO_LOCAL_DATE_TIME);
    }

    public static LocalDateTime parse(CharSequence text, DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.parse(text, LocalDateTime::from);
    }

    private LocalDateTime with(LocalDate newDate, LocalTime newTime) {
        if (date == newDate && time == newTime) return this;
        return new LocalDateTime(newDate, newTime);
    }

    @Override
    public boolean isSupported(TemporalField field) {
        if (field instanceof ChronoField) {
            ChronoField f = (ChronoField) field;
            return f.isDateBased() || f.isTimeBased();
        }
        return field != null && field.isSupportedBy(this);
    }

    @Override
    public boolean isSupported(TemporalUnit unit) {
        return ChronoLocalDateTime.super.isSupported(unit);
    }

    @Override
    public ValueRange range(TemporalField field) {
        if (field instanceof ChronoField) return ((ChronoField) field).isTimeBased() ? time.range(field) : date.range(field);
        return field.rangeRefinedBy(this);
    }

    @Override
    public int get(TemporalField field) {
        if (field instanceof ChronoField) return ((ChronoField) field).isTimeBased() ? time.get(field) : date.get(field);
        return ChronoLocalDateTime.super.get(field);
    }

    @Override
    public long getLong(TemporalField field) {
        if (field instanceof ChronoField)
            return ((ChronoField) field).isTimeBased() ? time.getLong(field) : date.getLong(field);
        return field.getFrom(this);
    }

    @Override
    public LocalDate toLocalDate() {
        return date;
    }

    public int getYear() {
        return date.getYear();
    }

    public int getMonthValue() {
        return date.getMonthValue();
    }

    public Month getMonth() {
        return date.getMonth();
    }

    public int getDayOfMonth() {
        return date.getDayOfMonth();
    }

    public int getDayOfYear() {
        return date.getDayOfYear();
    }

    public DayOfWeek getDayOfWeek() {
        return date.getDayOfWeek();
    }

    @Override
    public LocalTime toLocalTime() {
        return time;
    }

    public int getHour() {
        return time.getHour();
    }

    public int getMinute() {
        return time.getMinute();
    }

    public int getSecond() {
        return time.getSecond();
    }

    public int getNano() {
        return time.getNano();
    }

    @Override
    public LocalDateTime with(TemporalAdjuster adjuster) {
        if (adjuster instanceof LocalDate) return with((LocalDate) adjuster, time);
        if (adjuster instanceof LocalTime) return with(date, (LocalTime) adjuster);
        if (adjuster instanceof LocalDateTime) return (LocalDateTime) adjuster;
        return (LocalDateTime) adjuster.adjustInto(this);
    }

    @Override
    public LocalDateTime with(TemporalField field, long newValue) {
        if (field instanceof ChronoField) {
            if (((ChronoField) field).isTimeBased()) return with(date, time.with(field, newValue));
            return with(date.with(field, newValue), time);
        }
        return field.adjustInto(this, newValue);
    }

    public LocalDateTime withYear(int year) {
        return with(date.withYear(year), time);
    }

    public LocalDateTime withMonth(int month) {
        return with(date.withMonth(month), time);
    }

    public LocalDateTime withDayOfMonth(int dayOfMonth) {
        return with(date.withDayOfMonth(dayOfMonth), time);
    }

    public LocalDateTime withDayOfYear(int dayOfYear) {
        return with(date.withDayOfYear(dayOfYear), time);
    }

    public LocalDateTime withHour(int hour) {
        return with(date, time.withHour(hour));
    }

    public LocalDateTime withMinute(int minute) {
        return with(date, time.withMinute(minute));
    }

    public LocalDateTime withSecond(int second) {
        return with(date, time.withSecond(second));
    }

    public LocalDateTime withNano(int nanoOfSecond) {
        return with(date, time.withNano(nanoOfSecond));
    }

    public LocalDateTime truncatedTo(TemporalUnit unit) {
        return with(date, time.truncatedTo(unit));
    }

    @Override
    public LocalDateTime plus(TemporalAmount amountToAdd) {
        if (amountToAdd instanceof Period) return with(date.plus((Period) amountToAdd), time);
        Objects.requireNonNull(amountToAdd, "amountToAdd");
        return (LocalDateTime) amountToAdd.addTo(this);
    }

    @Override
    public LocalDateTime plus(long amountToAdd, TemporalUnit unit) {
        if (unit instanceof ChronoUnit) {
            switch ((ChronoUnit) unit) {
                case NANOS: return plusNanos(amountToAdd);
                case MICROS:
                    return plusDays(amountToAdd / LocalTime.MICROS_PER_DAY).plusNanos((amountToAdd % LocalTime.MICROS_PER_DAY) * 1000);
                case MILLIS:
                    return plusDays(amountToAdd / LocalTime.MILLIS_PER_DAY).plusNanos((amountToAdd % LocalTime.MILLIS_PER_DAY) * 1000_000);
                case SECONDS: return plusSeconds(amountToAdd);
                case MINUTES: return plusMinutes(amountToAdd);
                case HOURS: return plusHours(amountToAdd);
                case HALF_DAYS: return plusDays(amountToAdd / 256).plusHours((amountToAdd % 256) * 12);
                default: return with(date.plus(amountToAdd, unit), time);
            }
        }
        return unit.addTo(this, amountToAdd);
    }

    public LocalDateTime plusYears(long years) {
        return with(date.plusYears(years), time);
    }

    public LocalDateTime plusMonths(long months) {
        return with(date.plusMonths(months), time);
    }

    public LocalDateTime plusWeeks(long weeks) {
        return with(date.plusWeeks(weeks), time);
    }

    public LocalDateTime plusDays(long days) {
        return with(date.plusDays(days), time);
    }

    public LocalDateTime plusHours(long hours) {
        return plusWithOverflow(date, hours, 0, 0, 0, 1);
    }

    public LocalDateTime plusMinutes(long minutes) {
        return plusWithOverflow(date, 0, minutes, 0, 0, 1);
    }

    public LocalDateTime plusSeconds(long seconds) {
        return plusWithOverflow(date, 0, 0, seconds, 0, 1);
    }

    public LocalDateTime plusNanos(long nanos) {
        return plusWithOverflow(date, 0, 0, 0, nanos, 1);
    }

    @Override
    public LocalDateTime minus(TemporalAmount amountToSubtract) {
        if (amountToSubtract instanceof Period) return with(date.minus((Period) amountToSubtract), time);
        Objects.requireNonNull(amountToSubtract, "amountToSubtract");
        return (LocalDateTime) amountToSubtract.subtractFrom(this);
    }

    @Override
    public LocalDateTime minus(long amountToSubtract, TemporalUnit unit) {
        return amountToSubtract == Long.MIN_VALUE ? plus(Long.MAX_VALUE, unit).plus(1, unit) : plus(-amountToSubtract, unit);
    }

    public LocalDateTime minusYears(long n) {
        return n == Long.MIN_VALUE ? plusYears(Long.MAX_VALUE).plusYears(1) : plusYears(-n);
    }

    public LocalDateTime minusMonths(long n) {
        return n == Long.MIN_VALUE ? plusMonths(Long.MAX_VALUE).plusMonths(1) : plusMonths(-n);
    }

    public LocalDateTime minusWeeks(long n) {
        return n == Long.MIN_VALUE ? plusWeeks(Long.MAX_VALUE).plusWeeks(1) : plusWeeks(-n);
    }

    public LocalDateTime minusDays(long n) {
        return n == Long.MIN_VALUE ? plusDays(Long.MAX_VALUE).plusDays(1) : plusDays(-n);
    }

    public LocalDateTime minusHours(long hours) {
        return plusWithOverflow(date, hours, 0, 0, 0, -1);
    }

    public LocalDateTime minusMinutes(long minutes) {
        return plusWithOverflow(date, 0, minutes, 0, 0, -1);
    }

    public LocalDateTime minusSeconds(long seconds) {
        return plusWithOverflow(date, 0, 0, seconds, 0, -1);
    }

    public LocalDateTime minusNanos(long nanos) {
        return plusWithOverflow(date, 0, 0, 0, nanos, -1);
    }

    private LocalDateTime plusWithOverflow(LocalDate newDate, long hours, long minutes, long seconds, long nanos, int sign) {
        if ((hours | minutes | seconds | nanos) == 0) return with(newDate, time);
        long totDays = nanos / LocalTime.NANOS_PER_DAY + seconds / LocalTime.SECONDS_PER_DAY
            + minutes / LocalTime.MINUTES_PER_DAY + hours / LocalTime.HOURS_PER_DAY;
        totDays *= sign;
        long totNanos = nanos % LocalTime.NANOS_PER_DAY
            + (seconds % LocalTime.SECONDS_PER_DAY) * LocalTime.NANOS_PER_SECOND
            + (minutes % LocalTime.MINUTES_PER_DAY) * LocalTime.NANOS_PER_MINUTE
            + (hours % LocalTime.HOURS_PER_DAY) * LocalTime.NANOS_PER_HOUR;
        long curNoD = time.toNanoOfDay();
        totNanos = totNanos * sign + curNoD;
        totDays += Math.floorDiv(totNanos, LocalTime.NANOS_PER_DAY);
        long newNoD = Math.floorMod(totNanos, LocalTime.NANOS_PER_DAY);
        LocalTime newTime = newNoD == curNoD ? time : LocalTime.ofNanoOfDay(newNoD);
        return with(newDate.plusDays(totDays), newTime);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.localDate()) return (R) date;
        return ChronoLocalDateTime.super.query(query);
    }

    @Override
    public Temporal adjustInto(Temporal temporal) {
        return ChronoLocalDateTime.super.adjustInto(temporal);
    }

    @Override
    public long until(Temporal endExclusive, TemporalUnit unit) {
        LocalDateTime end = LocalDateTime.from(endExclusive);
        if (unit instanceof ChronoUnit) {
            if (unit.isTimeBased()) {
                long amount = date.daysUntil(end.date);
                if (amount == 0) return time.until(end.time, unit);
                long timePart = end.time.toNanoOfDay() - time.toNanoOfDay();
                if (amount > 0) {
                    amount--;
                    timePart += LocalTime.NANOS_PER_DAY;
                } else {
                    amount++;
                    timePart -= LocalTime.NANOS_PER_DAY;
                }
                switch ((ChronoUnit) unit) {
                    case NANOS:
                        amount = Math.multiplyExact(amount, LocalTime.NANOS_PER_DAY);
                        break;
                    case MICROS:
                        amount = Math.multiplyExact(amount, LocalTime.MICROS_PER_DAY);
                        timePart = timePart / 1000;
                        break;
                    case MILLIS:
                        amount = Math.multiplyExact(amount, LocalTime.MILLIS_PER_DAY);
                        timePart = timePart / 1_000_000;
                        break;
                    case SECONDS:
                        amount = Math.multiplyExact(amount, LocalTime.SECONDS_PER_DAY);
                        timePart = timePart / LocalTime.NANOS_PER_SECOND;
                        break;
                    case MINUTES:
                        amount = Math.multiplyExact(amount, LocalTime.MINUTES_PER_DAY);
                        timePart = timePart / LocalTime.NANOS_PER_MINUTE;
                        break;
                    case HOURS:
                        amount = Math.multiplyExact(amount, LocalTime.HOURS_PER_DAY);
                        timePart = timePart / LocalTime.NANOS_PER_HOUR;
                        break;
                    case HALF_DAYS:
                        amount = Math.multiplyExact(amount, 2);
                        timePart = timePart / (LocalTime.NANOS_PER_HOUR * 12);
                        break;
                    default:
                        break;
                }
                return Math.addExact(amount, timePart);
            }
            LocalDate endDate = end.date;
            if (endDate.isAfter(date) && end.time.isBefore(time)) {
                endDate = endDate.minusDays(1);
            } else if (endDate.isBefore(date) && end.time.isAfter(time)) {
                endDate = endDate.plusDays(1);
            }
            return date.until(endDate, unit);
        }
        return unit.between(this, end);
    }

    @Override
    public String format(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.format(this);
    }

    public OffsetDateTime atOffset(ZoneOffset offset) {
        return OffsetDateTime.of(this, offset);
    }

    @Override
    public ZonedDateTime atZone(ZoneId zone) {
        return ZonedDateTime.of(this, zone);
    }

    @Override
    public int compareTo(ChronoLocalDateTime<?> other) {
        if (other instanceof LocalDateTime) return compareTo0((LocalDateTime) other);
        return ChronoLocalDateTime.super.compareTo(other);
    }

    private int compareTo0(LocalDateTime other) {
        int cmp = date.compareTo0(other.toLocalDate());
        if (cmp == 0) cmp = time.compareTo(other.toLocalTime());
        return cmp;
    }

    @Override
    public boolean isAfter(ChronoLocalDateTime<?> other) {
        if (other instanceof LocalDateTime) return compareTo0((LocalDateTime) other) > 0;
        return ChronoLocalDateTime.super.isAfter(other);
    }

    @Override
    public boolean isBefore(ChronoLocalDateTime<?> other) {
        if (other instanceof LocalDateTime) return compareTo0((LocalDateTime) other) < 0;
        return ChronoLocalDateTime.super.isBefore(other);
    }

    @Override
    public boolean isEqual(ChronoLocalDateTime<?> other) {
        if (other instanceof LocalDateTime) return compareTo0((LocalDateTime) other) == 0;
        return ChronoLocalDateTime.super.isEqual(other);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof LocalDateTime)) return false;
        LocalDateTime o = (LocalDateTime) obj;
        return date.equals(o.date) && time.equals(o.time);
    }

    @Override
    public int hashCode() {
        return date.hashCode() ^ time.hashCode();
    }

    @Override
    public String toString() {
        return date.toString() + 'T' + time.toString();
    }
}

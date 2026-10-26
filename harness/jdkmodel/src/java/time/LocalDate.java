/*
 * rocq-jvm model of java.time.LocalDate (clean-room, Apache-2.0): year + month + day as in JDK 21,
 * with the JDK's epoch-day algorithms (ofEpochDay's 400-year cycles, toEpochDay), validation texts,
 * end-of-month adjustment (resolvePreviousValid), until (days, months by packed proleptic month,
 * Period), datesUntil (over the model LongStream), hashCode formula and toString (years beyond
 * 9999 with '+', negative years padded to 4 digits). parse uses the model ISO_LOCAL_DATE.
 * STUCK: now() and now(ZoneId) (host clock: absent; now(Clock) is modelled), atStartOfDay(ZoneId) of a region zone with
 * transitions (only fixed-offset rules are modelled), serialization.
 */
package java.time;

import java.time.chrono.ChronoLocalDate;
import java.time.chrono.IsoChronology;
import java.time.chrono.IsoEra;
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
import java.util.stream.LongStream;
import java.util.stream.Stream;

public final class LocalDate implements Temporal, TemporalAdjuster, ChronoLocalDate, java.io.Serializable {
    private static final long serialVersionUID = 2942565459149668126L;

    public static final LocalDate MIN = LocalDate.of(Year.MIN_VALUE, 1, 1);
    public static final LocalDate MAX = LocalDate.of(Year.MAX_VALUE, 12, 31);
    public static final LocalDate EPOCH = LocalDate.of(1970, 1, 1);

    private static final int DAYS_PER_CYCLE = 146097;
    static final long DAYS_0000_TO_1970 = (DAYS_PER_CYCLE * 5L) - (30L * 365L + 7L);

    private final int year;
    private final short month;
    private final short day;

    private LocalDate(int year, int month, int dayOfMonth) {
        this.year = year;
        this.month = (short) month;
        this.day = (short) dayOfMonth;
    }

    public static LocalDate now(Clock clock) {
        Objects.requireNonNull(clock, "clock");
        final Instant now = clock.instant();
        return ofInstant(now, clock.getZone());
    }

    public static LocalDate of(int year, Month month, int dayOfMonth) {
        ChronoField.YEAR.checkValidValue(year);
        Objects.requireNonNull(month, "month");
        ChronoField.DAY_OF_MONTH.checkValidValue(dayOfMonth);
        return create(year, month.getValue(), dayOfMonth);
    }

    public static LocalDate of(int year, int month, int dayOfMonth) {
        ChronoField.YEAR.checkValidValue(year);
        ChronoField.MONTH_OF_YEAR.checkValidValue(month);
        ChronoField.DAY_OF_MONTH.checkValidValue(dayOfMonth);
        return create(year, month, dayOfMonth);
    }

    public static LocalDate ofYearDay(int year, int dayOfYear) {
        ChronoField.YEAR.checkValidValue(year);
        ChronoField.DAY_OF_YEAR.checkValidValue(dayOfYear);
        boolean leap = IsoChronology.INSTANCE.isLeapYear(year);
        if (dayOfYear == 366 && !leap)
            throw new DateTimeException("Invalid date 'DayOfYear 366' as '" + year + "' is not a leap year");
        Month moy = Month.of((dayOfYear - 1) / 31 + 1);
        int monthEnd = moy.firstDayOfYear(leap) + moy.length(leap) - 1;
        if (dayOfYear > monthEnd) moy = moy.plus(1);
        int dom = dayOfYear - moy.firstDayOfYear(leap) + 1;
        return new LocalDate(year, moy.getValue(), dom);
    }

    public static LocalDate ofInstant(Instant instant, ZoneId zone) {
        Objects.requireNonNull(instant, "instant");
        Objects.requireNonNull(zone, "zone");
        ZoneOffset offset = zone.getRules().getOffset(instant);
        long localSecond = instant.getEpochSecond() + offset.getTotalSeconds();
        return ofEpochDay(Math.floorDiv(localSecond, LocalTime.SECONDS_PER_DAY));
    }

    public static LocalDate ofEpochDay(long epochDay) {
        ChronoField.EPOCH_DAY.checkValidValue(epochDay);
        long zeroDay = epochDay + DAYS_0000_TO_1970 - 60; // from 0000-03-01: the leap day ends each 4-year cycle
        long adjust = 0;
        if (zeroDay < 0) {
            long adjustCycles = (zeroDay + 1) / DAYS_PER_CYCLE - 1;
            adjust = adjustCycles * 400;
            zeroDay += -adjustCycles * DAYS_PER_CYCLE;
        }
        long yearEst = (400 * zeroDay + 591) / DAYS_PER_CYCLE;
        long doyEst = zeroDay - (365 * yearEst + yearEst / 4 - yearEst / 100 + yearEst / 400);
        if (doyEst < 0) {
            yearEst--;
            doyEst = zeroDay - (365 * yearEst + yearEst / 4 - yearEst / 100 + yearEst / 400);
        }
        yearEst += adjust;
        int marchDoy0 = (int) doyEst;
        int marchMonth0 = (marchDoy0 * 5 + 2) / 153;
        int m = marchMonth0 + 3;
        if (m > 12) m -= 12;
        int dom = marchDoy0 - (marchMonth0 * 306 + 5) / 10 + 1;
        if (marchDoy0 >= 306) yearEst++;
        return new LocalDate((int) yearEst, m, dom);
    }

    public static LocalDate from(TemporalAccessor temporal) {
        Objects.requireNonNull(temporal, "temporal");
        LocalDate date = temporal.query(TemporalQueries.localDate());
        if (date == null)
            throw new DateTimeException("Unable to obtain LocalDate from TemporalAccessor: " + temporal + " of type "
                + temporal.getClass().getName());
        return date;
    }

    public static LocalDate parse(CharSequence text) {
        return parse(text, DateTimeFormatter.ISO_LOCAL_DATE);
    }

    public static LocalDate parse(CharSequence text, DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.parse(text, LocalDate::from);
    }

    static int monthLength(int year, int month) {
        if (month == 2) return IsoChronology.INSTANCE.isLeapYear(year) ? 29 : 28;
        if (month == 4 || month == 6 || month == 9 || month == 11) return 30;
        return 31;
    }

    private static LocalDate create(int year, int month, int dayOfMonth) {
        if (dayOfMonth > 28 && dayOfMonth > monthLength(year, month)) {
            if (dayOfMonth == 29)
                throw new DateTimeException("Invalid date 'February 29' as '" + year + "' is not a leap year");
            throw new DateTimeException("Invalid date '" + Month.of(month).name() + " " + dayOfMonth + "'");
        }
        return new LocalDate(year, month, dayOfMonth);
    }

    private static LocalDate resolvePreviousValid(int year, int month, int day) {
        return new LocalDate(year, month, Math.min(day, monthLength(year, month)));
    }

    @Override
    public boolean isSupported(TemporalField field) {
        return ChronoLocalDate.super.isSupported(field);
    }

    @Override
    public boolean isSupported(TemporalUnit unit) {
        return ChronoLocalDate.super.isSupported(unit);
    }

    @Override
    public ValueRange range(TemporalField field) {
        if (field instanceof ChronoField) {
            ChronoField f = (ChronoField) field;
            if (!f.isDateBased()) throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            switch (f) {
                case DAY_OF_MONTH: return ValueRange.of(1, lengthOfMonth());
                case DAY_OF_YEAR: return ValueRange.of(1, lengthOfYear());
                case ALIGNED_WEEK_OF_MONTH: return ValueRange.of(1, getMonth() == Month.FEBRUARY && !isLeapYear() ? 4 : 5);
                case YEAR_OF_ERA: return getYear() <= 0 ? ValueRange.of(1, Year.MAX_VALUE + 1) : ValueRange.of(1, Year.MAX_VALUE);
                default: return field.range();
            }
        }
        return field.rangeRefinedBy(this);
    }

    @Override
    public int get(TemporalField field) {
        if (field instanceof ChronoField) return get0(field);
        return ChronoLocalDate.super.get(field);
    }

    @Override
    public long getLong(TemporalField field) {
        if (field instanceof ChronoField) {
            if (field == ChronoField.EPOCH_DAY) return toEpochDay();
            if (field == ChronoField.PROLEPTIC_MONTH) return getProlepticMonth();
            return get0(field);
        }
        return field.getFrom(this);
    }

    private int get0(TemporalField field) {
        switch ((ChronoField) field) {
            case DAY_OF_WEEK: return getDayOfWeek().getValue();
            case ALIGNED_DAY_OF_WEEK_IN_MONTH: return ((day - 1) % 7) + 1;
            case ALIGNED_DAY_OF_WEEK_IN_YEAR: return ((getDayOfYear() - 1) % 7) + 1;
            case DAY_OF_MONTH: return day;
            case DAY_OF_YEAR: return getDayOfYear();
            case EPOCH_DAY:
                throw new UnsupportedTemporalTypeException("Invalid field 'EpochDay' for get() method, use getLong() instead");
            case ALIGNED_WEEK_OF_MONTH: return ((day - 1) / 7) + 1;
            case ALIGNED_WEEK_OF_YEAR: return ((getDayOfYear() - 1) / 7) + 1;
            case MONTH_OF_YEAR: return month;
            case PROLEPTIC_MONTH:
                throw new UnsupportedTemporalTypeException("Invalid field 'ProlepticMonth' for get() method, use getLong() instead");
            case YEAR_OF_ERA: return year >= 1 ? year : 1 - year;
            case YEAR: return year;
            case ERA: return year >= 1 ? 1 : 0;
            default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
        }
    }

    private long getProlepticMonth() {
        return year * 12L + month - 1;
    }

    @Override
    public IsoChronology getChronology() {
        return IsoChronology.INSTANCE;
    }

    @Override
    public IsoEra getEra() {
        return getYear() >= 1 ? IsoEra.CE : IsoEra.BCE;
    }

    public int getYear() {
        return year;
    }

    public int getMonthValue() {
        return month;
    }

    public Month getMonth() {
        return Month.of(month);
    }

    public int getDayOfMonth() {
        return day;
    }

    public int getDayOfYear() {
        return getMonth().firstDayOfYear(isLeapYear()) + day - 1;
    }

    public DayOfWeek getDayOfWeek() {
        return DayOfWeek.of(Math.floorMod(toEpochDay() + 3, 7) + 1);
    }

    @Override
    public boolean isLeapYear() {
        return IsoChronology.INSTANCE.isLeapYear(year);
    }

    @Override
    public int lengthOfMonth() {
        return monthLength(year, month);
    }

    @Override
    public int lengthOfYear() {
        return isLeapYear() ? 366 : 365;
    }

    @Override
    public LocalDate with(TemporalAdjuster adjuster) {
        if (adjuster instanceof LocalDate) return (LocalDate) adjuster;
        return (LocalDate) adjuster.adjustInto(this);
    }

    @Override
    public LocalDate with(TemporalField field, long newValue) {
        if (field instanceof ChronoField) {
            ChronoField f = (ChronoField) field;
            f.checkValidValue(newValue);
            switch (f) {
                case DAY_OF_WEEK: return plusDays(newValue - getDayOfWeek().getValue());
                case ALIGNED_DAY_OF_WEEK_IN_MONTH: return plusDays(newValue - getLong(ChronoField.ALIGNED_DAY_OF_WEEK_IN_MONTH));
                case ALIGNED_DAY_OF_WEEK_IN_YEAR: return plusDays(newValue - getLong(ChronoField.ALIGNED_DAY_OF_WEEK_IN_YEAR));
                case DAY_OF_MONTH: return withDayOfMonth((int) newValue);
                case DAY_OF_YEAR: return withDayOfYear((int) newValue);
                case EPOCH_DAY: return LocalDate.ofEpochDay(newValue);
                case ALIGNED_WEEK_OF_MONTH: return plusWeeks(newValue - getLong(ChronoField.ALIGNED_WEEK_OF_MONTH));
                case ALIGNED_WEEK_OF_YEAR: return plusWeeks(newValue - getLong(ChronoField.ALIGNED_WEEK_OF_YEAR));
                case MONTH_OF_YEAR: return withMonth((int) newValue);
                case PROLEPTIC_MONTH: return plusMonths(newValue - getProlepticMonth());
                case YEAR_OF_ERA: return withYear((int) (year >= 1 ? newValue : 1 - newValue));
                case YEAR: return withYear((int) newValue);
                case ERA: return getLong(ChronoField.ERA) == newValue ? this : withYear(1 - year);
                default: throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            }
        }
        return field.adjustInto(this, newValue);
    }

    public LocalDate withYear(int year) {
        if (this.year == year) return this;
        ChronoField.YEAR.checkValidValue(year);
        return resolvePreviousValid(year, month, day);
    }

    public LocalDate withMonth(int month) {
        if (this.month == month) return this;
        ChronoField.MONTH_OF_YEAR.checkValidValue(month);
        return resolvePreviousValid(year, month, day);
    }

    public LocalDate withDayOfMonth(int dayOfMonth) {
        if (this.day == dayOfMonth) return this;
        return of(year, month, dayOfMonth);
    }

    public LocalDate withDayOfYear(int dayOfYear) {
        if (this.getDayOfYear() == dayOfYear) return this;
        return ofYearDay(year, dayOfYear);
    }

    @Override
    public LocalDate plus(TemporalAmount amountToAdd) {
        if (amountToAdd instanceof Period) {
            Period p = (Period) amountToAdd;
            return plusMonths(p.toTotalMonths()).plusDays(p.getDays());
        }
        Objects.requireNonNull(amountToAdd, "amountToAdd");
        return (LocalDate) amountToAdd.addTo(this);
    }

    @Override
    public LocalDate plus(long amountToAdd, TemporalUnit unit) {
        if (unit instanceof ChronoUnit) {
            switch ((ChronoUnit) unit) {
                case DAYS: return plusDays(amountToAdd);
                case WEEKS: return plusWeeks(amountToAdd);
                case MONTHS: return plusMonths(amountToAdd);
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

    public LocalDate plusYears(long yearsToAdd) {
        if (yearsToAdd == 0) return this;
        int newYear = ChronoField.YEAR.checkValidIntValue(year + yearsToAdd);
        return resolvePreviousValid(newYear, month, day);
    }

    public LocalDate plusMonths(long monthsToAdd) {
        if (monthsToAdd == 0) return this;
        long calcMonths = year * 12L + (month - 1) + monthsToAdd;
        int newYear = ChronoField.YEAR.checkValidIntValue(Math.floorDiv(calcMonths, 12));
        int newMonth = Math.floorMod(calcMonths, 12) + 1;
        return resolvePreviousValid(newYear, newMonth, day);
    }

    public LocalDate plusWeeks(long weeksToAdd) {
        return plusDays(Math.multiplyExact(weeksToAdd, 7));
    }

    public LocalDate plusDays(long daysToAdd) {
        if (daysToAdd == 0) return this;
        long dom = day + daysToAdd;
        if (dom > 0) {
            if (dom <= 28) return new LocalDate(year, month, (int) dom);
            if (dom <= 59) {
                long monthLen = lengthOfMonth();
                if (dom <= monthLen) return new LocalDate(year, month, (int) dom);
                if (month < 12) return new LocalDate(year, month + 1, (int) (dom - monthLen));
                ChronoField.YEAR.checkValidValue(year + 1);
                return new LocalDate(year + 1, 1, (int) (dom - monthLen));
            }
        }
        return LocalDate.ofEpochDay(Math.addExact(toEpochDay(), daysToAdd));
    }

    @Override
    public LocalDate minus(TemporalAmount amountToSubtract) {
        if (amountToSubtract instanceof Period) {
            Period p = (Period) amountToSubtract;
            return minusMonths(p.toTotalMonths()).minusDays(p.getDays());
        }
        Objects.requireNonNull(amountToSubtract, "amountToSubtract");
        return (LocalDate) amountToSubtract.subtractFrom(this);
    }

    @Override
    public LocalDate minus(long amountToSubtract, TemporalUnit unit) {
        return amountToSubtract == Long.MIN_VALUE ? plus(Long.MAX_VALUE, unit).plus(1, unit) : plus(-amountToSubtract, unit);
    }

    public LocalDate minusYears(long n) {
        return n == Long.MIN_VALUE ? plusYears(Long.MAX_VALUE).plusYears(1) : plusYears(-n);
    }

    public LocalDate minusMonths(long n) {
        return n == Long.MIN_VALUE ? plusMonths(Long.MAX_VALUE).plusMonths(1) : plusMonths(-n);
    }

    public LocalDate minusWeeks(long n) {
        return n == Long.MIN_VALUE ? plusWeeks(Long.MAX_VALUE).plusWeeks(1) : plusWeeks(-n);
    }

    public LocalDate minusDays(long n) {
        return n == Long.MIN_VALUE ? plusDays(Long.MAX_VALUE).plusDays(1) : plusDays(-n);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.localDate()) return (R) this;
        return ChronoLocalDate.super.query(query);
    }

    @Override
    public Temporal adjustInto(Temporal temporal) {
        return ChronoLocalDate.super.adjustInto(temporal);
    }

    @Override
    public long until(Temporal endExclusive, TemporalUnit unit) {
        LocalDate end = LocalDate.from(endExclusive);
        if (unit instanceof ChronoUnit) {
            switch ((ChronoUnit) unit) {
                case DAYS: return daysUntil(end);
                case WEEKS: return daysUntil(end) / 7;
                case MONTHS: return monthsUntil(end);
                case YEARS: return monthsUntil(end) / 12;
                case DECADES: return monthsUntil(end) / 120;
                case CENTURIES: return monthsUntil(end) / 1200;
                case MILLENNIA: return monthsUntil(end) / 12000;
                case ERAS: return end.getLong(ChronoField.ERA) - getLong(ChronoField.ERA);
                default: throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
            }
        }
        return unit.between(this, end);
    }

    long daysUntil(LocalDate end) {
        return end.toEpochDay() - toEpochDay();
    }

    private long monthsUntil(LocalDate end) {
        long packed1 = getProlepticMonth() * 32L + getDayOfMonth();
        long packed2 = end.getProlepticMonth() * 32L + end.getDayOfMonth();
        return (packed2 - packed1) / 32;
    }

    @Override
    public Period until(ChronoLocalDate endDateExclusive) {
        LocalDate end = LocalDate.from(endDateExclusive);
        long totalMonths = end.getProlepticMonth() - this.getProlepticMonth();
        int days = end.day - this.day;
        if (totalMonths > 0 && days < 0) {
            totalMonths--;
            LocalDate calcDate = this.plusMonths(totalMonths);
            days = (int) (end.toEpochDay() - calcDate.toEpochDay());
        } else if (totalMonths < 0 && days > 0) {
            totalMonths++;
            days -= end.lengthOfMonth();
        }
        long years = totalMonths / 12;
        int months = (int) (totalMonths % 12);
        return Period.of(Math.toIntExact(years), months, days);
    }

    public Stream<LocalDate> datesUntil(LocalDate endExclusive) {
        long end = endExclusive.toEpochDay();
        long start = toEpochDay();
        if (end < start) throw new IllegalArgumentException(endExclusive + " < " + this);
        return LongStream.range(start, end).mapToObj(LocalDate::ofEpochDay);
    }

    public Stream<LocalDate> datesUntil(LocalDate endExclusive, Period step) {
        if (step.isZero()) throw new IllegalArgumentException("step is zero");
        long end = endExclusive.toEpochDay();
        long start = toEpochDay();
        long until = end - start;
        long months = step.toTotalMonths();
        long days = step.getDays();
        if ((months < 0 && days > 0) || (months > 0 && days < 0))
            throw new IllegalArgumentException("period months and days are of opposite sign");
        if (until == 0) return Stream.empty();
        int sign = months > 0 || days > 0 ? 1 : -1;
        if (sign < 0 ^ until < 0) throw new IllegalArgumentException(endExclusive + (sign < 0 ? " > " : " < ") + this);
        if (months == 0) {
            long steps = (until - sign) / days;
            return LongStream.rangeClosed(0, steps).mapToObj(n -> LocalDate.ofEpochDay(start + n * days));
        }
        long steps = until * 1600 / (months * 48699 + days * 1600) + 1;
        long addMonths = months * steps;
        long addDays = days * steps;
        long maxAddMonths = months > 0 ? MAX.getProlepticMonth() - getProlepticMonth()
            : getProlepticMonth() - MIN.getProlepticMonth();
        if (addMonths * sign > maxAddMonths || (plusMonths(addMonths).toEpochDay() + addDays) * sign >= end * sign) {
            steps--;
            addMonths -= months;
            addDays -= days;
            if (addMonths * sign > maxAddMonths || (plusMonths(addMonths).toEpochDay() + addDays) * sign >= end * sign)
                steps--;
        }
        return LongStream.rangeClosed(0, steps).mapToObj(n -> this.plusMonths(months * n).plusDays(days * n));
    }

    @Override
    public String format(DateTimeFormatter formatter) {
        Objects.requireNonNull(formatter, "formatter");
        return formatter.format(this);
    }

    @Override
    public LocalDateTime atTime(LocalTime time) {
        return LocalDateTime.of(this, time);
    }

    public LocalDateTime atTime(int hour, int minute) {
        return atTime(LocalTime.of(hour, minute));
    }

    public LocalDateTime atTime(int hour, int minute, int second) {
        return atTime(LocalTime.of(hour, minute, second));
    }

    public LocalDateTime atTime(int hour, int minute, int second, int nanoOfSecond) {
        return atTime(LocalTime.of(hour, minute, second, nanoOfSecond));
    }

    public LocalDateTime atStartOfDay() {
        return LocalDateTime.of(this, LocalTime.MIDNIGHT);
    }

    public ZonedDateTime atStartOfDay(ZoneId zone) {
        Objects.requireNonNull(zone, "zone");
        LocalDateTime ldt = atTime(LocalTime.MIDNIGHT);
        if (!(zone instanceof ZoneOffset)) zone.getRules(); // fixed-offset rules: no transition
        return ZonedDateTime.of(ldt, zone);
    }

    @Override
    public long toEpochDay() {
        long y = year;
        long m = month;
        long total = 365 * y;
        if (y >= 0) {
            total += (y + 3) / 4 - (y + 99) / 100 + (y + 399) / 400;
        } else {
            total -= y / -4 - y / -100 + y / -400;
        }
        total += (367 * m - 362) / 12;
        total += day - 1;
        if (m > 2) {
            total--;
            if (!isLeapYear()) total--;
        }
        return total - DAYS_0000_TO_1970;
    }

    public long toEpochSecond(LocalTime time, ZoneOffset offset) {
        Objects.requireNonNull(time, "time");
        Objects.requireNonNull(offset, "offset");
        long secs = toEpochDay() * LocalTime.SECONDS_PER_DAY + time.toSecondOfDay();
        return secs - offset.getTotalSeconds();
    }

    @Override
    public int compareTo(ChronoLocalDate other) {
        if (other instanceof LocalDate) return compareTo0((LocalDate) other);
        return ChronoLocalDate.super.compareTo(other);
    }

    int compareTo0(LocalDate o) {
        int cmp = year - o.year;
        if (cmp == 0) {
            cmp = month - o.month;
            if (cmp == 0) cmp = day - o.day;
        }
        return cmp;
    }

    @Override
    public boolean isAfter(ChronoLocalDate other) {
        if (other instanceof LocalDate) return compareTo0((LocalDate) other) > 0;
        return ChronoLocalDate.super.isAfter(other);
    }

    @Override
    public boolean isBefore(ChronoLocalDate other) {
        if (other instanceof LocalDate) return compareTo0((LocalDate) other) < 0;
        return ChronoLocalDate.super.isBefore(other);
    }

    @Override
    public boolean isEqual(ChronoLocalDate other) {
        if (other instanceof LocalDate) return compareTo0((LocalDate) other) == 0;
        return ChronoLocalDate.super.isEqual(other);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj instanceof LocalDate) return compareTo0((LocalDate) obj) == 0;
        return false;
    }

    @Override
    public int hashCode() {
        return (year & 0xFFFFF800) ^ ((year << 11) + (month << 6) + day);
    }

    @Override
    public String toString() {
        int absYear = Math.abs(year);
        StringBuilder buf = new StringBuilder(10);
        if (absYear < 1000) {
            if (year < 0) {
                buf.append(year - 10000).deleteCharAt(1);
            } else {
                buf.append(year + 10000).deleteCharAt(0);
            }
        } else {
            if (year > 9999) buf.append('+');
            buf.append(year);
        }
        buf.append(month < 10 ? "-0" : "-").append(month);
        buf.append(day < 10 ? "-0" : "-").append(day);
        return buf.toString();
    }
}

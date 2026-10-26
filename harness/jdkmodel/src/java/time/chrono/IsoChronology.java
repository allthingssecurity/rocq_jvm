/* rocq-jvm model of java.time.chrono.IsoChronology (clean-room, Apache-2.0): the ISO calendar of
 * JDK 21 (leap-year rule, epochSecond with its checks and texts, the ISO overrides of field
 * resolution). dateNow() and dateNow(ZoneId) (host clock) are STUCK; dateNow(Clock) is modelled. */
package java.time.chrono;

import java.time.DateTimeException;
import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.Month;
import java.time.Period;
import java.time.Year;
import java.time.ZoneId;
import java.time.ZoneOffset;
import java.time.ZonedDateTime;
import java.time.format.ResolverStyle;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalField;
import java.time.temporal.ValueRange;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public final class IsoChronology extends AbstractChronology implements java.io.Serializable {
    private static final long serialVersionUID = -1440403870442975015L;
    public static final IsoChronology INSTANCE = new IsoChronology();
    private static final long DAYS_0000_TO_1970 = (146097 * 5L) - (30L * 365L + 7L);

    private IsoChronology() {
    }

    @Override
    public String getId() {
        return "ISO";
    }

    @Override
    public String getCalendarType() {
        return "iso8601";
    }

    @Override
    public LocalDate date(Era era, int yearOfEra, int month, int dayOfMonth) {
        return date(prolepticYear(era, yearOfEra), month, dayOfMonth);
    }

    @Override
    public LocalDate date(int prolepticYear, int month, int dayOfMonth) {
        return LocalDate.of(prolepticYear, month, dayOfMonth);
    }

    @Override
    public LocalDate dateYearDay(Era era, int yearOfEra, int dayOfYear) {
        return dateYearDay(prolepticYear(era, yearOfEra), dayOfYear);
    }

    @Override
    public LocalDate dateYearDay(int prolepticYear, int dayOfYear) {
        return LocalDate.ofYearDay(prolepticYear, dayOfYear);
    }

    @Override
    public LocalDate dateEpochDay(long epochDay) {
        return LocalDate.ofEpochDay(epochDay);
    }

    @Override
    public LocalDate date(TemporalAccessor temporal) {
        return LocalDate.from(temporal);
    }

    @Override
    public long epochSecond(int prolepticYear, int month, int dayOfMonth, int hour, int minute, int second,
                            ZoneOffset zoneOffset) {
        ChronoField.YEAR.checkValidValue(prolepticYear);
        ChronoField.MONTH_OF_YEAR.checkValidValue(month);
        ChronoField.DAY_OF_MONTH.checkValidValue(dayOfMonth);
        ChronoField.HOUR_OF_DAY.checkValidValue(hour);
        ChronoField.MINUTE_OF_HOUR.checkValidValue(minute);
        ChronoField.SECOND_OF_MINUTE.checkValidValue(second);
        Objects.requireNonNull(zoneOffset, "zoneOffset");
        if (dayOfMonth > 28) {
            int dom = month == 2 ? (isLeapYear(prolepticYear) ? 29 : 28)
                : (month == 4 || month == 6 || month == 9 || month == 11) ? 30 : 31;
            if (dayOfMonth > dom) {
                if (dayOfMonth == 29)
                    throw new DateTimeException("Invalid date 'February 29' as '" + prolepticYear + "' is not a leap year");
                throw new DateTimeException("Invalid date '" + Month.of(month).name() + " " + dayOfMonth + "'");
            }
        }
        long y = prolepticYear;
        long days = 365L * y;
        if (y >= 0) {
            days += (y + 3L) / 4 - (y + 99L) / 100 + (y + 399L) / 400;
        } else {
            days -= y / -4 - y / -100 + y / -400;
        }
        days += (367 * month - 362) / 12;
        days += dayOfMonth - 1;
        if (month > 2) {
            days--;
            if (!isLeapYear(prolepticYear)) days--;
        }
        days -= DAYS_0000_TO_1970;
        int timeinSec = (hour * 60 + minute) * 60 + second;
        return Math.addExact(Math.multiplyExact(days, 86400L), timeinSec - zoneOffset.getTotalSeconds());
    }

    @Override
    public LocalDateTime localDateTime(TemporalAccessor temporal) {
        return LocalDateTime.from(temporal);
    }

    @Override
    public ZonedDateTime zonedDateTime(TemporalAccessor temporal) {
        return ZonedDateTime.from(temporal);
    }

    @Override
    public ZonedDateTime zonedDateTime(Instant instant, ZoneId zone) {
        return ZonedDateTime.ofInstant(instant, zone);
    }

    @Override
    public LocalDate dateNow() {
        throw ModelStuckChrono.unsupported("IsoChronology.dateNow: host clock");
    }

    @Override
    public LocalDate dateNow(ZoneId zone) {
        throw ModelStuckChrono.unsupported("IsoChronology.dateNow: host clock");
    }

    @Override
    public LocalDate dateNow(java.time.Clock clock) {
        Objects.requireNonNull(clock, "clock");
        return date(LocalDate.now(clock));
    }

    @Override
    public boolean isLeapYear(long prolepticYear) {
        return ((prolepticYear & 3) == 0) && ((prolepticYear % 100) != 0 || (prolepticYear % 400) == 0);
    }

    @Override
    public int prolepticYear(Era era, int yearOfEra) {
        if (!(era instanceof IsoEra)) throw new ClassCastException("Era must be IsoEra");
        return era == IsoEra.CE ? yearOfEra : 1 - yearOfEra;
    }

    @Override
    public IsoEra eraOf(int eraValue) {
        return IsoEra.of(eraValue);
    }

    @Override
    public List<Era> eras() {
        return List.of(IsoEra.values());
    }

    @Override
    public LocalDate resolveDate(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        return (LocalDate) super.resolveDate(fieldValues, resolverStyle);
    }

    @Override
    void resolveProlepticMonth(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        Long pMonth = fieldValues.remove(ChronoField.PROLEPTIC_MONTH);
        if (pMonth != null) {
            if (resolverStyle != ResolverStyle.LENIENT) ChronoField.PROLEPTIC_MONTH.checkValidValue(pMonth);
            addFieldValue(fieldValues, ChronoField.MONTH_OF_YEAR, Math.floorMod(pMonth, 12) + 1);
            addFieldValue(fieldValues, ChronoField.YEAR, Math.floorDiv(pMonth, 12));
        }
    }

    @Override
    LocalDate resolveYearOfEra(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        Long yoeLong = fieldValues.remove(ChronoField.YEAR_OF_ERA);
        if (yoeLong != null) {
            if (resolverStyle != ResolverStyle.LENIENT) ChronoField.YEAR_OF_ERA.checkValidValue(yoeLong);
            Long era = fieldValues.remove(ChronoField.ERA);
            if (era == null) {
                Long year = fieldValues.get(ChronoField.YEAR);
                if (resolverStyle == ResolverStyle.STRICT) {
                    if (year != null) {
                        addFieldValue(fieldValues, ChronoField.YEAR, year > 0 ? yoeLong : Math.subtractExact(1, yoeLong));
                    } else {
                        fieldValues.put(ChronoField.YEAR_OF_ERA, yoeLong);
                    }
                } else {
                    addFieldValue(fieldValues, ChronoField.YEAR,
                        (year == null || year > 0) ? yoeLong : Math.subtractExact(1, yoeLong));
                }
            } else if (era.longValue() == 1L) {
                addFieldValue(fieldValues, ChronoField.YEAR, yoeLong);
            } else if (era.longValue() == 0L) {
                addFieldValue(fieldValues, ChronoField.YEAR, Math.subtractExact(1, yoeLong));
            } else {
                throw new DateTimeException("Invalid value for era: " + era);
            }
        } else if (fieldValues.containsKey(ChronoField.ERA)) {
            ChronoField.ERA.checkValidValue(fieldValues.get(ChronoField.ERA));
        }
        return null;
    }

    @Override
    LocalDate resolveYMD(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        int y = ChronoField.YEAR.checkValidIntValue(fieldValues.remove(ChronoField.YEAR));
        if (resolverStyle == ResolverStyle.LENIENT) {
            long months = Math.subtractExact(fieldValues.remove(ChronoField.MONTH_OF_YEAR), 1);
            long days = Math.subtractExact(fieldValues.remove(ChronoField.DAY_OF_MONTH), 1);
            return LocalDate.of(y, 1, 1).plusMonths(months).plusDays(days);
        }
        int moy = ChronoField.MONTH_OF_YEAR.checkValidIntValue(fieldValues.remove(ChronoField.MONTH_OF_YEAR));
        int dom = ChronoField.DAY_OF_MONTH.checkValidIntValue(fieldValues.remove(ChronoField.DAY_OF_MONTH));
        if (resolverStyle == ResolverStyle.SMART) {
            if (moy == 4 || moy == 6 || moy == 9 || moy == 11) {
                dom = Math.min(dom, 30);
            } else if (moy == 2) {
                dom = Math.min(dom, Month.FEBRUARY.length(Year.isLeap(y)));
            }
        }
        return LocalDate.of(y, moy, dom);
    }

    @Override
    public ValueRange range(ChronoField field) {
        return field.range();
    }

    @Override
    public Period period(int years, int months, int days) {
        return Period.of(years, months, days);
    }

    @Override
    public boolean isIsoBased() {
        return true;
    }
}

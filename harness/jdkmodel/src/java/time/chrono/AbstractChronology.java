/* rocq-jvm model of java.time.chrono.AbstractChronology (clean-room, Apache-2.0): JDK 21's field
 * resolution (resolveDate and its steps, "Conflict found" / strict-mode texts), compareTo, equals,
 * toString, hashCode (the class's identity hash code, TRUST.md 5c). The chronology registry
 * (ServiceLoader) is not modelled; resolveProlepticMonth of a non-ISO chronology needs dateNow: STUCK. */
package java.time.chrono;

import java.time.DateTimeException;
import java.time.DayOfWeek;
import java.time.format.ResolverStyle;
import java.time.temporal.ChronoField;
import java.time.temporal.ChronoUnit;
import java.time.temporal.TemporalAdjusters;
import java.time.temporal.TemporalField;
import java.time.temporal.ValueRange;
import java.util.List;
import java.util.Map;

public abstract class AbstractChronology implements Chronology {
    protected AbstractChronology() {
    }

    @Override
    public ChronoLocalDate resolveDate(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        if (fieldValues.containsKey(ChronoField.EPOCH_DAY)) return dateEpochDay(fieldValues.remove(ChronoField.EPOCH_DAY));
        resolveProlepticMonth(fieldValues, resolverStyle);
        ChronoLocalDate resolved = resolveYearOfEra(fieldValues, resolverStyle);
        if (resolved != null) return resolved;
        if (fieldValues.containsKey(ChronoField.YEAR)) {
            if (fieldValues.containsKey(ChronoField.MONTH_OF_YEAR)) {
                if (fieldValues.containsKey(ChronoField.DAY_OF_MONTH)) return resolveYMD(fieldValues, resolverStyle);
                if (fieldValues.containsKey(ChronoField.ALIGNED_WEEK_OF_MONTH)) {
                    if (fieldValues.containsKey(ChronoField.ALIGNED_DAY_OF_WEEK_IN_MONTH))
                        return resolveYMAA(fieldValues, resolverStyle);
                    if (fieldValues.containsKey(ChronoField.DAY_OF_WEEK)) return resolveYMAD(fieldValues, resolverStyle);
                }
            }
            if (fieldValues.containsKey(ChronoField.DAY_OF_YEAR)) return resolveYD(fieldValues, resolverStyle);
            if (fieldValues.containsKey(ChronoField.ALIGNED_WEEK_OF_YEAR)) {
                if (fieldValues.containsKey(ChronoField.ALIGNED_DAY_OF_WEEK_IN_YEAR))
                    return resolveYAA(fieldValues, resolverStyle);
                if (fieldValues.containsKey(ChronoField.DAY_OF_WEEK)) return resolveYAD(fieldValues, resolverStyle);
            }
        }
        return null;
    }

    void resolveProlepticMonth(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        if (fieldValues.containsKey(ChronoField.PROLEPTIC_MONTH))
            throw ModelStuckChrono.unsupported("AbstractChronology.resolveProlepticMonth: dateNow");
    }

    ChronoLocalDate resolveYearOfEra(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        Long yoeLong = fieldValues.remove(ChronoField.YEAR_OF_ERA);
        if (yoeLong != null) {
            Long eraLong = fieldValues.remove(ChronoField.ERA);
            int yoe;
            if (resolverStyle != ResolverStyle.LENIENT) {
                yoe = range(ChronoField.YEAR_OF_ERA).checkValidIntValue(yoeLong, ChronoField.YEAR_OF_ERA);
            } else {
                yoe = Math.toIntExact(yoeLong);
            }
            if (eraLong != null) {
                Era eraObj = eraOf(range(ChronoField.ERA).checkValidIntValue(eraLong, ChronoField.ERA));
                addFieldValue(fieldValues, ChronoField.YEAR, prolepticYear(eraObj, yoe));
            } else if (fieldValues.containsKey(ChronoField.YEAR)) {
                int year = range(ChronoField.YEAR).checkValidIntValue(fieldValues.get(ChronoField.YEAR), ChronoField.YEAR);
                ChronoLocalDate chronoDate = dateYearDay(year, 1);
                addFieldValue(fieldValues, ChronoField.YEAR, prolepticYear(chronoDate.getEra(), yoe));
            } else if (resolverStyle == ResolverStyle.STRICT) {
                fieldValues.put(ChronoField.YEAR_OF_ERA, yoeLong);
            } else {
                List<Era> eras = eras();
                if (eras.isEmpty()) {
                    addFieldValue(fieldValues, ChronoField.YEAR, yoe);
                } else {
                    Era eraObj = eras.get(eras.size() - 1);
                    addFieldValue(fieldValues, ChronoField.YEAR, prolepticYear(eraObj, yoe));
                }
            }
        } else if (fieldValues.containsKey(ChronoField.ERA)) {
            range(ChronoField.ERA).checkValidValue(fieldValues.get(ChronoField.ERA), ChronoField.ERA);
        }
        return null;
    }

    ChronoLocalDate resolveYMD(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        int y = range(ChronoField.YEAR).checkValidIntValue(fieldValues.remove(ChronoField.YEAR), ChronoField.YEAR);
        if (resolverStyle == ResolverStyle.LENIENT) {
            long months = Math.subtractExact(fieldValues.remove(ChronoField.MONTH_OF_YEAR), 1);
            long days = Math.subtractExact(fieldValues.remove(ChronoField.DAY_OF_MONTH), 1);
            return date(y, 1, 1).plus(months, ChronoUnit.MONTHS).plus(days, ChronoUnit.DAYS);
        }
        int moy = range(ChronoField.MONTH_OF_YEAR).checkValidIntValue(fieldValues.remove(ChronoField.MONTH_OF_YEAR),
            ChronoField.MONTH_OF_YEAR);
        ValueRange domRange = range(ChronoField.DAY_OF_MONTH);
        int dom = domRange.checkValidIntValue(fieldValues.remove(ChronoField.DAY_OF_MONTH), ChronoField.DAY_OF_MONTH);
        if (resolverStyle == ResolverStyle.SMART) {
            try {
                return date(y, moy, dom);
            } catch (DateTimeException ex) {
                return date(y, moy, 1).with(TemporalAdjusters.lastDayOfMonth());
            }
        }
        return date(y, moy, dom);
    }

    ChronoLocalDate resolveYD(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        int y = range(ChronoField.YEAR).checkValidIntValue(fieldValues.remove(ChronoField.YEAR), ChronoField.YEAR);
        if (resolverStyle == ResolverStyle.LENIENT) {
            long days = Math.subtractExact(fieldValues.remove(ChronoField.DAY_OF_YEAR), 1);
            return dateYearDay(y, 1).plus(days, ChronoUnit.DAYS);
        }
        int doy = range(ChronoField.DAY_OF_YEAR).checkValidIntValue(fieldValues.remove(ChronoField.DAY_OF_YEAR),
            ChronoField.DAY_OF_YEAR);
        return dateYearDay(y, doy);
    }

    ChronoLocalDate resolveYMAA(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        int y = range(ChronoField.YEAR).checkValidIntValue(fieldValues.remove(ChronoField.YEAR), ChronoField.YEAR);
        if (resolverStyle == ResolverStyle.LENIENT) {
            long months = Math.subtractExact(fieldValues.remove(ChronoField.MONTH_OF_YEAR), 1);
            long weeks = Math.subtractExact(fieldValues.remove(ChronoField.ALIGNED_WEEK_OF_MONTH), 1);
            long days = Math.subtractExact(fieldValues.remove(ChronoField.ALIGNED_DAY_OF_WEEK_IN_MONTH), 1);
            return date(y, 1, 1).plus(months, ChronoUnit.MONTHS).plus(weeks, ChronoUnit.WEEKS).plus(days, ChronoUnit.DAYS);
        }
        int moy = range(ChronoField.MONTH_OF_YEAR).checkValidIntValue(fieldValues.remove(ChronoField.MONTH_OF_YEAR),
            ChronoField.MONTH_OF_YEAR);
        int aw = range(ChronoField.ALIGNED_WEEK_OF_MONTH).checkValidIntValue(
            fieldValues.remove(ChronoField.ALIGNED_WEEK_OF_MONTH), ChronoField.ALIGNED_WEEK_OF_MONTH);
        int ad = range(ChronoField.ALIGNED_DAY_OF_WEEK_IN_MONTH).checkValidIntValue(
            fieldValues.remove(ChronoField.ALIGNED_DAY_OF_WEEK_IN_MONTH), ChronoField.ALIGNED_DAY_OF_WEEK_IN_MONTH);
        ChronoLocalDate date = date(y, moy, 1).plus((aw - 1) * 7 + (ad - 1), ChronoUnit.DAYS);
        if (resolverStyle == ResolverStyle.STRICT && date.get(ChronoField.MONTH_OF_YEAR) != moy)
            throw new DateTimeException("Strict mode rejected resolved date as it is in a different month");
        return date;
    }

    ChronoLocalDate resolveYMAD(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        int y = range(ChronoField.YEAR).checkValidIntValue(fieldValues.remove(ChronoField.YEAR), ChronoField.YEAR);
        if (resolverStyle == ResolverStyle.LENIENT) {
            long months = Math.subtractExact(fieldValues.remove(ChronoField.MONTH_OF_YEAR), 1);
            long weeks = Math.subtractExact(fieldValues.remove(ChronoField.ALIGNED_WEEK_OF_MONTH), 1);
            long dow = Math.subtractExact(fieldValues.remove(ChronoField.DAY_OF_WEEK), 1);
            return resolveAligned(date(y, 1, 1), months, weeks, dow);
        }
        int moy = range(ChronoField.MONTH_OF_YEAR).checkValidIntValue(fieldValues.remove(ChronoField.MONTH_OF_YEAR),
            ChronoField.MONTH_OF_YEAR);
        int aw = range(ChronoField.ALIGNED_WEEK_OF_MONTH).checkValidIntValue(
            fieldValues.remove(ChronoField.ALIGNED_WEEK_OF_MONTH), ChronoField.ALIGNED_WEEK_OF_MONTH);
        int dow = range(ChronoField.DAY_OF_WEEK).checkValidIntValue(fieldValues.remove(ChronoField.DAY_OF_WEEK),
            ChronoField.DAY_OF_WEEK);
        ChronoLocalDate date = date(y, moy, 1).plus((aw - 1) * 7, ChronoUnit.DAYS)
            .with(TemporalAdjusters.nextOrSame(DayOfWeek.of(dow)));
        if (resolverStyle == ResolverStyle.STRICT && date.get(ChronoField.MONTH_OF_YEAR) != moy)
            throw new DateTimeException("Strict mode rejected resolved date as it is in a different month");
        return date;
    }

    ChronoLocalDate resolveYAA(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        int y = range(ChronoField.YEAR).checkValidIntValue(fieldValues.remove(ChronoField.YEAR), ChronoField.YEAR);
        if (resolverStyle == ResolverStyle.LENIENT) {
            long weeks = Math.subtractExact(fieldValues.remove(ChronoField.ALIGNED_WEEK_OF_YEAR), 1);
            long days = Math.subtractExact(fieldValues.remove(ChronoField.ALIGNED_DAY_OF_WEEK_IN_YEAR), 1);
            return dateYearDay(y, 1).plus(weeks, ChronoUnit.WEEKS).plus(days, ChronoUnit.DAYS);
        }
        int aw = range(ChronoField.ALIGNED_WEEK_OF_YEAR).checkValidIntValue(
            fieldValues.remove(ChronoField.ALIGNED_WEEK_OF_YEAR), ChronoField.ALIGNED_WEEK_OF_YEAR);
        int ad = range(ChronoField.ALIGNED_DAY_OF_WEEK_IN_YEAR).checkValidIntValue(
            fieldValues.remove(ChronoField.ALIGNED_DAY_OF_WEEK_IN_YEAR), ChronoField.ALIGNED_DAY_OF_WEEK_IN_YEAR);
        ChronoLocalDate date = dateYearDay(y, 1).plus((aw - 1) * 7 + (ad - 1), ChronoUnit.DAYS);
        if (resolverStyle == ResolverStyle.STRICT && date.get(ChronoField.YEAR) != y)
            throw new DateTimeException("Strict mode rejected resolved date as it is in a different year");
        return date;
    }

    ChronoLocalDate resolveYAD(Map<TemporalField, Long> fieldValues, ResolverStyle resolverStyle) {
        int y = range(ChronoField.YEAR).checkValidIntValue(fieldValues.remove(ChronoField.YEAR), ChronoField.YEAR);
        if (resolverStyle == ResolverStyle.LENIENT) {
            long weeks = Math.subtractExact(fieldValues.remove(ChronoField.ALIGNED_WEEK_OF_YEAR), 1);
            long dow = Math.subtractExact(fieldValues.remove(ChronoField.DAY_OF_WEEK), 1);
            return resolveAligned(dateYearDay(y, 1), 0, weeks, dow);
        }
        int aw = range(ChronoField.ALIGNED_WEEK_OF_YEAR).checkValidIntValue(
            fieldValues.remove(ChronoField.ALIGNED_WEEK_OF_YEAR), ChronoField.ALIGNED_WEEK_OF_YEAR);
        int dow = range(ChronoField.DAY_OF_WEEK).checkValidIntValue(fieldValues.remove(ChronoField.DAY_OF_WEEK),
            ChronoField.DAY_OF_WEEK);
        ChronoLocalDate date = dateYearDay(y, 1).plus((aw - 1) * 7, ChronoUnit.DAYS)
            .with(TemporalAdjusters.nextOrSame(DayOfWeek.of(dow)));
        if (resolverStyle == ResolverStyle.STRICT && date.get(ChronoField.YEAR) != y)
            throw new DateTimeException("Strict mode rejected resolved date as it is in a different year");
        return date;
    }

    ChronoLocalDate resolveAligned(ChronoLocalDate base, long months, long weeks, long dow) {
        ChronoLocalDate date = base.plus(months, ChronoUnit.MONTHS).plus(weeks, ChronoUnit.WEEKS);
        if (dow > 7) {
            date = date.plus((dow - 1) / 7, ChronoUnit.WEEKS);
            dow = ((dow - 1) % 7) + 1;
        } else if (dow < 1) {
            date = date.plus(Math.subtractExact(dow, 7) / 7, ChronoUnit.WEEKS);
            dow = ((dow + 6) % 7) + 1;
        }
        return date.with(TemporalAdjusters.nextOrSame(DayOfWeek.of((int) dow)));
    }

    void addFieldValue(Map<TemporalField, Long> fieldValues, ChronoField field, long value) {
        Long old = fieldValues.get(field);
        if (old != null && old.longValue() != value)
            throw new DateTimeException("Conflict found: " + field + " " + old + " differs from " + field + " " + value);
        fieldValues.put(field, value);
    }

    @Override
    public int compareTo(Chronology other) {
        return getId().compareTo(other.getId());
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj instanceof AbstractChronology) return compareTo((AbstractChronology) obj) == 0;
        return false;
    }

    @Override
    public int hashCode() {
        return getClass().hashCode() ^ getId().hashCode();
    }

    @Override
    public String toString() {
        return getId();
    }
}

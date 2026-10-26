/*
 * rocq-jvm model of java.time.format.Parsed (clean-room, Apache-2.0): JDK 21's resolution of parsed
 * fields (resolveFields with TemporalField.resolve, instant fields, the chronology's resolveDate, the
 * time fields in every resolver style, lenient time, cross checks, excess days, fractions, the
 * instant), with every "Conflict found" text. The field map is a HashMap as in the JDK, so iteration
 * orders (toString with several fields, which of several conflicts is reported) follow the identity
 * hash codes of the ChronoField constants (TRUST.md 5c). Day periods ('B') and zone names are not
 * modelled (their parsers are STUCK), so they never reach this class.
 */
package java.time.format;

import java.time.DateTimeException;
import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalTime;
import java.time.Period;
import java.time.ZoneId;
import java.time.ZoneOffset;
import java.time.chrono.ChronoLocalDate;
import java.time.chrono.ChronoLocalDateTime;
import java.time.chrono.ChronoZonedDateTime;
import java.time.chrono.Chronology;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalField;
import java.time.temporal.TemporalQueries;
import java.time.temporal.TemporalQuery;
import java.time.temporal.UnsupportedTemporalTypeException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

final class Parsed implements TemporalAccessor {
    final Map<TemporalField, Long> fieldValues = new HashMap<>();
    ZoneId zone;
    int zoneNameType = -1;
    Chronology chrono;
    boolean leapSecond;
    private ResolverStyle resolverStyle;
    private ChronoLocalDate date;
    private LocalTime time;
    Period excessDays = Period.ZERO;

    Parsed() {
    }

    Parsed copy() {
        Parsed c = new Parsed();
        c.fieldValues.putAll(this.fieldValues);
        c.zone = this.zone;
        c.zoneNameType = this.zoneNameType;
        c.chrono = this.chrono;
        c.leapSecond = this.leapSecond;
        return c;
    }

    @Override
    public boolean isSupported(TemporalField field) {
        if (fieldValues.containsKey(field) || (date != null && date.isSupported(field))
            || (time != null && time.isSupported(field))) return true;
        return field != null && !(field instanceof ChronoField) && field.isSupportedBy(this);
    }

    @Override
    public long getLong(TemporalField field) {
        Objects.requireNonNull(field, "field");
        Long value = fieldValues.get(field);
        if (value != null) return value;
        if (date != null && date.isSupported(field)) return date.getLong(field);
        if (time != null && time.isSupported(field)) return time.getLong(field);
        if (field instanceof ChronoField) throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
        return field.getFrom(this);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.zoneId()) return (R) zone;
        if (query == TemporalQueries.chronology()) return (R) chrono;
        if (query == TemporalQueries.localDate()) return (R) (date != null ? LocalDate.from(date) : null);
        if (query == TemporalQueries.localTime()) return (R) time;
        if (query == TemporalQueries.offset()) {
            Long offsetSecs = fieldValues.get(ChronoField.OFFSET_SECONDS);
            if (offsetSecs != null) return (R) ZoneOffset.ofTotalSeconds(offsetSecs.intValue());
            if (zone instanceof ZoneOffset) return (R) zone;
            return query.queryFrom(this);
        }
        if (query == TemporalQueries.zone()) return query.queryFrom(this);
        if (query == TemporalQueries.precision()) return null;
        return query.queryFrom(this);
    }

    TemporalAccessor resolve(ResolverStyle resolverStyle, Set<TemporalField> resolverFields) {
        if (resolverFields != null) fieldValues.keySet().retainAll(resolverFields);
        this.resolverStyle = resolverStyle;
        resolveFields();
        resolveTimeLenient();
        crossCheck();
        resolvePeriod();
        resolveFractional();
        resolveInstant();
        return this;
    }

    private void resolveFields() {
        resolveInstantFields();
        resolveDateFields();
        resolveTimeFields();
        if (fieldValues.size() > 0) {
            int changedCount = 0;
            outer:
            while (changedCount < 50) {
                for (Map.Entry<TemporalField, Long> entry : fieldValues.entrySet()) {
                    TemporalField targetField = entry.getKey();
                    TemporalAccessor resolvedObject = targetField.resolve(fieldValues, this, resolverStyle);
                    if (resolvedObject != null) {
                        if (resolvedObject instanceof ChronoZonedDateTime) {
                            ChronoZonedDateTime<?> czdt = (ChronoZonedDateTime<?>) resolvedObject;
                            if (zone == null) {
                                zone = czdt.getZone();
                            } else if (!zone.equals(czdt.getZone())) {
                                throw new DateTimeException("ChronoZonedDateTime must use the effective parsed zone: " + zone);
                            }
                            resolvedObject = czdt.toLocalDateTime();
                        }
                        if (resolvedObject instanceof ChronoLocalDateTime) {
                            ChronoLocalDateTime<?> cldt = (ChronoLocalDateTime<?>) resolvedObject;
                            updateCheckConflict(cldt.toLocalTime(), Period.ZERO);
                            updateCheckConflict(cldt.toLocalDate());
                            changedCount++;
                            continue outer;
                        }
                        if (resolvedObject instanceof ChronoLocalDate) {
                            updateCheckConflict((ChronoLocalDate) resolvedObject);
                            changedCount++;
                            continue outer;
                        }
                        if (resolvedObject instanceof LocalTime) {
                            updateCheckConflict((LocalTime) resolvedObject, Period.ZERO);
                            changedCount++;
                            continue outer;
                        }
                        throw new DateTimeException("Method resolve() can only return ChronoZonedDateTime, "
                            + "ChronoLocalDateTime, ChronoLocalDate or LocalTime");
                    } else if (!fieldValues.containsKey(targetField)) {
                        changedCount++;
                        continue outer;
                    }
                }
                break;
            }
            if (changedCount == 50)
                throw new DateTimeException("One of the parsed fields has an incorrectly implemented resolve method");
            if (changedCount > 0) {
                resolveInstantFields();
                resolveDateFields();
                resolveTimeFields();
            }
        }
    }

    private void updateCheckConflict(TemporalField targetField, TemporalField changeField, Long changeValue) {
        Long old = fieldValues.put(changeField, changeValue);
        if (old != null && old.longValue() != changeValue.longValue())
            throw new DateTimeException("Conflict found: " + changeField + " " + old + " differs from " + changeField + " "
                + changeValue + " while resolving  " + targetField);
    }

    private void resolveInstantFields() {
        if (fieldValues.containsKey(ChronoField.INSTANT_SECONDS)) {
            if (zone != null) {
                resolveInstantFields0(zone);
            } else {
                Long offsetSecs = fieldValues.get(ChronoField.OFFSET_SECONDS);
                if (offsetSecs != null) resolveInstantFields0(ZoneOffset.ofTotalSeconds(offsetSecs.intValue()));
            }
        }
    }

    private void resolveInstantFields0(ZoneId selectedZone) {
        Instant instant = Instant.ofEpochSecond(fieldValues.get(ChronoField.INSTANT_SECONDS));
        ChronoZonedDateTime<?> zdt = chrono.zonedDateTime(instant, selectedZone);
        updateCheckConflict(zdt.toLocalDate());
        updateCheckConflict(ChronoField.INSTANT_SECONDS, ChronoField.SECOND_OF_DAY, (long) zdt.toLocalTime().toSecondOfDay());
        updateCheckConflict(ChronoField.INSTANT_SECONDS, ChronoField.OFFSET_SECONDS, (long) zdt.getOffset().getTotalSeconds());
    }

    private void resolveDateFields() {
        updateCheckConflict(chrono.resolveDate(fieldValues, resolverStyle));
    }

    private void updateCheckConflict(ChronoLocalDate cld) {
        if (date != null) {
            if (cld != null && !date.equals(cld))
                throw new DateTimeException("Conflict found: Fields resolved to two different dates: " + date + " " + cld);
        } else if (cld != null) {
            if (!chrono.equals(cld.getChronology()))
                throw new DateTimeException("ChronoLocalDate must use the effective parsed chronology: " + chrono);
            date = cld;
        }
    }

    private void resolveTimeFields() {
        if (fieldValues.containsKey(ChronoField.CLOCK_HOUR_OF_DAY)) {
            long ch = fieldValues.remove(ChronoField.CLOCK_HOUR_OF_DAY);
            if (resolverStyle == ResolverStyle.STRICT || (resolverStyle == ResolverStyle.SMART && ch != 0))
                ChronoField.CLOCK_HOUR_OF_DAY.checkValidValue(ch);
            updateCheckConflict(ChronoField.CLOCK_HOUR_OF_DAY, ChronoField.HOUR_OF_DAY, ch == 24 ? 0 : ch);
        }
        if (fieldValues.containsKey(ChronoField.CLOCK_HOUR_OF_AMPM)) {
            long ch = fieldValues.remove(ChronoField.CLOCK_HOUR_OF_AMPM);
            if (resolverStyle == ResolverStyle.STRICT || (resolverStyle == ResolverStyle.SMART && ch != 0))
                ChronoField.CLOCK_HOUR_OF_AMPM.checkValidValue(ch);
            updateCheckConflict(ChronoField.CLOCK_HOUR_OF_AMPM, ChronoField.HOUR_OF_AMPM, ch == 12 ? 0 : ch);
        }
        if (fieldValues.containsKey(ChronoField.AMPM_OF_DAY) && fieldValues.containsKey(ChronoField.HOUR_OF_AMPM)) {
            long ap = fieldValues.remove(ChronoField.AMPM_OF_DAY);
            long hap = fieldValues.remove(ChronoField.HOUR_OF_AMPM);
            if (resolverStyle == ResolverStyle.LENIENT) {
                updateCheckConflict(ChronoField.AMPM_OF_DAY, ChronoField.HOUR_OF_DAY,
                    Math.addExact(Math.multiplyExact(ap, 12), hap));
            } else {
                ChronoField.AMPM_OF_DAY.checkValidValue(ap);
                ChronoField.HOUR_OF_AMPM.checkValidValue(hap);
                updateCheckConflict(ChronoField.AMPM_OF_DAY, ChronoField.HOUR_OF_DAY, ap * 12 + hap);
            }
        }
        if (fieldValues.containsKey(ChronoField.NANO_OF_DAY)) {
            long nod = fieldValues.remove(ChronoField.NANO_OF_DAY);
            if (resolverStyle != ResolverStyle.LENIENT) ChronoField.NANO_OF_DAY.checkValidValue(nod);
            updateCheckConflict(ChronoField.NANO_OF_DAY, ChronoField.HOUR_OF_DAY, nod / 3600_000_000_000L);
            updateCheckConflict(ChronoField.NANO_OF_DAY, ChronoField.MINUTE_OF_HOUR, (nod / 60_000_000_000L) % 60);
            updateCheckConflict(ChronoField.NANO_OF_DAY, ChronoField.SECOND_OF_MINUTE, (nod / 1_000_000_000L) % 60);
            updateCheckConflict(ChronoField.NANO_OF_DAY, ChronoField.NANO_OF_SECOND, nod % 1_000_000_000L);
        }
        if (fieldValues.containsKey(ChronoField.MICRO_OF_DAY)) {
            long cod = fieldValues.remove(ChronoField.MICRO_OF_DAY);
            if (resolverStyle != ResolverStyle.LENIENT) ChronoField.MICRO_OF_DAY.checkValidValue(cod);
            updateCheckConflict(ChronoField.MICRO_OF_DAY, ChronoField.SECOND_OF_DAY, cod / 1_000_000L);
            updateCheckConflict(ChronoField.MICRO_OF_DAY, ChronoField.MICRO_OF_SECOND, cod % 1_000_000L);
        }
        if (fieldValues.containsKey(ChronoField.MILLI_OF_DAY)) {
            long lod = fieldValues.remove(ChronoField.MILLI_OF_DAY);
            if (resolverStyle != ResolverStyle.LENIENT) ChronoField.MILLI_OF_DAY.checkValidValue(lod);
            updateCheckConflict(ChronoField.MILLI_OF_DAY, ChronoField.SECOND_OF_DAY, lod / 1_000);
            updateCheckConflict(ChronoField.MILLI_OF_DAY, ChronoField.MILLI_OF_SECOND, lod % 1_000);
        }
        if (fieldValues.containsKey(ChronoField.SECOND_OF_DAY)) {
            long sod = fieldValues.remove(ChronoField.SECOND_OF_DAY);
            if (resolverStyle != ResolverStyle.LENIENT) ChronoField.SECOND_OF_DAY.checkValidValue(sod);
            updateCheckConflict(ChronoField.SECOND_OF_DAY, ChronoField.HOUR_OF_DAY, sod / 3600);
            updateCheckConflict(ChronoField.SECOND_OF_DAY, ChronoField.MINUTE_OF_HOUR, (sod / 60) % 60);
            updateCheckConflict(ChronoField.SECOND_OF_DAY, ChronoField.SECOND_OF_MINUTE, sod % 60);
        }
        if (fieldValues.containsKey(ChronoField.MINUTE_OF_DAY)) {
            long mod = fieldValues.remove(ChronoField.MINUTE_OF_DAY);
            if (resolverStyle != ResolverStyle.LENIENT) ChronoField.MINUTE_OF_DAY.checkValidValue(mod);
            updateCheckConflict(ChronoField.MINUTE_OF_DAY, ChronoField.HOUR_OF_DAY, mod / 60);
            updateCheckConflict(ChronoField.MINUTE_OF_DAY, ChronoField.MINUTE_OF_HOUR, mod % 60);
        }
        if (fieldValues.containsKey(ChronoField.NANO_OF_SECOND)) {
            long nos = fieldValues.get(ChronoField.NANO_OF_SECOND);
            if (resolverStyle != ResolverStyle.LENIENT) ChronoField.NANO_OF_SECOND.checkValidValue(nos);
            if (fieldValues.containsKey(ChronoField.MICRO_OF_SECOND)) {
                long cos = fieldValues.remove(ChronoField.MICRO_OF_SECOND);
                if (resolverStyle != ResolverStyle.LENIENT) ChronoField.MICRO_OF_SECOND.checkValidValue(cos);
                nos = cos * 1000 + (nos % 1000);
                updateCheckConflict(ChronoField.MICRO_OF_SECOND, ChronoField.NANO_OF_SECOND, nos);
            }
            if (fieldValues.containsKey(ChronoField.MILLI_OF_SECOND)) {
                long los = fieldValues.remove(ChronoField.MILLI_OF_SECOND);
                if (resolverStyle != ResolverStyle.LENIENT) ChronoField.MILLI_OF_SECOND.checkValidValue(los);
                updateCheckConflict(ChronoField.MILLI_OF_SECOND, ChronoField.NANO_OF_SECOND, los * 1_000_000L + (nos % 1_000_000L));
            }
        }
        if (fieldValues.containsKey(ChronoField.HOUR_OF_DAY) && fieldValues.containsKey(ChronoField.MINUTE_OF_HOUR)
            && fieldValues.containsKey(ChronoField.SECOND_OF_MINUTE) && fieldValues.containsKey(ChronoField.NANO_OF_SECOND)) {
            long hod = fieldValues.remove(ChronoField.HOUR_OF_DAY);
            long moh = fieldValues.remove(ChronoField.MINUTE_OF_HOUR);
            long som = fieldValues.remove(ChronoField.SECOND_OF_MINUTE);
            long nos = fieldValues.remove(ChronoField.NANO_OF_SECOND);
            resolveTime(hod, moh, som, nos);
        }
    }

    private void resolveTimeLenient() {
        if (time == null) {
            if (fieldValues.containsKey(ChronoField.MILLI_OF_SECOND)) {
                long los = fieldValues.remove(ChronoField.MILLI_OF_SECOND);
                if (fieldValues.containsKey(ChronoField.MICRO_OF_SECOND)) {
                    long cos = los * 1_000 + (fieldValues.get(ChronoField.MICRO_OF_SECOND) % 1_000);
                    updateCheckConflict(ChronoField.MILLI_OF_SECOND, ChronoField.MICRO_OF_SECOND, cos);
                    fieldValues.remove(ChronoField.MICRO_OF_SECOND);
                    fieldValues.put(ChronoField.NANO_OF_SECOND, cos * 1_000L);
                } else {
                    fieldValues.put(ChronoField.NANO_OF_SECOND, los * 1_000_000L);
                }
            } else if (fieldValues.containsKey(ChronoField.MICRO_OF_SECOND)) {
                long cos = fieldValues.remove(ChronoField.MICRO_OF_SECOND);
                fieldValues.put(ChronoField.NANO_OF_SECOND, cos * 1_000L);
            }
            if (!fieldValues.containsKey(ChronoField.HOUR_OF_DAY) && !fieldValues.containsKey(ChronoField.MINUTE_OF_HOUR)
                && !fieldValues.containsKey(ChronoField.SECOND_OF_MINUTE) && !fieldValues.containsKey(ChronoField.NANO_OF_SECOND)
                && resolverStyle != ResolverStyle.STRICT) {
                if (fieldValues.containsKey(ChronoField.AMPM_OF_DAY)) {
                    long ap = fieldValues.remove(ChronoField.AMPM_OF_DAY);
                    if (resolverStyle == ResolverStyle.LENIENT) {
                        resolveTime(Math.addExact(Math.multiplyExact(ap, 12), 6), 0, 0, 0);
                    } else {
                        ChronoField.AMPM_OF_DAY.checkValidValue(ap);
                        resolveTime(ap * 12 + 6, 0, 0, 0);
                    }
                }
            }
            Long hod = fieldValues.get(ChronoField.HOUR_OF_DAY);
            if (hod != null) {
                Long moh = fieldValues.get(ChronoField.MINUTE_OF_HOUR);
                Long som = fieldValues.get(ChronoField.SECOND_OF_MINUTE);
                Long nos = fieldValues.get(ChronoField.NANO_OF_SECOND);
                if ((moh == null && (som != null || nos != null)) || (moh != null && som == null && nos != null)) return;
                long mohVal = moh != null ? moh : 0;
                long somVal = som != null ? som : 0;
                long nosVal = nos != null ? nos : 0;
                resolveTime(hod, mohVal, somVal, nosVal);
                fieldValues.remove(ChronoField.HOUR_OF_DAY);
                fieldValues.remove(ChronoField.MINUTE_OF_HOUR);
                fieldValues.remove(ChronoField.SECOND_OF_MINUTE);
                fieldValues.remove(ChronoField.NANO_OF_SECOND);
            }
        }
        if (resolverStyle != ResolverStyle.LENIENT && fieldValues.size() > 0) {
            for (Map.Entry<TemporalField, Long> entry : fieldValues.entrySet()) {
                TemporalField field = entry.getKey();
                if (field instanceof ChronoField && field.isTimeBased()) ((ChronoField) field).checkValidValue(entry.getValue());
            }
        }
    }

    private void resolveTime(long hod, long moh, long som, long nos) {
        if (resolverStyle == ResolverStyle.LENIENT) {
            long totalNanos = Math.multiplyExact(hod, 3600_000_000_000L);
            totalNanos = Math.addExact(totalNanos, Math.multiplyExact(moh, 60_000_000_000L));
            totalNanos = Math.addExact(totalNanos, Math.multiplyExact(som, 1_000_000_000L));
            totalNanos = Math.addExact(totalNanos, nos);
            int excess = (int) Math.floorDiv(totalNanos, 86400_000_000_000L);
            long nod = Math.floorMod(totalNanos, 86400_000_000_000L);
            updateCheckConflict(LocalTime.ofNanoOfDay(nod), Period.ofDays(excess));
        } else {
            int mohVal = ChronoField.MINUTE_OF_HOUR.checkValidIntValue(moh);
            int nosVal = ChronoField.NANO_OF_SECOND.checkValidIntValue(nos);
            if (resolverStyle == ResolverStyle.SMART && hod == 24 && mohVal == 0 && som == 0 && nosVal == 0) {
                updateCheckConflict(LocalTime.MIDNIGHT, Period.ofDays(1));
            } else {
                int hodVal = ChronoField.HOUR_OF_DAY.checkValidIntValue(hod);
                int somVal = ChronoField.SECOND_OF_MINUTE.checkValidIntValue(som);
                updateCheckConflict(LocalTime.of(hodVal, mohVal, somVal, nosVal), Period.ZERO);
            }
        }
    }

    private void resolvePeriod() {
        if (date != null && time != null && !excessDays.isZero()) {
            date = date.plus(excessDays);
            excessDays = Period.ZERO;
        }
    }

    private void resolveFractional() {
        if (time == null && (fieldValues.containsKey(ChronoField.INSTANT_SECONDS)
            || fieldValues.containsKey(ChronoField.SECOND_OF_DAY) || fieldValues.containsKey(ChronoField.SECOND_OF_MINUTE))) {
            if (fieldValues.containsKey(ChronoField.NANO_OF_SECOND)) {
                long nos = fieldValues.get(ChronoField.NANO_OF_SECOND);
                fieldValues.put(ChronoField.MICRO_OF_SECOND, nos / 1000);
                fieldValues.put(ChronoField.MILLI_OF_SECOND, nos / 1000000);
            } else {
                fieldValues.put(ChronoField.NANO_OF_SECOND, 0L);
                fieldValues.put(ChronoField.MICRO_OF_SECOND, 0L);
                fieldValues.put(ChronoField.MILLI_OF_SECOND, 0L);
            }
        }
    }

    private void resolveInstant() {
        if (!fieldValues.containsKey(ChronoField.INSTANT_SECONDS) && date != null && time != null) {
            Long offsetSecs = fieldValues.get(ChronoField.OFFSET_SECONDS);
            if (offsetSecs != null) {
                ZoneOffset offset = ZoneOffset.ofTotalSeconds(offsetSecs.intValue());
                long instant = date.atTime(time).atZone(offset).toEpochSecond();
                fieldValues.put(ChronoField.INSTANT_SECONDS, instant);
            } else if (zone != null) {
                ChronoZonedDateTime<?> czdt = date.atTime(time).atZone(zone);
                fieldValues.put(ChronoField.INSTANT_SECONDS, czdt.toEpochSecond());
            }
        }
    }

    private void updateCheckConflict(LocalTime timeToSet, Period periodToSet) {
        if (time != null) {
            if (!time.equals(timeToSet))
                throw new DateTimeException("Conflict found: Fields resolved to different times: " + time + " " + timeToSet);
            if (!excessDays.isZero() && !periodToSet.isZero() && !excessDays.equals(periodToSet)) {
                throw new DateTimeException("Conflict found: Fields resolved to different excess periods: " + excessDays + " "
                    + periodToSet);
            } else {
                excessDays = periodToSet;
            }
        } else {
            time = timeToSet;
            excessDays = periodToSet;
        }
    }

    private void crossCheck() {
        if (date != null) crossCheck(date);
        if (time != null) {
            crossCheck(time);
            if (date != null && fieldValues.size() > 0) crossCheck(date.atTime(time));
        }
    }

    private void crossCheck(TemporalAccessor target) {
        for (Iterator<Map.Entry<TemporalField, Long>> it = fieldValues.entrySet().iterator(); it.hasNext(); ) {
            Map.Entry<TemporalField, Long> entry = it.next();
            TemporalField field = entry.getKey();
            if (target.isSupported(field)) {
                long val1;
                try {
                    val1 = target.getLong(field);
                } catch (RuntimeException ex) {
                    continue;
                }
                long val2 = entry.getValue();
                if (val1 != val2)
                    throw new DateTimeException("Conflict found: Field " + field + " " + val1 + " differs from " + field + " "
                        + val2 + " derived from " + target);
                it.remove();
            }
        }
    }

    @Override
    public String toString() {
        StringBuilder buf = new StringBuilder(64);
        buf.append(fieldValues).append(',').append(chrono);
        if (zone != null) buf.append(',').append(zone).append(',').append(zoneNameType);
        if (date != null || time != null) {
            buf.append(" resolved to ");
            if (date != null) {
                buf.append(date);
                if (time != null) buf.append('T').append(time);
            } else {
                buf.append(time);
            }
        }
        return buf.toString();
    }
}

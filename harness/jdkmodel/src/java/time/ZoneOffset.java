/*
 * rocq-jvm model of java.time.ZoneOffset (clean-room, Apache-2.0): JDK 21's parsing of offset ids
 * (+h, +hh, +hh:mm, +hhmm, +hh:mm:ss, +hhmmss with every DateTimeException text), validation, the
 * identity cache of multiples of 15 minutes (the JDK's SECONDS_CACHE; its ID_CACHE only ever answers
 * "Z" differently from parsing), ids, fixed rules, field access, compareTo/equals/hashCode.
 */
package java.time;

import java.time.temporal.ChronoField;
import java.time.temporal.Temporal;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalAdjuster;
import java.time.temporal.TemporalField;
import java.time.temporal.TemporalQueries;
import java.time.temporal.TemporalQuery;
import java.time.temporal.UnsupportedTemporalTypeException;
import java.time.temporal.ValueRange;
import java.time.zone.ZoneRules;
import java.util.Objects;

public final class ZoneOffset extends ZoneId implements TemporalAccessor, TemporalAdjuster, Comparable<ZoneOffset>,
        java.io.Serializable {
    private static final long serialVersionUID = 2357656521762053153L;

    private static final int MAX_SECONDS = 18 * LocalTime.SECONDS_PER_HOUR;
    /** The cached offsets that are multiples of 15 minutes, by (totalSeconds / 900) + 72. */
    private static final ZoneOffset[] QUARTERS = new ZoneOffset[145];

    public static final ZoneOffset UTC = ZoneOffset.ofTotalSeconds(0);
    public static final ZoneOffset MIN = ZoneOffset.ofTotalSeconds(-MAX_SECONDS);
    public static final ZoneOffset MAX = ZoneOffset.ofTotalSeconds(MAX_SECONDS);

    private final int totalSeconds;
    private final transient String id;
    private transient ZoneRules rules;

    private ZoneOffset(int totalSeconds) {
        this.totalSeconds = totalSeconds;
        this.id = buildId(totalSeconds);
    }

    public static ZoneOffset of(String offsetId) {
        Objects.requireNonNull(offsetId, "offsetId");
        if (offsetId.equals("Z")) return UTC;
        int hours, minutes, seconds;
        switch (offsetId.length()) {
            case 2:
                offsetId = offsetId.charAt(0) + "0" + offsetId.charAt(1);
                hours = parseNumber(offsetId, 1, false);
                minutes = 0;
                seconds = 0;
                break;
            case 3:
                hours = parseNumber(offsetId, 1, false);
                minutes = 0;
                seconds = 0;
                break;
            case 5:
                hours = parseNumber(offsetId, 1, false);
                minutes = parseNumber(offsetId, 3, false);
                seconds = 0;
                break;
            case 6:
                hours = parseNumber(offsetId, 1, false);
                minutes = parseNumber(offsetId, 4, true);
                seconds = 0;
                break;
            case 7:
                hours = parseNumber(offsetId, 1, false);
                minutes = parseNumber(offsetId, 3, false);
                seconds = parseNumber(offsetId, 5, false);
                break;
            case 9:
                hours = parseNumber(offsetId, 1, false);
                minutes = parseNumber(offsetId, 4, true);
                seconds = parseNumber(offsetId, 7, true);
                break;
            default:
                throw new DateTimeException("Invalid ID for ZoneOffset, invalid format: " + offsetId);
        }
        char first = offsetId.charAt(0);
        if (first != '+' && first != '-')
            throw new DateTimeException("Invalid ID for ZoneOffset, plus/minus not found when expected: " + offsetId);
        if (first == '-') return ofHoursMinutesSeconds(-hours, -minutes, -seconds);
        return ofHoursMinutesSeconds(hours, minutes, seconds);
    }

    private static int parseNumber(CharSequence offsetId, int pos, boolean precededByColon) {
        if (precededByColon && offsetId.charAt(pos - 1) != ':')
            throw new DateTimeException("Invalid ID for ZoneOffset, colon not found when expected: " + offsetId);
        char ch1 = offsetId.charAt(pos);
        char ch2 = offsetId.charAt(pos + 1);
        if (ch1 < '0' || ch1 > '9' || ch2 < '0' || ch2 > '9')
            throw new DateTimeException("Invalid ID for ZoneOffset, non numeric characters found: " + offsetId);
        return (ch1 - 48) * 10 + (ch2 - 48);
    }

    public static ZoneOffset ofHours(int hours) {
        return ofHoursMinutesSeconds(hours, 0, 0);
    }

    public static ZoneOffset ofHoursMinutes(int hours, int minutes) {
        return ofHoursMinutesSeconds(hours, minutes, 0);
    }

    public static ZoneOffset ofHoursMinutesSeconds(int hours, int minutes, int seconds) {
        validate(hours, minutes, seconds);
        return ofTotalSeconds(hours * LocalTime.SECONDS_PER_HOUR + minutes * LocalTime.SECONDS_PER_MINUTE + seconds);
    }

    public static ZoneOffset from(TemporalAccessor temporal) {
        Objects.requireNonNull(temporal, "temporal");
        ZoneOffset offset = temporal.query(TemporalQueries.offset());
        if (offset == null)
            throw new DateTimeException("Unable to obtain ZoneOffset from TemporalAccessor: " + temporal + " of type "
                + temporal.getClass().getName());
        return offset;
    }

    private static void validate(int hours, int minutes, int seconds) {
        if (hours < -18 || hours > 18)
            throw new DateTimeException("Zone offset hours not in valid range: value " + hours + " is not in the range -18 to 18");
        if (hours > 0) {
            if (minutes < 0 || seconds < 0)
                throw new DateTimeException("Zone offset minutes and seconds must be positive because hours is positive");
        } else if (hours < 0) {
            if (minutes > 0 || seconds > 0)
                throw new DateTimeException("Zone offset minutes and seconds must be negative because hours is negative");
        } else if ((minutes > 0 && seconds < 0) || (minutes < 0 && seconds > 0)) {
            throw new DateTimeException("Zone offset minutes and seconds must have the same sign");
        }
        if (minutes < -59 || minutes > 59)
            throw new DateTimeException("Zone offset minutes not in valid range: value " + minutes + " is not in the range -59 to 59");
        if (seconds < -59 || seconds > 59)
            throw new DateTimeException("Zone offset seconds not in valid range: value " + seconds + " is not in the range -59 to 59");
        if (Math.abs(hours) == 18 && (minutes | seconds) != 0)
            throw new DateTimeException("Zone offset not in valid range: -18:00 to +18:00");
    }

    public static ZoneOffset ofTotalSeconds(int totalSeconds) {
        if (totalSeconds < -MAX_SECONDS || totalSeconds > MAX_SECONDS)
            throw new DateTimeException("Zone offset not in valid range: -18:00 to +18:00");
        if (totalSeconds % 900 == 0) {
            int k = totalSeconds / 900 + 72;
            ZoneOffset r = QUARTERS[k];
            if (r == null) {
                r = new ZoneOffset(totalSeconds);
                QUARTERS[k] = r;
            }
            return r;
        }
        return new ZoneOffset(totalSeconds);
    }

    private static String buildId(int totalSeconds) {
        if (totalSeconds == 0) return "Z";
        int abs = Math.abs(totalSeconds);
        StringBuilder buf = new StringBuilder();
        int absHours = abs / LocalTime.SECONDS_PER_HOUR;
        int absMinutes = (abs / LocalTime.SECONDS_PER_MINUTE) % LocalTime.MINUTES_PER_HOUR;
        buf.append(totalSeconds < 0 ? "-" : "+").append(absHours < 10 ? "0" : "").append(absHours)
            .append(absMinutes < 10 ? ":0" : ":").append(absMinutes);
        int absSeconds = abs % LocalTime.SECONDS_PER_MINUTE;
        if (absSeconds != 0) buf.append(absSeconds < 10 ? ":0" : ":").append(absSeconds);
        return buf.toString();
    }

    public int getTotalSeconds() {
        return totalSeconds;
    }

    @Override
    public String getId() {
        return id;
    }

    @Override
    public ZoneRules getRules() {
        ZoneRules r = rules;
        if (r == null) r = rules = ZoneRules.of(this);
        return r;
    }

    @Override
    public ZoneId normalized() {
        return this;
    }

    @Override
    ZoneOffset getOffset(long epochSecond) {
        return this;
    }

    @Override
    public boolean isSupported(TemporalField field) {
        if (field instanceof ChronoField) return field == ChronoField.OFFSET_SECONDS;
        return field != null && field.isSupportedBy(this);
    }

    @Override
    public ValueRange range(TemporalField field) {
        return TemporalAccessor.super.range(field);
    }

    @Override
    public int get(TemporalField field) {
        if (field == ChronoField.OFFSET_SECONDS) return totalSeconds;
        if (field instanceof ChronoField) throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
        return range(field).checkValidIntValue(getLong(field), field);
    }

    @Override
    public long getLong(TemporalField field) {
        if (field == ChronoField.OFFSET_SECONDS) return totalSeconds;
        if (field instanceof ChronoField) throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
        return field.getFrom(this);
    }

    @Override
    @SuppressWarnings("unchecked")
    public <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.offset() || query == TemporalQueries.zone()) return (R) this;
        return TemporalAccessor.super.query(query);
    }

    @Override
    public Temporal adjustInto(Temporal temporal) {
        return temporal.with(ChronoField.OFFSET_SECONDS, totalSeconds);
    }

    @Override
    public int compareTo(ZoneOffset other) {
        return other.totalSeconds - totalSeconds;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj instanceof ZoneOffset) return totalSeconds == ((ZoneOffset) obj).totalSeconds;
        return false;
    }

    @Override
    public int hashCode() {
        return totalSeconds;
    }

    @Override
    public String toString() {
        return id;
    }
}

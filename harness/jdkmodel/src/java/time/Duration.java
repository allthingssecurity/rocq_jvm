/*
 * rocq-jvm model of java.time.Duration (clean-room, Apache-2.0): seconds + nanos-of-second as in
 * JDK 21, with the JDK's normalisation, exact-arithmetic errors ("long overflow" from Math.*Exact),
 * parse (the JDK's grammar, by a direct parser of its pattern), toString (ISO-8601) and the
 * conversions. multipliedBy / dividedBy / negated compute the JDK's BigDecimal results with exact
 * long arithmetic; where an intermediate value would not fit in a long the model is STUCK (the JDK's
 * "Exceeds capacity" message prints a 100+ bit number). between, addTo and subtractFrom follow
 * JDK 21 over the model temporals (until in NANOS, then SECONDS with the nano-of-second correction).
 */
package java.time;

import java.time.format.DateTimeParseException;
import java.time.temporal.ChronoUnit;
import java.time.temporal.TemporalAmount;
import java.time.temporal.TemporalUnit;
import java.time.temporal.UnsupportedTemporalTypeException;
import java.util.List;
import java.util.Objects;

public final class Duration implements TemporalAmount, Comparable<Duration>, java.io.Serializable {
    private static final long serialVersionUID = 3078945930695997490L;

    static final long NANOS_PER_SECOND = 1000_000_000L;
    static final int SECONDS_PER_DAY = 86400;
    static final int SECONDS_PER_HOUR = 3600;
    static final int SECONDS_PER_MINUTE = 60;

    public static final Duration ZERO = new Duration(0, 0);

    private final long seconds;
    private final int nanos;

    private Duration(long seconds, int nanos) {
        this.seconds = seconds;
        this.nanos = nanos;
    }

    private static Duration create(long seconds, int nanoAdjustment) {
        if ((seconds | nanoAdjustment) == 0) return ZERO;
        return new Duration(seconds, nanoAdjustment);
    }

    public static Duration ofDays(long days) {
        return create(Math.multiplyExact(days, SECONDS_PER_DAY), 0);
    }

    public static Duration ofHours(long hours) {
        return create(Math.multiplyExact(hours, SECONDS_PER_HOUR), 0);
    }

    public static Duration ofMinutes(long minutes) {
        return create(Math.multiplyExact(minutes, SECONDS_PER_MINUTE), 0);
    }

    public static Duration ofSeconds(long seconds) {
        return create(seconds, 0);
    }

    public static Duration ofSeconds(long seconds, long nanoAdjustment) {
        long secs = Math.addExact(seconds, Math.floorDiv(nanoAdjustment, NANOS_PER_SECOND));
        int nos = (int) Math.floorMod(nanoAdjustment, NANOS_PER_SECOND);
        return create(secs, nos);
    }

    public static Duration ofMillis(long millis) {
        long secs = millis / 1000;
        int mos = (int) (millis % 1000);
        if (mos < 0) {
            mos += 1000;
            secs--;
        }
        return create(secs, mos * 1000_000);
    }

    public static Duration ofNanos(long nanos) {
        long secs = nanos / NANOS_PER_SECOND;
        int nos = (int) (nanos % NANOS_PER_SECOND);
        if (nos < 0) {
            nos += (int) NANOS_PER_SECOND;
            secs--;
        }
        return create(secs, nos);
    }

    public static Duration of(long amount, TemporalUnit unit) {
        return ZERO.plus(amount, unit);
    }

    public static Duration from(TemporalAmount amount) {
        Objects.requireNonNull(amount, "amount");
        Duration duration = ZERO;
        for (TemporalUnit unit : amount.getUnits()) {
            duration = duration.plus(amount.get(unit), unit);
        }
        return duration;
    }

    /** The JDK's pattern ([-+]?)P(?:([-+]?[0-9]+)D)?(T(?:([-+]?[0-9]+)H)?(?:([-+]?[0-9]+)M)?
     *  (?:([-+]?[0-9]+)(?:[.,]([0-9]{0,9}))?S)?)?, case-insensitive, matched against the whole text:
     *  its groups' start/end (-1 when absent), computed by a direct parser of the same language (every
     *  optional part begins with a sign, a digit or a letter that its successors cannot begin with, so
     *  the regex's backtracking never revisits a choice that succeeded). null = no match. */
    private static int[] groups(String t) {
        int[] g = new int[16];
        for (int k = 0; k < 16; k++) g[k] = -1;
        int n = t.length(), i = 0;
        g[2] = i;
        if (i < n && (t.charAt(i) == '-' || t.charAt(i) == '+')) i++;
        g[3] = i;
        if (i >= n || (t.charAt(i) != 'P' && t.charAt(i) != 'p')) return null;
        i++;
        int e = number(t, i);
        if (e > i && e < n && (t.charAt(e) == 'D' || t.charAt(e) == 'd')) {
            g[4] = i;
            g[5] = e;
            i = e + 1;
        }
        if (i < n && (t.charAt(i) == 'T' || t.charAt(i) == 't')) {
            int ts = i;
            i++;
            e = number(t, i);
            if (e > i && e < n && (t.charAt(e) == 'H' || t.charAt(e) == 'h')) {
                g[8] = i;
                g[9] = e;
                i = e + 1;
            }
            e = number(t, i);
            if (e > i && e < n && (t.charAt(e) == 'M' || t.charAt(e) == 'm')) {
                g[10] = i;
                g[11] = e;
                i = e + 1;
            }
            e = number(t, i);
            if (e > i) {
                int j = e, fs = -1, fe = -1;
                if (j < n && (t.charAt(j) == '.' || t.charAt(j) == ',')) {
                    fs = j + 1;
                    int k = fs;
                    while (k < n && t.charAt(k) >= '0' && t.charAt(k) <= '9' && k - fs < 9) k++;
                    fe = k;
                    j = k;
                }
                if (j < n && (t.charAt(j) == 'S' || t.charAt(j) == 's')) {
                    g[12] = i;
                    g[13] = e;
                    g[14] = fs;
                    g[15] = fe;
                    i = j + 1;
                }
            }
            g[6] = ts;
            g[7] = i;
        }
        return i == n ? g : null;
    }

    /** End of [-+]?[0-9]+ from i, or i if there is none. */
    private static int number(String t, int i) {
        int n = t.length(), j = i;
        if (j < n && (t.charAt(j) == '-' || t.charAt(j) == '+')) j++;
        int d = j;
        while (j < n && t.charAt(j) >= '0' && t.charAt(j) <= '9') j++;
        return j > d ? j : i;
    }

    public static Duration parse(CharSequence text) {
        Objects.requireNonNull(text, "text");
        int[] m = groups(text.toString());
        if (m != null) {
            if (!charMatch(text, m[6], m[7], 'T')) {
                boolean negate = charMatch(text, m[2], m[3], '-');
                int dayStart = m[4], dayEnd = m[5];
                int hourStart = m[8], hourEnd = m[9];
                int minuteStart = m[10], minuteEnd = m[11];
                int secondStart = m[12], secondEnd = m[13];
                int fractionStart = m[14], fractionEnd = m[15];
                if (dayStart >= 0 || hourStart >= 0 || minuteStart >= 0 || secondStart >= 0) {
                    long daysAsSecs = parseNumber(text, dayStart, dayEnd, SECONDS_PER_DAY, "days");
                    long hoursAsSecs = parseNumber(text, hourStart, hourEnd, SECONDS_PER_HOUR, "hours");
                    long minsAsSecs = parseNumber(text, minuteStart, minuteEnd, SECONDS_PER_MINUTE, "minutes");
                    long secs = parseNumber(text, secondStart, secondEnd, 1, "seconds");
                    boolean negativeSecs = secondStart >= 0 && text.charAt(secondStart) == '-';
                    int nanosOf = parseFraction(text, fractionStart, fractionEnd, negativeSecs ? -1 : 1);
                    try {
                        return create(negate, daysAsSecs, hoursAsSecs, minsAsSecs, secs, nanosOf);
                    } catch (ArithmeticException ex) {
                        throw new DateTimeParseException("Text cannot be parsed to a Duration: overflow", text, 0, ex);
                    }
                }
            }
        }
        throw new DateTimeParseException("Text cannot be parsed to a Duration", text, 0);
    }

    private static boolean charMatch(CharSequence text, int start, int end, char c) {
        return (start >= 0 && end == start + 1 && text.charAt(start) == c);
    }

    private static long parseNumber(CharSequence text, int start, int end, int multiplier, String errorText) {
        if (start < 0 || end < 0) return 0;
        try {
            long val = Long.parseLong(text.toString().substring(start, end));
            return Math.multiplyExact(val, multiplier);
        } catch (NumberFormatException | ArithmeticException ex) {
            throw new DateTimeParseException("Text cannot be parsed to a Duration: " + errorText, text, 0, ex);
        }
    }

    private static int parseFraction(CharSequence text, int start, int end, int negate) {
        if (start < 0 || end < 0 || end - start == 0) return 0;
        int fraction = Integer.parseInt(text.toString().substring(start, end));
        for (int i = end - start; i < 9; i++) fraction *= 10;
        return fraction * negate;
    }

    private static Duration create(boolean negate, long daysAsSecs, long hoursAsSecs, long minsAsSecs, long secs, int nanos) {
        long seconds = Math.addExact(daysAsSecs, Math.addExact(hoursAsSecs, Math.addExact(minsAsSecs, secs)));
        if (negate) return ofSeconds(seconds, nanos).negated();
        return ofSeconds(seconds, nanos);
    }

    public static Duration between(java.time.temporal.Temporal startInclusive, java.time.temporal.Temporal endExclusive) {
        try {
            return ofNanos(startInclusive.until(endExclusive, ChronoUnit.NANOS));
        } catch (DateTimeException | ArithmeticException ex) {
            long secs = startInclusive.until(endExclusive, ChronoUnit.SECONDS);
            long nanos;
            try {
                nanos = endExclusive.getLong(java.time.temporal.ChronoField.NANO_OF_SECOND)
                    - startInclusive.getLong(java.time.temporal.ChronoField.NANO_OF_SECOND);
                if (secs > 0 && nanos < 0) {
                    secs++;
                } else if (secs < 0 && nanos > 0) {
                    secs--;
                }
            } catch (DateTimeException ex2) {
                nanos = 0;
            }
            return ofSeconds(secs, nanos);
        }
    }

    public long get(TemporalUnit unit) {
        if (unit == ChronoUnit.SECONDS) return seconds;
        else if (unit == ChronoUnit.NANOS) return nanos;
        else throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
    }

    public List<TemporalUnit> getUnits() {
        return List.of(ChronoUnit.SECONDS, ChronoUnit.NANOS);
    }

    public boolean isPositive() {
        return (seconds | nanos) > 0;
    }

    public boolean isZero() {
        return (seconds | nanos) == 0;
    }

    public boolean isNegative() {
        return seconds < 0;
    }

    public long getSeconds() {
        return seconds;
    }

    public int getNano() {
        return nanos;
    }

    public Duration withSeconds(long seconds) {
        return create(seconds, nanos);
    }

    public Duration withNanos(int nanoOfSecond) {
        if (nanoOfSecond < 0 || nanoOfSecond > 999_999_999)
            throw new DateTimeException("Invalid value for NanoOfSecond (valid values 0 - 999999999): " + nanoOfSecond);
        return create(seconds, nanoOfSecond);
    }

    public Duration plus(Duration duration) {
        return plus(duration.getSeconds(), duration.getNano());
    }

    public Duration plus(long amountToAdd, TemporalUnit unit) {
        Objects.requireNonNull(unit, "unit");
        if (unit == ChronoUnit.DAYS) return plus(Math.multiplyExact(amountToAdd, SECONDS_PER_DAY), 0);
        if (unit.isDurationEstimated()) throw new UnsupportedTemporalTypeException("Unit must not have an estimated duration");
        if (amountToAdd == 0) return this;
        if (unit instanceof ChronoUnit) {
            switch ((ChronoUnit) unit) {
                case NANOS: return plusNanos(amountToAdd);
                case MICROS: return plusSeconds((amountToAdd / (1000_000L * 1000)) * 1000).plusNanos((amountToAdd % (1000_000L * 1000)) * 1000);
                case MILLIS: return plusMillis(amountToAdd);
                case SECONDS: return plusSeconds(amountToAdd);
                default: return plusSeconds(Math.multiplyExact(unit.getDuration().seconds, amountToAdd));
            }
        }
        Duration duration = unit.getDuration().multipliedBy(amountToAdd);
        return plusSeconds(duration.getSeconds()).plusNanos(duration.getNano());
    }

    public Duration plusDays(long daysToAdd) {
        return plus(Math.multiplyExact(daysToAdd, SECONDS_PER_DAY), 0);
    }

    public Duration plusHours(long hoursToAdd) {
        return plus(Math.multiplyExact(hoursToAdd, SECONDS_PER_HOUR), 0);
    }

    public Duration plusMinutes(long minutesToAdd) {
        return plus(Math.multiplyExact(minutesToAdd, SECONDS_PER_MINUTE), 0);
    }

    public Duration plusSeconds(long secondsToAdd) {
        return plus(secondsToAdd, 0);
    }

    public Duration plusMillis(long millisToAdd) {
        return plus(millisToAdd / 1000, (millisToAdd % 1000) * 1000_000);
    }

    public Duration plusNanos(long nanosToAdd) {
        return plus(0, nanosToAdd);
    }

    private Duration plus(long secondsToAdd, long nanosToAdd) {
        if ((secondsToAdd | nanosToAdd) == 0) return this;
        long epochSec = Math.addExact(seconds, secondsToAdd);
        epochSec = Math.addExact(epochSec, nanosToAdd / NANOS_PER_SECOND);
        nanosToAdd = nanosToAdd % NANOS_PER_SECOND;
        long nanoAdjustment = nanos + nanosToAdd;
        return ofSeconds(epochSec, nanoAdjustment);
    }

    public Duration minus(Duration duration) {
        long secsToSubtract = duration.getSeconds();
        int nanosToSubtract = duration.getNano();
        if (secsToSubtract == Long.MIN_VALUE) return plus(Long.MAX_VALUE, -nanosToSubtract).plus(1, 0);
        return plus(-secsToSubtract, -nanosToSubtract);
    }

    public Duration minus(long amountToSubtract, TemporalUnit unit) {
        return (amountToSubtract == Long.MIN_VALUE ? plus(Long.MAX_VALUE, unit).plus(1, unit) : plus(-amountToSubtract, unit));
    }

    public Duration minusDays(long d) {
        return (d == Long.MIN_VALUE ? plusDays(Long.MAX_VALUE).plusDays(1) : plusDays(-d));
    }

    public Duration minusHours(long h) {
        return (h == Long.MIN_VALUE ? plusHours(Long.MAX_VALUE).plusHours(1) : plusHours(-h));
    }

    public Duration minusMinutes(long m) {
        return (m == Long.MIN_VALUE ? plusMinutes(Long.MAX_VALUE).plusMinutes(1) : plusMinutes(-m));
    }

    public Duration minusSeconds(long s) {
        return (s == Long.MIN_VALUE ? plusSeconds(Long.MAX_VALUE).plusSeconds(1) : plusSeconds(-s));
    }

    public Duration minusMillis(long m) {
        return (m == Long.MIN_VALUE ? plusMillis(Long.MAX_VALUE).plusMillis(1) : plusMillis(-m));
    }

    public Duration minusNanos(long n) {
        return (n == Long.MIN_VALUE ? plusNanos(Long.MAX_VALUE).plusNanos(1) : plusNanos(-n));
    }

    private static RuntimeException capacity() {
        return ModelStuckTime.unsupported("Duration: a result beyond the exact long arithmetic of the model");
    }

    /** (seconds * 10^9 + nanos) * m, exactly, as a Duration (the JDK's BigDecimal product). */
    public Duration multipliedBy(long multiplicand) {
        if (multiplicand == 0) return ZERO;
        if (multiplicand == 1) return this;
        long q = Math.floorDiv(multiplicand, NANOS_PER_SECOND);
        long r = Math.floorMod(multiplicand, NANOS_PER_SECOND);
        long nr = nanos * r; // < 10^18
        try {
            long secs = Math.addExact(Math.addExact(Math.multiplyExact(seconds, multiplicand), Math.multiplyExact((long) nanos, q)),
                Math.floorDiv(nr, NANOS_PER_SECOND));
            return create(secs, (int) Math.floorMod(nr, NANOS_PER_SECOND));
        } catch (ArithmeticException e) {
            throw capacity();
        }
    }

    /** The total nanoseconds, if they fit in a long. */
    private long totalNanosOrStuck() {
        try {
            return Math.addExact(Math.multiplyExact(seconds, NANOS_PER_SECOND), nanos);
        } catch (ArithmeticException e) {
            throw capacity();
        }
    }

    public Duration dividedBy(long divisor) {
        if (divisor == 0) throw new ArithmeticException("Cannot divide by zero");
        if (divisor == 1) return this;
        long total = totalNanosOrStuck();
        if (total == Long.MIN_VALUE && divisor == -1) throw capacity();
        return ofNanos(total / divisor);
    }

    public long dividedBy(Duration divisor) {
        Objects.requireNonNull(divisor, "divisor");
        long a = totalNanosOrStuck();
        long b = divisor.totalNanosOrStuck();
        if (b == 0) throw new ArithmeticException(a == 0 ? "Division undefined" : "Division by zero");
        if (a == Long.MIN_VALUE && b == -1) throw capacity();
        return a / b;
    }

    public Duration negated() {
        return multipliedBy(-1);
    }

    public Duration abs() {
        return isNegative() ? negated() : this;
    }

    public java.time.temporal.Temporal addTo(java.time.temporal.Temporal temporal) {
        if (seconds != 0) temporal = temporal.plus(seconds, ChronoUnit.SECONDS);
        if (nanos != 0) temporal = temporal.plus(nanos, ChronoUnit.NANOS);
        return temporal;
    }

    public java.time.temporal.Temporal subtractFrom(java.time.temporal.Temporal temporal) {
        if (seconds != 0) temporal = temporal.minus(seconds, ChronoUnit.SECONDS);
        if (nanos != 0) temporal = temporal.minus(nanos, ChronoUnit.NANOS);
        return temporal;
    }

    public long toDays() {
        return seconds / SECONDS_PER_DAY;
    }

    public long toHours() {
        return seconds / SECONDS_PER_HOUR;
    }

    public long toMinutes() {
        return seconds / SECONDS_PER_MINUTE;
    }

    public long toSeconds() {
        return seconds;
    }

    public long toMillis() {
        long tempSeconds = seconds;
        long tempNanos = nanos;
        if (tempSeconds < 0) {
            tempSeconds = tempSeconds + 1;
            tempNanos = tempNanos - NANOS_PER_SECOND;
        }
        long millis = Math.multiplyExact(tempSeconds, 1000);
        millis = Math.addExact(millis, tempNanos / 1000_000);
        return millis;
    }

    public long toNanos() {
        long tempSeconds = seconds;
        long tempNanos = nanos;
        if (tempSeconds < 0) {
            tempSeconds = tempSeconds + 1;
            tempNanos = tempNanos - NANOS_PER_SECOND;
        }
        long totalNanos = Math.multiplyExact(tempSeconds, NANOS_PER_SECOND);
        totalNanos = Math.addExact(totalNanos, tempNanos);
        return totalNanos;
    }

    public long toDaysPart() {
        return seconds / SECONDS_PER_DAY;
    }

    public int toHoursPart() {
        return (int) (toHours() % 24);
    }

    public int toMinutesPart() {
        return (int) (toMinutes() % 60);
    }

    public int toSecondsPart() {
        return (int) (seconds % SECONDS_PER_MINUTE);
    }

    public int toMillisPart() {
        return nanos / 1000_000;
    }

    public int toNanosPart() {
        return nanos;
    }

    public Duration truncatedTo(TemporalUnit unit) {
        Objects.requireNonNull(unit, "unit");
        if (unit == ChronoUnit.SECONDS && (seconds >= 0 || nanos == 0)) {
            return new Duration(seconds, 0);
        } else if (unit == ChronoUnit.NANOS) {
            return this;
        }
        Duration unitDur = unit.getDuration();
        if (unitDur.getSeconds() > SECONDS_PER_DAY) {
            throw new UnsupportedTemporalTypeException("Unit is too large to be used for truncation");
        }
        long dur = unitDur.toNanos();
        if ((86400L * NANOS_PER_SECOND % dur) != 0) {
            throw new UnsupportedTemporalTypeException("Unit must divide into a standard day without remainder");
        }
        long nod = (seconds % SECONDS_PER_DAY) * NANOS_PER_SECOND + nanos;
        long result = (nod / dur) * dur;
        return plusNanos(result - nod);
    }

    public int compareTo(Duration otherDuration) {
        int cmp = Long.compare(seconds, otherDuration.seconds);
        if (cmp != 0) return cmp;
        return nanos - otherDuration.nanos;
    }

    public boolean equals(Object other) {
        if (this == other) return true;
        return (other instanceof Duration) && this.seconds == ((Duration) other).seconds && this.nanos == ((Duration) other).nanos;
    }

    public int hashCode() {
        return ((int) (seconds ^ (seconds >>> 32))) + (51 * nanos);
    }

    public String toString() {
        if (this == ZERO) return "PT0S";
        long effectiveTotalSecs = seconds;
        if (seconds < 0 && nanos > 0) effectiveTotalSecs++;
        long hours = effectiveTotalSecs / SECONDS_PER_HOUR;
        int minutes = (int) ((effectiveTotalSecs % SECONDS_PER_HOUR) / SECONDS_PER_MINUTE);
        int secs = (int) (effectiveTotalSecs % SECONDS_PER_MINUTE);
        StringBuilder buf = new StringBuilder(24);
        buf.append("PT");
        if (hours != 0) buf.append(hours).append('H');
        if (minutes != 0) buf.append(minutes).append('M');
        if (secs == 0 && nanos == 0 && buf.length() > 2) return buf.toString();
        if (seconds < 0 && nanos > 0) {
            if (secs == 0) buf.append("-0");
            else buf.append(secs);
        } else {
            buf.append(secs);
        }
        if (nanos > 0) {
            String frac = String.valueOf(seconds < 0 ? 2 * NANOS_PER_SECOND - nanos : nanos + NANOS_PER_SECOND);
            int end = frac.length();
            while (frac.charAt(end - 1) == '0') end--;
            buf.append('.').append(frac.substring(1, end));
        }
        buf.append('S');
        return buf.toString();
    }
}

final class ModelStuckTime {
    private ModelStuckTime() {
    }

    static native RuntimeException unsupported(String what);
}

/*
 * rocq-jvm model of java.time.Period (clean-room, Apache-2.0): years/months/days as in JDK 21, the
 * ZERO identity, Math.*Exact overflow errors, normalized, addTo/subtractFrom (years or total months,
 * then days, with the ISO chronology check), hashCode and toString. parse is a direct parser of the
 * JDK's pattern ([-+]?)P(?:([-+]?[0-9]+)Y)?(?:([-+]?[0-9]+)M)?(?:([-+]?[0-9]+)W)?(?:([-+]?[0-9]+)D)?
 * (case-insensitive, whole text; every optional part begins with a sign or digit and ends with its
 * letter, so the regex never needs to backtrack), with Integer.parseInt and the JDK's exceptions.
 */
package java.time;

import java.time.chrono.ChronoPeriod;
import java.time.chrono.Chronology;
import java.time.chrono.IsoChronology;
import java.time.format.DateTimeParseException;
import java.time.temporal.ChronoUnit;
import java.time.temporal.Temporal;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalAmount;
import java.time.temporal.TemporalQueries;
import java.time.temporal.TemporalUnit;
import java.time.temporal.UnsupportedTemporalTypeException;
import java.util.List;
import java.util.Objects;

public final class Period implements ChronoPeriod, java.io.Serializable {
    private static final long serialVersionUID = -3587258372562876L;

    public static final Period ZERO = new Period(0, 0, 0);
    private static final List<TemporalUnit> SUPPORTED_UNITS = List.of(ChronoUnit.YEARS, ChronoUnit.MONTHS, ChronoUnit.DAYS);

    private final int years;
    private final int months;
    private final int days;

    private Period(int years, int months, int days) {
        this.years = years;
        this.months = months;
        this.days = days;
    }

    public static Period ofYears(int years) {
        return create(years, 0, 0);
    }

    public static Period ofMonths(int months) {
        return create(0, months, 0);
    }

    public static Period ofWeeks(int weeks) {
        return create(0, 0, Math.multiplyExact(weeks, 7));
    }

    public static Period ofDays(int days) {
        return create(0, 0, days);
    }

    public static Period of(int years, int months, int days) {
        return create(years, months, days);
    }

    public static Period from(TemporalAmount amount) {
        if (amount instanceof Period) return (Period) amount;
        if (amount instanceof ChronoPeriod) {
            if (!IsoChronology.INSTANCE.equals(((ChronoPeriod) amount).getChronology()))
                throw new DateTimeException("Period requires ISO chronology: " + amount);
        }
        Objects.requireNonNull(amount, "amount");
        int y = 0, m = 0, d = 0;
        for (TemporalUnit unit : amount.getUnits()) {
            long unitAmount = amount.get(unit);
            if (unit == ChronoUnit.YEARS) {
                y = Math.toIntExact(unitAmount);
            } else if (unit == ChronoUnit.MONTHS) {
                m = Math.toIntExact(unitAmount);
            } else if (unit == ChronoUnit.DAYS) {
                d = Math.toIntExact(unitAmount);
            } else {
                throw new DateTimeException("Unit must be Years, Months or Days, but was " + unit);
            }
        }
        return create(y, m, d);
    }

    /** End of [-+]?[0-9]+ at i, or -1. */
    private static int number(CharSequence t, int i) {
        int n = t.length(), j = i;
        if (j < n && (t.charAt(j) == '-' || t.charAt(j) == '+')) j++;
        int d = j;
        while (j < n && t.charAt(j) >= '0' && t.charAt(j) <= '9') j++;
        return j > d ? j : -1;
    }

    private static boolean letter(CharSequence t, int i, char upper) {
        return i < t.length() && (t.charAt(i) == upper || t.charAt(i) == (char) (upper + 32));
    }

    public static Period parse(CharSequence text) {
        Objects.requireNonNull(text, "text");
        int n = text.length(), i = 0;
        int signStart = 0, signEnd = 0;
        if (i < n && (text.charAt(i) == '-' || text.charAt(i) == '+')) {
            i++;
            signEnd = 1;
        }
        int[] g = {-1, -1, -1, -1, -1, -1, -1, -1};
        boolean ok = letter(text, i, 'P');
        if (ok) {
            i++;
            char[] units = {'Y', 'M', 'W', 'D'};
            for (int k = 0; k < 4; k++) {
                int e = number(text, i);
                if (e >= 0 && letter(text, e, units[k])) {
                    g[2 * k] = i;
                    g[2 * k + 1] = e;
                    i = e + 1;
                }
            }
            ok = i == n;
        }
        if (ok && (g[0] >= 0 || g[2] >= 0 || g[4] >= 0 || g[6] >= 0)) {
            int negate = (signEnd == signStart + 1 && text.charAt(signStart) == '-') ? -1 : 1;
            try {
                int y = parseNumber(text, g[0], g[1], negate);
                int m = parseNumber(text, g[2], g[3], negate);
                int w = parseNumber(text, g[4], g[5], negate);
                int d = parseNumber(text, g[6], g[7], negate);
                d = Math.addExact(d, Math.multiplyExact(w, 7));
                return create(y, m, d);
            } catch (NumberFormatException ex) {
                throw new DateTimeParseException("Text cannot be parsed to a Period", text, 0, ex);
            }
        }
        throw new DateTimeParseException("Text cannot be parsed to a Period", text, 0);
    }

    private static int parseNumber(CharSequence text, int start, int end, int negate) {
        if (start < 0 || end < 0) return 0;
        int val = Integer.parseInt(text, start, end, 10);
        try {
            return Math.multiplyExact(val, negate);
        } catch (ArithmeticException ex) {
            throw new DateTimeParseException("Text cannot be parsed to a Period", text, 0, ex);
        }
    }

    public static Period between(LocalDate startDateInclusive, LocalDate endDateExclusive) {
        return startDateInclusive.until(endDateExclusive);
    }

    private static Period create(int years, int months, int days) {
        if ((years | months | days) == 0) return ZERO;
        return new Period(years, months, days);
    }

    @Override
    public long get(TemporalUnit unit) {
        if (unit == ChronoUnit.YEARS) return getYears();
        if (unit == ChronoUnit.MONTHS) return getMonths();
        if (unit == ChronoUnit.DAYS) return getDays();
        throw new UnsupportedTemporalTypeException("Unsupported unit: " + unit);
    }

    @Override
    public List<TemporalUnit> getUnits() {
        return SUPPORTED_UNITS;
    }

    @Override
    public IsoChronology getChronology() {
        return IsoChronology.INSTANCE;
    }

    @Override
    public boolean isZero() {
        return this == ZERO;
    }

    @Override
    public boolean isNegative() {
        return years < 0 || months < 0 || days < 0;
    }

    public int getYears() {
        return years;
    }

    public int getMonths() {
        return months;
    }

    public int getDays() {
        return days;
    }

    public Period withYears(int years) {
        if (years == this.years) return this;
        return create(years, months, days);
    }

    public Period withMonths(int months) {
        if (months == this.months) return this;
        return create(years, months, days);
    }

    public Period withDays(int days) {
        if (days == this.days) return this;
        return create(years, months, days);
    }

    @Override
    public Period plus(TemporalAmount amountToAdd) {
        Period p = Period.from(amountToAdd);
        return create(Math.addExact(years, p.years), Math.addExact(months, p.months), Math.addExact(days, p.days));
    }

    public Period plusYears(long yearsToAdd) {
        if (yearsToAdd == 0) return this;
        return create(Math.toIntExact(Math.addExact(years, yearsToAdd)), months, days);
    }

    public Period plusMonths(long monthsToAdd) {
        if (monthsToAdd == 0) return this;
        return create(years, Math.toIntExact(Math.addExact(months, monthsToAdd)), days);
    }

    public Period plusDays(long daysToAdd) {
        if (daysToAdd == 0) return this;
        return create(years, months, Math.toIntExact(Math.addExact(days, daysToAdd)));
    }

    @Override
    public Period minus(TemporalAmount amountToSubtract) {
        Period p = Period.from(amountToSubtract);
        return create(Math.subtractExact(years, p.years), Math.subtractExact(months, p.months),
            Math.subtractExact(days, p.days));
    }

    public Period minusYears(long n) {
        return n == Long.MIN_VALUE ? plusYears(Long.MAX_VALUE).plusYears(1) : plusYears(-n);
    }

    public Period minusMonths(long n) {
        return n == Long.MIN_VALUE ? plusMonths(Long.MAX_VALUE).plusMonths(1) : plusMonths(-n);
    }

    public Period minusDays(long n) {
        return n == Long.MIN_VALUE ? plusDays(Long.MAX_VALUE).plusDays(1) : plusDays(-n);
    }

    @Override
    public Period multipliedBy(int scalar) {
        if (this == ZERO || scalar == 1) return this;
        return create(Math.multiplyExact(years, scalar), Math.multiplyExact(months, scalar), Math.multiplyExact(days, scalar));
    }

    @Override
    public Period negated() {
        return multipliedBy(-1);
    }

    @Override
    public Period normalized() {
        long totalMonths = toTotalMonths();
        long splitYears = totalMonths / 12;
        int splitMonths = (int) (totalMonths % 12);
        if (splitYears == years && splitMonths == months) return this;
        return create(Math.toIntExact(splitYears), splitMonths, days);
    }

    public long toTotalMonths() {
        return years * 12L + months;
    }

    @Override
    public Temporal addTo(Temporal temporal) {
        validateChrono(temporal);
        if (months == 0) {
            if (years != 0) temporal = temporal.plus(years, ChronoUnit.YEARS);
        } else {
            long totalMonths = toTotalMonths();
            if (totalMonths != 0) temporal = temporal.plus(totalMonths, ChronoUnit.MONTHS);
        }
        if (days != 0) temporal = temporal.plus(days, ChronoUnit.DAYS);
        return temporal;
    }

    @Override
    public Temporal subtractFrom(Temporal temporal) {
        validateChrono(temporal);
        if (months == 0) {
            if (years != 0) temporal = temporal.minus(years, ChronoUnit.YEARS);
        } else {
            long totalMonths = toTotalMonths();
            if (totalMonths != 0) temporal = temporal.minus(totalMonths, ChronoUnit.MONTHS);
        }
        if (days != 0) temporal = temporal.minus(days, ChronoUnit.DAYS);
        return temporal;
    }

    private void validateChrono(TemporalAccessor temporal) {
        Objects.requireNonNull(temporal, "temporal");
        Chronology c = temporal.query(TemporalQueries.chronology());
        if (c != null && !IsoChronology.INSTANCE.equals(c))
            throw new DateTimeException("Chronology mismatch, expected: ISO, actual: " + c.getId());
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Period)) return false;
        Period o = (Period) obj;
        return years == o.years && months == o.months && days == o.days;
    }

    @Override
    public int hashCode() {
        return years + Integer.rotateLeft(months, 8) + Integer.rotateLeft(days, 16);
    }

    @Override
    public String toString() {
        if (this == ZERO) return "P0D";
        StringBuilder buf = new StringBuilder();
        buf.append('P');
        if (years != 0) buf.append(years).append('Y');
        if (months != 0) buf.append(months).append('M');
        if (days != 0) buf.append(days).append('D');
        return buf.toString();
    }
}

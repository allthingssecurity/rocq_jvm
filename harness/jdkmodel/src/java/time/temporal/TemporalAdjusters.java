/* rocq-jvm model of java.time.temporal.TemporalAdjusters (clean-room, Apache-2.0): JDK 21's adjusters
 * as lambdas over the temporal's with/plus/minus/range/get, in the JDK's order of calls. */
package java.time.temporal;

import java.time.DayOfWeek;
import java.time.LocalDate;
import java.util.Objects;
import java.util.function.UnaryOperator;

public final class TemporalAdjusters {
    private TemporalAdjusters() {
    }

    public static TemporalAdjuster ofDateAdjuster(UnaryOperator<LocalDate> dateBasedAdjuster) {
        Objects.requireNonNull(dateBasedAdjuster, "dateBasedAdjuster");
        return (temporal) -> {
            LocalDate in = LocalDate.from(temporal);
            LocalDate out = dateBasedAdjuster.apply(in);
            return temporal.with(out);
        };
    }

    public static TemporalAdjuster firstDayOfMonth() {
        return (t) -> t.with(ChronoField.DAY_OF_MONTH, 1);
    }

    public static TemporalAdjuster lastDayOfMonth() {
        return (t) -> t.with(ChronoField.DAY_OF_MONTH, t.range(ChronoField.DAY_OF_MONTH).getMaximum());
    }

    public static TemporalAdjuster firstDayOfNextMonth() {
        return (t) -> t.with(ChronoField.DAY_OF_MONTH, 1).plus(1, ChronoUnit.MONTHS);
    }

    public static TemporalAdjuster firstDayOfYear() {
        return (t) -> t.with(ChronoField.DAY_OF_YEAR, 1);
    }

    public static TemporalAdjuster lastDayOfYear() {
        return (t) -> t.with(ChronoField.DAY_OF_YEAR, t.range(ChronoField.DAY_OF_YEAR).getMaximum());
    }

    public static TemporalAdjuster firstDayOfNextYear() {
        return (t) -> t.with(ChronoField.DAY_OF_YEAR, 1).plus(1, ChronoUnit.YEARS);
    }

    public static TemporalAdjuster firstInMonth(DayOfWeek dayOfWeek) {
        return dayOfWeekInMonth(1, dayOfWeek);
    }

    public static TemporalAdjuster lastInMonth(DayOfWeek dayOfWeek) {
        return dayOfWeekInMonth(-1, dayOfWeek);
    }

    public static TemporalAdjuster dayOfWeekInMonth(int ordinal, DayOfWeek dayOfWeek) {
        Objects.requireNonNull(dayOfWeek, "dayOfWeek");
        int dow = dayOfWeek.getValue();
        if (ordinal >= 0) {
            return (t) -> {
                Temporal first = t.with(ChronoField.DAY_OF_MONTH, 1);
                int cur = first.get(ChronoField.DAY_OF_WEEK);
                int diff = (dow - cur + 7) % 7;
                diff += (int) ((ordinal - 1L) * 7L);
                return first.plus(diff, ChronoUnit.DAYS);
            };
        }
        return (t) -> {
            Temporal last = t.with(ChronoField.DAY_OF_MONTH, t.range(ChronoField.DAY_OF_MONTH).getMaximum());
            int cur = last.get(ChronoField.DAY_OF_WEEK);
            int diff = dow - cur;
            diff = diff == 0 ? 0 : (diff > 0 ? diff - 7 : diff);
            diff -= (int) ((-ordinal - 1L) * 7L);
            return last.plus(diff, ChronoUnit.DAYS);
        };
    }

    public static TemporalAdjuster next(DayOfWeek dayOfWeek) {
        int dow = dayOfWeek.getValue();
        return (t) -> {
            int diff = t.get(ChronoField.DAY_OF_WEEK) - dow;
            return t.plus(diff >= 0 ? 7 - diff : -diff, ChronoUnit.DAYS);
        };
    }

    public static TemporalAdjuster nextOrSame(DayOfWeek dayOfWeek) {
        int dow = dayOfWeek.getValue();
        return (t) -> {
            int cal = t.get(ChronoField.DAY_OF_WEEK);
            if (cal == dow) return t;
            int diff = cal - dow;
            return t.plus(diff >= 0 ? 7 - diff : -diff, ChronoUnit.DAYS);
        };
    }

    public static TemporalAdjuster previous(DayOfWeek dayOfWeek) {
        int dow = dayOfWeek.getValue();
        return (t) -> {
            int diff = dow - t.get(ChronoField.DAY_OF_WEEK);
            return t.minus(diff >= 0 ? 7 - diff : -diff, ChronoUnit.DAYS);
        };
    }

    public static TemporalAdjuster previousOrSame(DayOfWeek dayOfWeek) {
        int dow = dayOfWeek.getValue();
        return (t) -> {
            int cal = t.get(ChronoField.DAY_OF_WEEK);
            if (cal == dow) return t;
            int diff = dow - cal;
            return t.minus(diff >= 0 ? 7 - diff : -diff, ChronoUnit.DAYS);
        };
    }
}

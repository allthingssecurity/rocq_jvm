/* rocq-jvm model of java.time.temporal.TemporalUnit (clean-room, Apache-2.0): JDK 21's default
 * isSupportedBy (the instanceof tests, then a trial plus(1)/plus(-1)). */
package java.time.temporal;

import java.time.Duration;
import java.time.LocalTime;
import java.time.chrono.ChronoLocalDate;
import java.time.chrono.ChronoLocalDateTime;
import java.time.chrono.ChronoZonedDateTime;

public interface TemporalUnit {
    Duration getDuration();

    boolean isDurationEstimated();

    boolean isDateBased();

    boolean isTimeBased();

    default boolean isSupportedBy(Temporal temporal) {
        if (temporal instanceof LocalTime) return isTimeBased();
        if (temporal instanceof ChronoLocalDate) return isDateBased();
        if (temporal instanceof ChronoLocalDateTime || temporal instanceof ChronoZonedDateTime) return true;
        try {
            temporal.plus(1, this);
            return true;
        } catch (UnsupportedTemporalTypeException ex) {
            return false;
        } catch (RuntimeException ex) {
            try {
                temporal.plus(-1, this);
                return true;
            } catch (RuntimeException ex2) {
                return false;
            }
        }
    }

    <R extends Temporal> R addTo(R temporal, long amount);

    long between(Temporal temporal1Inclusive, Temporal temporal2Exclusive);

    String toString();
}

/* rocq-jvm helper (not a JDK class): the chronology check of JDK 21's ChronoLocalDateImpl.ensureValid. */
package java.time.chrono;

import java.time.temporal.Temporal;

final class ChronoHelp {
    private ChronoHelp() {
    }

    static ChronoLocalDate ensureDate(Chronology chrono, Temporal temporal) {
        ChronoLocalDate other = (ChronoLocalDate) temporal;
        if (!chrono.equals(other.getChronology()))
            throw new ClassCastException("Chronology mismatch, expected: " + chrono.getId() + ", actual: "
                + other.getChronology().getId());
        return other;
    }
}

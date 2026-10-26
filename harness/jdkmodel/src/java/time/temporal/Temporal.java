/* rocq-jvm model of java.time.temporal.Temporal (clean-room, Apache-2.0): JDK 21's default methods. */
package java.time.temporal;

public interface Temporal extends TemporalAccessor {
    boolean isSupported(TemporalUnit unit);

    default Temporal with(TemporalAdjuster adjuster) {
        return adjuster.adjustInto(this);
    }

    Temporal with(TemporalField field, long newValue);

    default Temporal plus(TemporalAmount amount) {
        return amount.addTo(this);
    }

    Temporal plus(long amountToAdd, TemporalUnit unit);

    default Temporal minus(TemporalAmount amount) {
        return amount.subtractFrom(this);
    }

    default Temporal minus(long amountToSubtract, TemporalUnit unit) {
        if (amountToSubtract == Long.MIN_VALUE) return plus(Long.MAX_VALUE, unit).plus(1, unit);
        return plus(-amountToSubtract, unit);
    }

    long until(Temporal endExclusive, TemporalUnit unit);
}

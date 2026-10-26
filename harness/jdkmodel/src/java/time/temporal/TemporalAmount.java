/* rocq-jvm model of java.time.temporal.TemporalAmount (clean-room, Apache-2.0). */
package java.time.temporal;

import java.util.List;

public interface TemporalAmount {
    long get(TemporalUnit unit);

    List<TemporalUnit> getUnits();

    Temporal addTo(Temporal temporal);

    Temporal subtractFrom(Temporal temporal);
}

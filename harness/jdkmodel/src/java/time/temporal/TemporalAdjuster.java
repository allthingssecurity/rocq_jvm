/* rocq-jvm model of java.time.temporal.TemporalAdjuster (clean-room, Apache-2.0). */
package java.time.temporal;

@FunctionalInterface
public interface TemporalAdjuster {
    Temporal adjustInto(Temporal temporal);
}

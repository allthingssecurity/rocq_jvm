/* rocq-jvm model of java.time.temporal.TemporalQuery (clean-room, Apache-2.0). */
package java.time.temporal;

@FunctionalInterface
public interface TemporalQuery<R> {
    R queryFrom(TemporalAccessor temporal);
}

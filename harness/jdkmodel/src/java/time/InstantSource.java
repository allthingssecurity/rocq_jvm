/* rocq-jvm model of java.time.InstantSource (clean-room, Apache-2.0): JDK 21's fixed/offset/tick
 * sources and defaults; system() reads the host clock: STUCK. */
package java.time;

import java.util.Objects;

public interface InstantSource {
    static InstantSource system() {
        throw ModelStuckTime.unsupported("InstantSource.system: host clock");
    }

    static InstantSource tick(InstantSource baseSource, Duration tickDuration) {
        Objects.requireNonNull(baseSource, "baseSource");
        return Clock.tick(baseSource.withZone(ZoneOffset.UTC), tickDuration);
    }

    static InstantSource fixed(Instant fixedInstant) {
        return Clock.fixed(fixedInstant, ZoneOffset.UTC);
    }

    static InstantSource offset(InstantSource baseSource, Duration offsetDuration) {
        Objects.requireNonNull(baseSource, "baseSource");
        return Clock.offset(baseSource.withZone(ZoneOffset.UTC), offsetDuration);
    }

    Instant instant();

    default long millis() {
        return instant().toEpochMilli();
    }

    default Clock withZone(ZoneId zone) {
        return new Clock.SourceClock(this, zone);
    }
}

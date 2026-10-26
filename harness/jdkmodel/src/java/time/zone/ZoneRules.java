/*
 * rocq-jvm model of java.time.zone.ZoneRules (clean-room, Apache-2.0): only the fixed-offset rules
 * of JDK 21's ZoneRules.of(ZoneOffset) (no transitions: every query answers the offset, transitions
 * are null/empty, hashCode is the JDK's formula over the empty arrays, which is 1). Rules with
 * transitions (ZoneRules.of with transition lists, the tz database) are STUCK.
 */
package java.time.zone;

import java.time.Duration;
import java.time.Instant;
import java.time.LocalDateTime;
import java.time.ZoneOffset;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

public final class ZoneRules implements java.io.Serializable {
    private static final long serialVersionUID = 3044319355680032515L;
    private final ZoneOffset offset;

    private ZoneRules(ZoneOffset offset) {
        this.offset = offset;
    }

    public static ZoneRules of(ZoneOffset offset) {
        Objects.requireNonNull(offset, "offset");
        return new ZoneRules(offset);
    }

    public boolean isFixedOffset() {
        return true;
    }

    public ZoneOffset getOffset(Instant instant) {
        return offset;
    }

    public ZoneOffset getOffset(LocalDateTime localDateTime) {
        return offset;
    }

    public List<ZoneOffset> getValidOffsets(LocalDateTime localDateTime) {
        return Collections.singletonList(offset);
    }

    public ZoneOffset getStandardOffset(Instant instant) {
        return offset;
    }

    public Duration getDaylightSavings(Instant instant) {
        return Duration.ZERO;
    }

    public boolean isDaylightSavings(Instant instant) {
        return false;
    }

    public boolean isValidOffset(LocalDateTime localDateTime, ZoneOffset offset) {
        return this.offset.equals(offset);
    }

    public boolean equals(Object otherRules) {
        if (this == otherRules) return true;
        return (otherRules instanceof ZoneRules) && offset.equals(((ZoneRules) otherRules).offset);
    }

    public int hashCode() {
        return 1;
    }

    public String toString() {
        return "ZoneRules[currentStandardOffset=" + offset + "]";
    }
}

/*
 * rocq-jvm model of java.time.ZoneId (clean-room, Apache-2.0): JDK 21's of(String) dispatch (offsets,
 * the UTC/GMT/UT prefixes with their texts, the region-id syntax check) and ofOffset; only
 * fixed-offset zones are modelled. A region id that passes the syntax check needs the tz database
 * (ZoneRulesProvider): STUCK, as are systemDefault(), getAvailableZoneIds(), SHORT_IDS, of(id, map)
 * and getDisplayName.
 */
package java.time;

import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalQueries;
import java.time.zone.ZoneRules;
import java.util.Objects;

public abstract sealed class ZoneId implements java.io.Serializable permits ZoneOffset, ZoneRegion {
    private static final long serialVersionUID = 8352817235686L;

    ZoneId() {
    }

    public static ZoneId of(String zoneId) {
        return of(zoneId, true);
    }

    public static ZoneId ofOffset(String prefix, ZoneOffset offset) {
        Objects.requireNonNull(prefix, "prefix");
        Objects.requireNonNull(offset, "offset");
        if (prefix.isEmpty()) return offset;
        if (!prefix.equals("GMT") && !prefix.equals("UTC") && !prefix.equals("UT"))
            throw new IllegalArgumentException("prefix should be GMT, UTC or UT, is: " + prefix);
        if (offset.getTotalSeconds() != 0) prefix = prefix.concat(offset.getId());
        return new ZoneRegion(prefix, offset.getRules());
    }

    static ZoneId of(String zoneId, boolean checkAvailable) {
        Objects.requireNonNull(zoneId, "zoneId");
        if (zoneId.length() <= 1 || zoneId.startsWith("+") || zoneId.startsWith("-")) return ZoneOffset.of(zoneId);
        if (zoneId.startsWith("UTC") || zoneId.startsWith("GMT")) return ofWithPrefix(zoneId, 3, checkAvailable);
        if (zoneId.startsWith("UT")) return ofWithPrefix(zoneId, 2, checkAvailable);
        return ZoneRegion.ofId(zoneId, checkAvailable);
    }

    private static ZoneId ofWithPrefix(String zoneId, int prefixLength, boolean checkAvailable) {
        String prefix = zoneId.substring(0, prefixLength);
        if (zoneId.length() == prefixLength) return ofOffset(prefix, ZoneOffset.UTC);
        if (zoneId.charAt(prefixLength) != '+' && zoneId.charAt(prefixLength) != '-')
            return ZoneRegion.ofId(zoneId, checkAvailable);
        try {
            ZoneOffset offset = ZoneOffset.of(zoneId.substring(prefixLength));
            return ofOffset(prefix, offset);
        } catch (DateTimeException ex) {
            throw new DateTimeException("Invalid ID for offset-based ZoneId: " + zoneId, ex);
        }
    }

    public static ZoneId from(TemporalAccessor temporal) {
        ZoneId obj = temporal.query(TemporalQueries.zone());
        if (obj == null)
            throw new DateTimeException("Unable to obtain ZoneId from TemporalAccessor: " + temporal + " of type "
                + temporal.getClass().getName());
        return obj;
    }

    public abstract String getId();

    public abstract ZoneRules getRules();

    public ZoneId normalized() {
        ZoneRules rules = getRules();
        if (rules.isFixedOffset()) return rules.getOffset(Instant.EPOCH);
        return this;
    }

    abstract ZoneOffset getOffset(long epochSecond);

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        return (obj instanceof ZoneId) && getId().equals(((ZoneId) obj).getId());
    }

    @Override
    public int hashCode() {
        return getId().hashCode();
    }

    @Override
    public String toString() {
        return getId();
    }
}

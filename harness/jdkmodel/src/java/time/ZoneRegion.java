/* rocq-jvm model of java.time.ZoneRegion (clean-room, Apache-2.0): the JDK 21 class for region ids;
 * only the fixed-offset regions that ZoneId.of / ofOffset build without the tz database ("UTC",
 * "GMT+02:00", ...) are modelled. ofId checks the id syntax with the JDK's text, then needs the tz
 * database: STUCK. */
package java.time;

import java.time.zone.ZoneRules;
import java.util.Objects;

final class ZoneRegion extends ZoneId implements java.io.Serializable {
    private static final long serialVersionUID = 8386373296231747096L;
    private final String id;
    private final transient ZoneRules rules;

    ZoneRegion(String id, ZoneRules rules) {
        this.id = id;
        this.rules = rules;
    }

    static ZoneRegion ofId(String zoneId, boolean checkAvailable) {
        Objects.requireNonNull(zoneId, "zoneId");
        checkName(zoneId);
        throw ModelStuckTime.unsupported("ZoneId.of: region ids need the tz database");
    }

    private static void checkName(String zoneId) {
        int n = zoneId.length();
        if (n < 2) throw new DateTimeException("Invalid ID for region-based ZoneId, invalid format: " + zoneId);
        for (int i = 0; i < n; i++) {
            char c = zoneId.charAt(i);
            if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) continue;
            if (i != 0 && ((c >= '0' && c <= '9') || c == '/' || c == '~' || c == '.' || c == '_' || c == '+' || c == '-'))
                continue;
            throw new DateTimeException("Invalid ID for region-based ZoneId, invalid format: " + zoneId);
        }
    }

    @Override
    public String getId() {
        return id;
    }

    @Override
    public ZoneRules getRules() {
        return rules;
    }

    @Override
    ZoneOffset getOffset(long epochSecond) {
        return getRules().getOffset(Instant.ofEpochSecond(epochSecond));
    }
}

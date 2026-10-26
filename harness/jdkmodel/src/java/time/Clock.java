/*
 * rocq-jvm model of java.time.Clock (clean-room, Apache-2.0): JDK 21's fixed, offset, tick and
 * source clocks (texts, equals, hashCode, toString), which make now(Clock) deterministic. The system
 * clocks (systemUTC, systemDefaultZone, system, tickMillis/Seconds/Minutes) read the host clock and
 * zone: STUCK. equals/hashCode of Clock itself are Object's (identity, TRUST.md 5c).
 */
package java.time;

import java.util.Objects;

public abstract class Clock implements InstantSource {
    public static Clock systemUTC() {
        throw ModelStuckTime.unsupported("Clock.systemUTC: host clock");
    }

    public static Clock systemDefaultZone() {
        throw ModelStuckTime.unsupported("Clock.systemDefaultZone: host clock and zone");
    }

    public static Clock system(ZoneId zone) {
        Objects.requireNonNull(zone, "zone");
        throw ModelStuckTime.unsupported("Clock.system: host clock");
    }

    public static Clock tickMillis(ZoneId zone) {
        return system(zone);
    }

    public static Clock tickSeconds(ZoneId zone) {
        return system(zone);
    }

    public static Clock tickMinutes(ZoneId zone) {
        return system(zone);
    }

    public static Clock tick(Clock baseClock, Duration tickDuration) {
        Objects.requireNonNull(baseClock, "baseClock");
        Objects.requireNonNull(tickDuration, "tickDuration");
        if (tickDuration.isNegative()) throw new IllegalArgumentException("Tick duration must not be negative");
        long tickNanos = tickDuration.toNanos();
        if (tickNanos % 1000_000 != 0 && 1000_000_000 % tickNanos != 0)
            throw new IllegalArgumentException("Invalid tick duration");
        if (tickNanos <= 1) return baseClock;
        return new TickClock(baseClock, tickNanos);
    }

    public static Clock fixed(Instant fixedInstant, ZoneId zone) {
        Objects.requireNonNull(fixedInstant, "fixedInstant");
        Objects.requireNonNull(zone, "zone");
        return new FixedClock(fixedInstant, zone);
    }

    public static Clock offset(Clock baseClock, Duration offsetDuration) {
        Objects.requireNonNull(baseClock, "baseClock");
        Objects.requireNonNull(offsetDuration, "offsetDuration");
        if (offsetDuration.equals(Duration.ZERO)) return baseClock;
        return new OffsetClock(baseClock, offsetDuration);
    }

    protected Clock() {
    }

    public abstract ZoneId getZone();

    @Override
    public abstract Clock withZone(ZoneId zone);

    @Override
    public long millis() {
        return instant().toEpochMilli();
    }

    @Override
    public abstract Instant instant();

    @Override
    public boolean equals(Object obj) {
        return super.equals(obj);
    }

    @Override
    public int hashCode() {
        return super.hashCode();
    }

    static final class FixedClock extends Clock implements java.io.Serializable {
        private static final long serialVersionUID = 7430389292664866958L;
        private final Instant instant;
        private final ZoneId zone;

        FixedClock(Instant fixedInstant, ZoneId zone) {
            this.instant = fixedInstant;
            this.zone = zone;
        }

        @Override
        public ZoneId getZone() {
            return zone;
        }

        @Override
        public Clock withZone(ZoneId zone) {
            if (zone.equals(this.zone)) return this;
            return new FixedClock(instant, zone);
        }

        @Override
        public long millis() {
            return instant.toEpochMilli();
        }

        @Override
        public Instant instant() {
            return instant;
        }

        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof FixedClock)) return false;
            FixedClock o = (FixedClock) obj;
            return instant.equals(o.instant) && zone.equals(o.zone);
        }

        @Override
        public int hashCode() {
            return instant.hashCode() ^ zone.hashCode();
        }

        @Override
        public String toString() {
            return "FixedClock[" + instant + "," + zone + "]";
        }
    }

    static final class OffsetClock extends Clock implements java.io.Serializable {
        private static final long serialVersionUID = 2007484719125426256L;
        private final Clock baseClock;
        private final Duration offset;

        OffsetClock(Clock baseClock, Duration offset) {
            this.baseClock = baseClock;
            this.offset = offset;
        }

        @Override
        public ZoneId getZone() {
            return baseClock.getZone();
        }

        @Override
        public Clock withZone(ZoneId zone) {
            if (zone.equals(baseClock.getZone())) return this;
            return new OffsetClock(baseClock.withZone(zone), offset);
        }

        @Override
        public long millis() {
            return Math.addExact(baseClock.millis(), offset.toMillis());
        }

        @Override
        public Instant instant() {
            return baseClock.instant().plus(offset);
        }

        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof OffsetClock)) return false;
            OffsetClock o = (OffsetClock) obj;
            return baseClock.equals(o.baseClock) && offset.equals(o.offset);
        }

        @Override
        public int hashCode() {
            return baseClock.hashCode() ^ offset.hashCode();
        }

        @Override
        public String toString() {
            return "OffsetClock[" + baseClock + "," + offset + "]";
        }
    }

    static final class TickClock extends Clock implements java.io.Serializable {
        private static final long serialVersionUID = 6504659149906368850L;
        private final Clock baseClock;
        private final long tickNanos;

        TickClock(Clock baseClock, long tickNanos) {
            this.baseClock = baseClock;
            this.tickNanos = tickNanos;
        }

        @Override
        public ZoneId getZone() {
            return baseClock.getZone();
        }

        @Override
        public Clock withZone(ZoneId zone) {
            if (zone.equals(baseClock.getZone())) return this;
            return new TickClock(baseClock.withZone(zone), tickNanos);
        }

        @Override
        public long millis() {
            long millis = baseClock.millis();
            return millis - Math.floorMod(millis, tickNanos / 1000_000L);
        }

        @Override
        public Instant instant() {
            if ((tickNanos % 1000_000) == 0) {
                long millis = baseClock.millis();
                return Instant.ofEpochMilli(millis - Math.floorMod(millis, tickNanos / 1000_000L));
            }
            Instant instant = baseClock.instant();
            long nanos = instant.getNano();
            long adjust = Math.floorMod(nanos, tickNanos);
            return instant.minusNanos(adjust);
        }

        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof TickClock)) return false;
            TickClock o = (TickClock) obj;
            return tickNanos == o.tickNanos && baseClock.equals(o.baseClock);
        }

        @Override
        public int hashCode() {
            return baseClock.hashCode() ^ ((int) (tickNanos ^ (tickNanos >>> 32)));
        }

        @Override
        public String toString() {
            return "TickClock[" + baseClock + "," + Duration.ofNanos(tickNanos) + "]";
        }
    }

    static final class SourceClock extends Clock implements java.io.Serializable {
        private static final long serialVersionUID = 235386528762398L;
        private final InstantSource baseSource;
        private final ZoneId zone;

        SourceClock(InstantSource baseSource, ZoneId zone) {
            this.baseSource = baseSource;
            this.zone = zone;
        }

        @Override
        public ZoneId getZone() {
            return zone;
        }

        @Override
        public Clock withZone(ZoneId zone) {
            if (zone.equals(this.zone)) return this;
            return new SourceClock(baseSource, zone);
        }

        @Override
        public long millis() {
            return baseSource.millis();
        }

        @Override
        public Instant instant() {
            return baseSource.instant();
        }

        @Override
        public boolean equals(Object obj) {
            if (!(obj instanceof SourceClock)) return false;
            SourceClock o = (SourceClock) obj;
            return zone.equals(o.zone) && baseSource.equals(o.baseSource);
        }

        @Override
        public int hashCode() {
            return baseSource.hashCode() ^ zone.hashCode();
        }

        @Override
        public String toString() {
            return "SourceClock[" + baseSource + "," + zone + "]";
        }
    }
}

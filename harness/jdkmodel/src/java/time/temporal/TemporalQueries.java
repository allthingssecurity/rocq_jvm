/* rocq-jvm model of java.time.temporal.TemporalQueries (clean-room, Apache-2.0): the seven queries of
 * JDK 21 (anonymous classes in the JDK's order, with their toString). */
package java.time.temporal;

import java.time.LocalDate;
import java.time.LocalTime;
import java.time.ZoneId;
import java.time.ZoneOffset;
import java.time.chrono.Chronology;

public final class TemporalQueries {
    private TemporalQueries() {
    }

    public static TemporalQuery<ZoneId> zoneId() {
        return ZONE_ID;
    }

    public static TemporalQuery<Chronology> chronology() {
        return CHRONO;
    }

    public static TemporalQuery<TemporalUnit> precision() {
        return PRECISION;
    }

    public static TemporalQuery<ZoneId> zone() {
        return ZONE;
    }

    public static TemporalQuery<ZoneOffset> offset() {
        return OFFSET;
    }

    public static TemporalQuery<LocalDate> localDate() {
        return LOCAL_DATE;
    }

    public static TemporalQuery<LocalTime> localTime() {
        return LOCAL_TIME;
    }

    static final TemporalQuery<ZoneId> ZONE_ID = new TemporalQuery<>() {
        public ZoneId queryFrom(TemporalAccessor temporal) {
            return temporal.query(TemporalQueries.ZONE_ID);
        }

        public String toString() {
            return "ZoneId";
        }
    };

    static final TemporalQuery<Chronology> CHRONO = new TemporalQuery<>() {
        public Chronology queryFrom(TemporalAccessor temporal) {
            return temporal.query(TemporalQueries.CHRONO);
        }

        public String toString() {
            return "Chronology";
        }
    };

    static final TemporalQuery<TemporalUnit> PRECISION = new TemporalQuery<>() {
        public TemporalUnit queryFrom(TemporalAccessor temporal) {
            return temporal.query(TemporalQueries.PRECISION);
        }

        public String toString() {
            return "Precision";
        }
    };

    static final TemporalQuery<ZoneOffset> OFFSET = new TemporalQuery<>() {
        public ZoneOffset queryFrom(TemporalAccessor temporal) {
            if (temporal.isSupported(ChronoField.OFFSET_SECONDS))
                return ZoneOffset.ofTotalSeconds(temporal.get(ChronoField.OFFSET_SECONDS));
            return null;
        }

        public String toString() {
            return "ZoneOffset";
        }
    };

    static final TemporalQuery<ZoneId> ZONE = new TemporalQuery<>() {
        public ZoneId queryFrom(TemporalAccessor temporal) {
            ZoneId z = temporal.query(ZONE_ID);
            return z != null ? z : temporal.query(OFFSET);
        }

        public String toString() {
            return "Zone";
        }
    };

    static final TemporalQuery<LocalDate> LOCAL_DATE = new TemporalQuery<>() {
        public LocalDate queryFrom(TemporalAccessor temporal) {
            if (temporal.isSupported(ChronoField.EPOCH_DAY))
                return LocalDate.ofEpochDay(temporal.getLong(ChronoField.EPOCH_DAY));
            return null;
        }

        public String toString() {
            return "LocalDate";
        }
    };

    static final TemporalQuery<LocalTime> LOCAL_TIME = new TemporalQuery<>() {
        public LocalTime queryFrom(TemporalAccessor temporal) {
            if (temporal.isSupported(ChronoField.NANO_OF_DAY))
                return LocalTime.ofNanoOfDay(temporal.getLong(ChronoField.NANO_OF_DAY));
            return null;
        }

        public String toString() {
            return "LocalTime";
        }
    };
}

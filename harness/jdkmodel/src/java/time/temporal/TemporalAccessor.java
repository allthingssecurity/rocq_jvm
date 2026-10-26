/* rocq-jvm model of java.time.temporal.TemporalAccessor (clean-room, Apache-2.0): the JDK 21 default
 * methods range/get/query (UnsupportedTemporalTypeException / DateTimeException texts as in JDK 21). */
package java.time.temporal;

import java.time.DateTimeException;
import java.util.Objects;

public interface TemporalAccessor {
    boolean isSupported(TemporalField field);

    default ValueRange range(TemporalField field) {
        if (field instanceof ChronoField) {
            if (!isSupported(field)) throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
            return field.range();
        }
        Objects.requireNonNull(field, "field");
        return field.rangeRefinedBy(this);
    }

    default int get(TemporalField field) {
        ValueRange r = range(field);
        if (!r.isIntValue())
            throw new UnsupportedTemporalTypeException("Invalid field " + field + " for get() method, use getLong() instead");
        long v = getLong(field);
        if (!r.isValidValue(v))
            throw new DateTimeException("Invalid value for " + field + " (valid values " + r + "): " + v);
        return (int) v;
    }

    long getLong(TemporalField field);

    default <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.zoneId() || query == TemporalQueries.chronology() || query == TemporalQueries.precision())
            return null;
        return query.queryFrom(this);
    }
}

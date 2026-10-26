/* rocq-jvm model of java.time.chrono.Era (clean-room, Apache-2.0): JDK 21's default methods;
 * getDisplayName goes through the model DateTimeFormatterBuilder (English text only). */
package java.time.chrono;

import java.time.format.DateTimeFormatterBuilder;
import java.time.format.TextStyle;
import java.time.temporal.ChronoField;
import java.time.temporal.ChronoUnit;
import java.time.temporal.Temporal;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalAdjuster;
import java.time.temporal.TemporalField;
import java.time.temporal.TemporalQueries;
import java.time.temporal.TemporalQuery;
import java.time.temporal.UnsupportedTemporalTypeException;
import java.time.temporal.ValueRange;
import java.util.Locale;

public interface Era extends TemporalAccessor, TemporalAdjuster {
    int getValue();

    @Override
    default boolean isSupported(TemporalField field) {
        if (field instanceof ChronoField) return field == ChronoField.ERA;
        return field != null && field.isSupportedBy(this);
    }

    @Override
    default ValueRange range(TemporalField field) {
        return TemporalAccessor.super.range(field);
    }

    @Override
    default int get(TemporalField field) {
        if (field == ChronoField.ERA) return getValue();
        return TemporalAccessor.super.get(field);
    }

    @Override
    default long getLong(TemporalField field) {
        if (field == ChronoField.ERA) return getValue();
        if (field instanceof ChronoField) throw new UnsupportedTemporalTypeException("Unsupported field: " + field);
        return field.getFrom(this);
    }

    @Override
    @SuppressWarnings("unchecked")
    default <R> R query(TemporalQuery<R> query) {
        if (query == TemporalQueries.precision()) return (R) ChronoUnit.ERAS;
        return TemporalAccessor.super.query(query);
    }

    @Override
    default Temporal adjustInto(Temporal temporal) {
        return temporal.with(ChronoField.ERA, getValue());
    }

    default String getDisplayName(TextStyle style, Locale locale) {
        return new DateTimeFormatterBuilder().appendText(ChronoField.ERA, style).toFormatter(locale).format(this);
    }
}

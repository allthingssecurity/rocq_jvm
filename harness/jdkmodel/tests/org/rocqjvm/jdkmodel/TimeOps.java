package org.rocqjvm.jdkmodel;

import java.time.DateTimeException;
import java.time.DayOfWeek;
import java.time.Duration;
import java.time.Instant;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.LocalTime;
import java.time.Month;
import java.time.OffsetDateTime;
import java.time.Period;
import java.time.ZoneId;
import java.time.ZoneOffset;
import java.time.ZonedDateTime;
import java.time.chrono.ChronoLocalDate;
import java.time.chrono.IsoChronology;
import java.time.format.DateTimeFormatter;
import java.time.format.DateTimeFormatterBuilder;
import java.time.format.DateTimeParseException;
import java.time.format.ResolverStyle;
import java.time.format.SignStyle;
import java.time.format.TextStyle;
import java.time.temporal.ChronoField;
import java.time.temporal.ChronoUnit;
import java.time.temporal.Temporal;
import java.time.temporal.TemporalAccessor;
import java.time.temporal.TemporalAdjuster;
import java.time.temporal.TemporalAdjusters;
import java.time.temporal.TemporalQueries;
import java.time.temporal.ValueRange;
import java.util.Locale;

/** Differential tests of the java.time model: Instant, LocalDate, LocalTime, LocalDateTime, ZoneOffset,
 *  OffsetDateTime, ZonedDateTime (fixed offsets), Period, ChronoField/ChronoUnit/ValueRange,
 *  TemporalAdjusters and DateTimeFormatter (ISO formatters, ofPattern in English, parse errors),
 *  over random values incl. the extremes, invalid fields and malformed text. */
public final class TimeOps {
    private TimeOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static long big() {
        switch (r(10)) {
            case 0: return Long.MAX_VALUE - r(3);
            case 1: return Long.MIN_VALUE + r(3);
            case 2: return r(2000) - 1000;
            case 3: return (long) (r(2000000) - 1000000) * 1000003L;
            case 4: return 0;
            case 5: return (long) (r(2000000) - 1000000) * 86400L;
            case 6: return (long) (r(2000000) - 1000000) * 31556952000L;
            case 7: return r(2) == 0 ? 31556889864403199L - r(1000) : -31557014167219200L + r(1000);
            default: return r(1000000) - 500000;
        }
    }

    static int year() {
        switch (r(8)) {
            case 0: return r(2) == 0 ? 999_999_999 - r(3) : -999_999_999 + r(3);
            case 1: return r(20000) - 10000;
            case 2: return r(40) - 20;
            case 3: return 1_000_000_000;
            case 4: return 9999 + r(3);
            default: return 1900 + r(250);
        }
    }

    /** Set by the tests whose parsed text can have several conflicting or invalid fields: which of them the
     *  resolver reports follows the HashMap order of the ChronoField keys, i.e. identity hash codes. */
    static boolean fuzzy;

    static String fz(String m) {
        if (!fuzzy || m == null) return m;
        int c = m.indexOf("Conflict found: Field ");
        if (c >= 0) {
            int d = m.indexOf(" derived from ", c);
            return m.substring(0, c) + "Conflict found: Field ..." + (d >= 0 ? m.substring(d) : "");
        }
        int v = m.indexOf("Invalid value for ");
        if (v >= 0 && m.indexOf("could not be parsed:") >= 0) return m.substring(0, v) + "Invalid value ...";
        if (v >= 0 && m.indexOf("Text '") < 0 && x0) return "Invalid value ...";
        return m;
    }

    static boolean x0;

    static String exc(Throwable x) {
        if (x instanceof ClassCastException) return "!" + x.getClass().getName();
        String m = fz(x.getMessage());
        String out = "!" + x.getClass().getName() + ":" + norm(m);
        if (x instanceof DateTimeParseException) {
            DateTimeParseException p = (DateTimeParseException) x;
            out += "@" + p.getErrorIndex() + "<" + p.getParsedString() + ">";
        }
        if (x.getCause() != null) {
            x0 = x instanceof DateTimeParseException;
            out += "(cause " + x.getCause().getClass().getName() + ":" + norm(fz(x.getCause().getMessage())) + ")";
            x0 = false;
        }
        return out;
    }

    /** Sorts the entries of a printed HashMap of parsed fields ("{A=1, B=2}"): their order follows
     *  identity hash codes. */
    static String norm(String m) {
        if (m == null) return "null";
        int a = m.indexOf('{');
        int b = m.indexOf('}', a + 1);
        if (a < 0 || b < 0) return m;
        String[] parts = m.substring(a + 1, b).split(", ");
        java.util.Arrays.sort(parts);
        return m.substring(0, a + 1) + String.join(", ", parts) + m.substring(b);
    }

    static final ChronoUnit[] UNITS = ChronoUnit.values();
    static final ChronoField[] FIELDS = ChronoField.values();

    static Instant inst() {
        switch (r(6)) {
            case 0: return Instant.ofEpochSecond(big(), big());
            case 1: return Instant.ofEpochMilli(big());
            case 2: return Instant.ofEpochSecond(big());
            case 3: return r(2) == 0 ? Instant.MAX : Instant.MIN;
            case 4: return Instant.EPOCH.plusNanos(big());
            default: return Instant.ofEpochSecond(r(2000000000) - 1000000000L, r(1000000000));
        }
    }

    public static String instant(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                Instant a = inst();
                out.append(a).append('|').append(a.getEpochSecond()).append(',').append(a.getNano()).append('|');
                Instant b = inst();
                ChronoUnit u = UNITS[r(UNITS.length)];
                switch (r(12)) {
                    case 0: out.append(a.plus(r(2000) - 1000, u)).append(a.minus(big(), u)); break;
                    case 1: out.append(a.until(b, u)); break;
                    case 2: out.append(a.truncatedTo(UNITS[r(9)])); break;
                    case 3: out.append(a.compareTo(b)).append(a.isBefore(b)).append(a.isAfter(b)).append(a.equals(b)).append(a.hashCode()); break;
                    case 4: out.append(a.toEpochMilli()); break;
                    case 5: out.append(a.plusSeconds(big())).append(a.plusMillis(big())).append(a.minusNanos(big())); break;
                    case 6: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.isSupported(f)).append(a.getLong(f)).append(a.get(f)); break; }
                    case 7: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.with(f, big() % 2000000)); break; }
                    case 8: out.append(a.atOffset(ZoneOffset.ofTotalSeconds(r(129601) - 64800))).append(a.atZone(ZoneOffset.UTC)); break;
                    case 9: out.append(Duration.between(a, b)).append(a.plus(Duration.ofSeconds(r(1000), big()))); break;
                    case 10: out.append(a.isSupported(u)).append(a.range(FIELDS[r(FIELDS.length)])); break;
                    default: out.append(Instant.parse(a.toString())).append(a.toString().length()); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String[] ITEXTS = {"2024-01-01T00:00:00Z", "2024-01-01T00:00:00.5+01:00", "+12024-01-01T00:00:00Z",
        "-0001-12-31T23:59:59Z", "2024-02-30T00:00:00Z", "2024-01-01T24:00:00Z", "2024-12-31T23:59:60Z",
        "2024-01-01t10:15:30z", "2024-01-01T10:15Z", "2024-01-01T10:15:30.123456789123Z", "x", "",
        "+1000000000-12-31T23:59:59.999999999Z", "-1000000000-01-01T00:00:00Z", "2024-01-01T10:15:30+18:00",
        "2024-01-01T10:15:30+19:00", "2024-01-01T10:15:30-03:30:15", "2024-01-01T10:15:30.Z", "2024-1-01T10:15:30Z"};

    public static String instantParse(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            String t;
            if (r(3) == 0) {
                t = ITEXTS[r(ITEXTS.length)];
            } else {
                try {
                    t = inst().toString();
                } catch (RuntimeException x) {
                    t = "1970-01-01T00:00:00Z";
                }
                if (r(2) == 0) {
                    int i = r(t.length());
                    t = t.substring(0, i) + "0+-:.TZ1x".charAt(r(9)) + t.substring(i + (r(2) == 0 ? 1 : 0));
                }
            }
            try {
                Instant i = Instant.parse(t);
                out.append(i).append('/').append(i.getEpochSecond()).append(',').append(i.getNano());
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static LocalDate ld() {
        switch (r(6)) {
            case 0: return LocalDate.of(year(), r(14), r(33));
            case 1: return LocalDate.ofEpochDay(r(2) == 0 ? big() % 400000000000L : r(2000000) - 1000000);
            case 2: return LocalDate.ofYearDay(year(), r(368));
            case 3: return r(2) == 0 ? LocalDate.MAX : LocalDate.MIN;
            case 4: return LocalDate.of(year(), Month.of(1 + r(12)), 1 + r(31));
            default: return LocalDate.of(1900 + r(250), 1 + r(12), 1 + r(28));
        }
    }

    static TemporalAdjuster adj() {
        DayOfWeek d = DayOfWeek.of(1 + r(7));
        switch (r(12)) {
            case 0: return TemporalAdjusters.firstDayOfMonth();
            case 1: return TemporalAdjusters.lastDayOfMonth();
            case 2: return TemporalAdjusters.firstDayOfNextMonth();
            case 3: return TemporalAdjusters.firstDayOfYear();
            case 4: return TemporalAdjusters.lastDayOfYear();
            case 5: return TemporalAdjusters.firstDayOfNextYear();
            case 6: return TemporalAdjusters.next(d);
            case 7: return TemporalAdjusters.previous(d);
            case 8: return TemporalAdjusters.nextOrSame(d);
            case 9: return TemporalAdjusters.previousOrSame(d);
            case 10: return TemporalAdjusters.dayOfWeekInMonth(r(11) - 5, d);
            default: return r(2) == 0 ? TemporalAdjusters.firstInMonth(d) : TemporalAdjusters.lastInMonth(d);
        }
    }

    public static String date(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                LocalDate a = ld();
                out.append(a).append('|').append(a.getDayOfWeek()).append(a.getDayOfYear()).append(',').append(a.lengthOfMonth())
                    .append(a.isLeapYear()).append(a.toEpochDay()).append(a.hashCode()).append('|');
                long n = r(3) == 0 ? big() : r(2000) - 1000;
                switch (r(14)) {
                    case 0: out.append(a.plusDays(n)).append(a.minusDays(n)); break;
                    case 1: out.append(a.plusMonths(n)).append(a.minusMonths(r(30))); break;
                    case 2: out.append(a.plusYears(n)).append(a.plusWeeks(n)); break;
                    case 3: out.append(a.plus(n, UNITS[r(UNITS.length)])); break;
                    case 4: { LocalDate b = ld(); out.append(a.until(b, UNITS[r(UNITS.length)])).append(a.until(b)).append(a.compareTo(b))
                        .append(a.isBefore(b)).append(a.isEqual(b)).append(a.equals(b)); break; }
                    case 5: out.append(a.withYear(year())).append(a.withMonth(r(14))).append(a.withDayOfMonth(r(33))); break;
                    case 6: out.append(a.withDayOfYear(r(368))); break;
                    case 7: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.with(f, r(4) == 0 ? big() : r(60) - 5)); break; }
                    case 8: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.isSupported(f)).append(a.range(f)).append(a.getLong(f)).append(a.get(f)); break; }
                    case 9: out.append(a.with(adj())); break;
                    case 10: out.append(a.plus(Period.of(r(200) - 100, r(30) - 15, r(70) - 35))).append(a.minus(Period.ofWeeks(r(10)))); break;
                    case 11: out.append(a.atTime(r(25), r(61))).append(a.atStartOfDay()).append(a.atStartOfDay(ZoneOffset.ofHours(r(37) - 18))); break;
                    case 12: { LocalDate b = a.plusDays(r(40) - 5); StringBuilder c = new StringBuilder();
                        a.datesUntil(b).forEach(d -> c.append(d.getDayOfMonth()).append(' ')); out.append(c); break; }
                    default: out.append(a.getEra()).append(a.getChronology()).append(a.lengthOfYear()).append(a.query(TemporalQueries.precision()))
                        .append(a.format(DateTimeFormatter.ISO_LOCAL_DATE)).append(a.format(DateTimeFormatter.BASIC_ISO_DATE)); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String[] DTEXTS = {"2024-13-01", "x", "2024-02-30", "2024-01-01x", "+2024-01-01", "+12024-01-01",
        "12024-01-01", "-0001-01-01", "-12024-01-01", "2023-02-29", "2024-02-29", "2024-04-31", "0000-01-01", "2024-1-1",
        "20240101", "2024-00-10", "2024-06-00", "-999999999-01-01", "+999999999-12-31", "+1000000000-01-01", "2024-01-01T",
        "２０２４-01-01", "2024-01-01+01:00", "2024-001", "2024-366", "2023-366", "20241301", "20240101Z", "20240101+0130"};

    public static String dateParse(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            String t;
            int f = r(5);
            if (r(2) == 0) {
                t = DTEXTS[r(DTEXTS.length)];
            } else {
                try {
                    LocalDate d = ld();
                    t = f == 1 ? d.format(DateTimeFormatter.BASIC_ISO_DATE) : f == 3 ? d.format(DateTimeFormatter.ISO_ORDINAL_DATE) : d.toString();
                } catch (RuntimeException x) {
                    t = "2000-01-01";
                }
                if (r(2) == 0) {
                    int i = r(t.length());
                    t = t.substring(0, i) + "0+-:9Z1x".charAt(r(8)) + t.substring(i + (r(2) == 0 ? 1 : 0));
                }
            }
            try {
                switch (f) {
                    case 0: out.append(LocalDate.parse(t)); break;
                    case 1: out.append(LocalDate.parse(t, DateTimeFormatter.BASIC_ISO_DATE)); break;
                    case 2: out.append(LocalDate.parse(t, DateTimeFormatter.ISO_DATE)); break;
                    case 3: out.append(LocalDate.parse(t, DateTimeFormatter.ISO_ORDINAL_DATE)); break;
                    default: out.append(LocalDate.parse(t, DateTimeFormatter.ISO_LOCAL_DATE.withResolverStyle(ResolverStyle.values()[r(3)]))); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static LocalTime lt() {
        switch (r(5)) {
            case 0: return LocalTime.of(r(26) - 1, r(62) - 1);
            case 1: return LocalTime.of(r(25), r(61), r(61), r(3) == 0 ? r(1000) * 1000000 : r(1000000000));
            case 2: return LocalTime.ofSecondOfDay(r(86401));
            case 3: return LocalTime.ofNanoOfDay((long) r(86400) * 1000000000L + r(1000000000));
            default: return LocalTime.of(r(24), r(60), r(2) == 0 ? 0 : r(60));
        }
    }

    public static String time(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                LocalTime a = lt();
                out.append(a).append('|').append(a.toSecondOfDay()).append(',').append(a.toNanoOfDay()).append(a.hashCode()).append('|');
                long n = r(3) == 0 ? big() : r(200000) - 100000;
                switch (r(10)) {
                    case 0: out.append(a.plusHours(n)).append(a.plusMinutes(n)).append(a.minusSeconds(n)).append(a.plusNanos(n * 1000003)); break;
                    case 1: out.append(a.plus(n, UNITS[r(UNITS.length)])); break;
                    case 2: { LocalTime b = lt(); out.append(a.until(b, UNITS[r(UNITS.length)])).append(a.compareTo(b)).append(a.isBefore(b)).append(a.equals(b)); break; }
                    case 3: out.append(a.truncatedTo(UNITS[r(UNITS.length)])); break;
                    case 4: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.with(f, r(4) == 0 ? big() : r(100) - 5)); break; }
                    case 5: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.isSupported(f)).append(a.range(f)).append(a.getLong(f)).append(a.get(f)); break; }
                    case 6: out.append(a.withHour(r(25))).append(a.withMinute(r(61))).append(a.withSecond(r(61))).append(a.withNano(r(3) == 0 ? -1 : r(1000))); break;
                    case 7: out.append(LocalTime.parse(a.toString())).append(a.format(DateTimeFormatter.ISO_LOCAL_TIME)); break;
                    case 8: out.append(a.plus(Duration.ofSeconds(big() % 1000000000L, r(1000000000)))).append(a.minus(Duration.ofMinutes(r(10000)))); break;
                    default: out.append(a.atDate(LocalDate.of(2000, 1, 1 + r(28)))).append(a == LocalTime.of(a.getHour(), 0)).append(LocalTime.MIDNIGHT == LocalTime.of(0, 0, 0, 0)); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static LocalDateTime ldt() {
        switch (r(4)) {
            case 0: return LocalDateTime.of(ld(), lt());
            case 1: return LocalDateTime.ofEpochSecond(big() % 30000000000000000L, r(1000000000), ZoneOffset.ofHours(r(37) - 18));
            case 2: return r(2) == 0 ? LocalDateTime.MAX : LocalDateTime.MIN;
            default: return LocalDateTime.of(1900 + r(250), 1 + r(12), 1 + r(28), r(24), r(60), r(60), r(3) == 0 ? 0 : r(1000000000));
        }
    }

    static final String[] LDTEXTS = {"2024-01-01T10:15", "2024-01-01T10:15:30", "2024-01-01T10:15:30.1", "2024-01-01t10:15",
        "2024-01-01T24:00", "2024-01-01T23:59:60", "2024-01-01T10:15:30.1234567890", "2024-01-01 10:15", "2024-01-01T10",
        "2024-01-01T10:15:30Z", "2024-01-01T10:15:30+01:00", "2024-01-01T10:15:30+01:00[UTC]", "2024-01-01T10:15:30.000"};

    public static String dateTime(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                LocalDateTime a = ldt();
                out.append(a).append('|').append(a.hashCode()).append('|');
                long n = r(3) == 0 ? big() : r(2000000) - 1000000;
                switch (r(12)) {
                    case 0: out.append(a.plusHours(n)).append(a.minusMinutes(n)).append(a.plusSeconds(n)).append(a.plusNanos(n * 7919)); break;
                    case 1: out.append(a.plus(n, UNITS[r(UNITS.length)])); break;
                    case 2: { LocalDateTime b = ldt(); out.append(a.until(b, UNITS[r(UNITS.length)])).append(a.compareTo(b)).append(a.isAfter(b)); break; }
                    case 3: out.append(a.truncatedTo(UNITS[r(9)])); break;
                    case 4: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.with(f, r(4) == 0 ? big() : r(100) - 5)); break; }
                    case 5: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.range(f)).append(a.getLong(f)).append(a.get(f)); break; }
                    case 6: out.append(a.with(adj())).append(a.with(LocalTime.NOON)).append(a.with(LocalDate.EPOCH)); break;
                    case 7: out.append(LocalDateTime.parse(a.toString())).append(a.format(DateTimeFormatter.ISO_LOCAL_DATE_TIME)); break;
                    case 8: out.append(LocalDateTime.parse(LDTEXTS[r(LDTEXTS.length)])); break;
                    case 9: { ZoneOffset o = ZoneOffset.ofTotalSeconds((r(145) - 72) * 900); out.append(a.toEpochSecond(o)).append(a.toInstant(o)).append(a.atOffset(o)); break; }
                    case 10: out.append(Duration.between(a, ldt())).append(a.plus(Duration.ofSeconds(big() % 100000000000L))); break;
                    default: out.append(a.toLocalDate().atTime(a.toLocalTime()).equals(a)).append(a.getDayOfWeek()).append(a.query(TemporalQueries.localTime())); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String[] ZIDS = {"Z", "+05:30", "-08:00", "+18:00", "-18:00", "+19:00", "+5", "+05", "-0530", "+05:30:45",
        "+053045", "+05:3", "05:30", "+aa:00", "+05-30", "", "+", "UTC", "GMT", "UT", "UTC+01:00", "GMT-05:30", "UT+3",
        "UTC+x", "GMT+25", "@@", "a", "Europe/Paris", "UTC0", "+00:00", "-00:00", "+01:00:00", "+12:34:56", "-1"};

    static ZoneId zone() {
        switch (r(5)) {
            case 0: return ZoneOffset.ofHours(r(37) - 18);
            case 1: return ZoneOffset.ofTotalSeconds(r(129601) - 64800);
            case 2: return ZoneId.of(new String[] {"UTC", "GMT", "UT", "UTC+01:00", "GMT-05:30", "UT+03"}[r(6)]);
            case 3: return ZoneOffset.UTC;
            default: return ZoneOffset.ofHoursMinutes(r(19) - 9, (r(19) - 9) * 3 * (r(2) == 0 ? 0 : 1));
        }
    }

    public static String zoned(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                switch (r(10)) {
                    case 0: { String id = ZIDS[r(ZIDS.length)]; ZoneOffset o = ZoneOffset.of(id); out.append(o).append(o.getTotalSeconds())
                        .append(o == ZoneOffset.ofTotalSeconds(o.getTotalSeconds())).append(o.hashCode()); break; }
                    case 1: { String id = ZIDS[r(ZIDS.length)]; ZoneId z = id.startsWith("Europe") ? ZoneOffset.UTC : ZoneId.of(id);
                        out.append(z).append(z.getClass().getName()).append(z.normalized()).append(z.getRules()).append(z.hashCode()); break; }
                    case 2: out.append(ZoneOffset.ofHoursMinutesSeconds(r(41) - 20, r(130) - 65, r(130) - 65)); break;
                    case 3: { ZoneOffset o = ZoneOffset.ofTotalSeconds(r(140000) - 70000); out.append(o).append(o.compareTo(ZoneOffset.UTC)); break; }
                    case 4: { OffsetDateTime a = OffsetDateTime.of(ldt(), ZoneOffset.ofHours(r(37) - 18));
                        OffsetDateTime b = OffsetDateTime.ofInstant(inst(), ZoneOffset.ofHoursMinutes(r(10), r(60)));
                        out.append(a).append(b).append(a.compareTo(b)).append(a.isBefore(b)).append(a.isEqual(b)).append(a.until(b, UNITS[r(15)]))
                            .append(a.hashCode()).append(a.withOffsetSameInstant(ZoneOffset.UTC)); break; }
                    case 5: { ZonedDateTime z = ZonedDateTime.of(ldt(), zone()); out.append(z).append(z.getOffset()).append(z.getZone())
                        .append(z.toEpochSecond()).append(z.hashCode()).append(z.plusHours(r(100))).append(z.withZoneSameInstant(zone()))
                        .append(z.withZoneSameLocal(zone())); break; }
                    case 6: { ZonedDateTime z = ZonedDateTime.ofInstant(inst(), zone()); ZonedDateTime y = ZonedDateTime.ofInstant(inst(), zone());
                        out.append(z).append(z.compareTo(y)).append(z.until(y, UNITS[r(15)])).append(z.equals(y)).append(z.toOffsetDateTime()); break; }
                    case 7: { OffsetDateTime a = OffsetDateTime.of(ldt(), ZoneOffset.ofHours(r(37) - 18));
                        out.append(OffsetDateTime.parse(a.toString())).append(a.format(DateTimeFormatter.ISO_OFFSET_DATE_TIME))
                            .append(a.format(DateTimeFormatter.ISO_INSTANT)).append(a.format(DateTimeFormatter.ISO_ZONED_DATE_TIME)); break; }
                    case 8: { ZonedDateTime z = ZonedDateTime.of(ldt(), zone()); out.append(ZonedDateTime.parse(z.toOffsetDateTime().toString()))
                        .append(z.format(DateTimeFormatter.ISO_ZONED_DATE_TIME)).append(z.format(DateTimeFormatter.ISO_DATE_TIME)); break; }
                    default: { ZonedDateTime z = ZonedDateTime.of(ldt(), zone()); ChronoField f = FIELDS[r(FIELDS.length)];
                        out.append(z.range(f)).append(z.getLong(f)).append(z.with(f, r(100))).append(z.plus(r(1000) - 500, UNITS[r(15)])); break; }
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String[] PTEXTS = {"P1Y2M3D", "P-1Y", "-P1Y2M", "+P3W", "P1W2D", "p1y", "P", "PT1H", "P1Y-2M", "P2147483647D",
        "P2147483648D", "P-2147483648Y", "-P-2147483648Y", "P300000000W", "P1D2M", "P+1M", "P1.5Y", "PY", "P1Y2M3W4D", "1Y"};

    public static String period(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                Period p = r(3) == 0 ? Period.of(r(2) == 0 ? Integer.MAX_VALUE - r(3) : r(40) - 20, r(30) - 15, r(80) - 40)
                    : Period.of(r(10) - 5, r(30) - 15, r(70) - 35);
                out.append(p).append('|').append(p.hashCode()).append(p.isZero()).append(p.isNegative()).append(p.toTotalMonths()).append('|');
                switch (r(8)) {
                    case 0: out.append(p.normalized()).append(p.negated()).append(p.multipliedBy(r(7) - 3)); break;
                    case 1: out.append(p.plus(Period.ofMonths(r(50)))).append(p.minusDays(r(100))).append(p.plusYears(big() % 3000000000L)); break;
                    case 2: out.append(Period.parse(PTEXTS[r(PTEXTS.length)])); break;
                    case 3: { LocalDate a = ld(), b = ld(); out.append(Period.between(a, b)).append(a.plus(Period.between(a, b)).equals(b)); break; }
                    case 4: out.append(ld().plus(p)).append(LocalDateTime.of(2000, 1, 31, 0, 0).minus(p)); break;
                    case 5: out.append(Period.from(Period.ofDays(r(9)))).append(p.withDays(r(5))).append(p.getUnits()).append(p.get(UNITS[r(UNITS.length)])); break;
                    case 6: out.append(Period.parse(p.toString()).equals(p)).append(Period.ofWeeks(r(2) == 0 ? 400000000 : r(10))); break;
                    default: out.append(p.addTo(ld())).append(p.subtractFrom(ld())).append(p.getChronology()); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String fields(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                ChronoField f = FIELDS[r(FIELDS.length)];
                ChronoUnit u = UNITS[r(UNITS.length)];
                switch (r(10)) {
                    case 0: out.append(f).append(f.range()).append(f.getBaseUnit()).append(f.getRangeUnit()).append(f.isDateBased()).append(f.isTimeBased())
                        .append(f.range().hashCode()).append(f.range().isIntValue()).append(f.range().isFixed()); break;
                    case 1: out.append(f.checkValidValue(r(2) == 0 ? big() : r(100) - 5)); break;
                    case 2: out.append(f.checkValidIntValue(r(2) == 0 ? big() : r(100) - 5)); break;
                    case 3: out.append(u).append(u.getDuration()).append(u.isDurationEstimated()).append(u.isDateBased()).append(u.isTimeBased()); break;
                    case 4: { ValueRange v = ValueRange.of(r(10) - 5, r(10) - 5, r(10) - 5, r(10) - 5); out.append(v).append(v.hashCode())
                        .append(v.equals(ValueRange.of(v.getMinimum(), v.getMaximum()))).append(v.checkValidValue(r(10) - 5, r(2) == 0 ? null : f)); break; }
                    case 5: { DayOfWeek d = DayOfWeek.of(r(9)); out.append(d).append(d.plus(big())).append(d.minus(r(20))).append(d.getValue()); break; }
                    case 6: { Month m = Month.of(r(14)); out.append(m).append(m.plus(big())).append(m.length(r(2) == 0)).append(m.firstDayOfYear(true))
                        .append(m.firstMonthOfQuarter()).append(m.maxLength()).append(m.getDisplayName(TextStyle.values()[r(6)], r(2) == 0 ? Locale.ENGLISH : Locale.US)); break; }
                    case 7: { DayOfWeek d = DayOfWeek.of(1 + r(7)); out.append(d.getDisplayName(TextStyle.values()[r(6)], Locale.US)).append(DayOfWeek.from(ld())); break; }
                    case 8: out.append(ld().with(DayOfWeek.of(1 + r(7)))).append(ld().with(Month.of(1 + r(12)))).append(Month.from(ldt())); break;
                    default: out.append(IsoChronology.INSTANCE.isLeapYear(big())).append(IsoChronology.INSTANCE.date(year(), 1 + r(12), 1 + r(31)))
                        .append(IsoChronology.INSTANCE.epochSecond(year(), 1 + r(12), 1 + r(31), r(24), r(60), r(60), ZoneOffset.ofHours(r(10)))); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String LETTERS = "yuMLdDHhKkmsSnaEGAN";

    static String pattern() {
        StringBuilder b = new StringBuilder();
        for (int i = 1 + r(5); i > 0; i--) {
            switch (r(7)) {
                case 0: b.append(r(2) == 0 ? "-" : r(2) == 0 ? " " : ":"); break;
                case 1: b.append("'T'"); break;
                case 2: b.append(r(4) == 0 ? "[" : r(3) == 0 ? "]" : r(2) == 0 ? "''" : "."); break;
                case 3: b.append(r(8) == 0 ? "XXX" : r(7) == 0 ? "xx" : r(6) == 0 ? "Z" : r(5) == 0 ? "VV" : "yyyy"); break;
                default: { char c = LETTERS.charAt(r(LETTERS.length())); int max = "dHhKkmsa".indexOf(c) >= 0 ? 2 : 4;
                    if (c == 'a') max = 1;
                    for (int j = 1 + r(r(8) == 0 ? 7 : max); j > 0; j--) b.append(c); }
            }
        }
        if (r(40) == 0) b.append("{#Qwq".charAt(r(5)));
        return b.toString();
    }

    public static String fmt(int seed) {
        s = seed;
        fuzzy = true;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                String p = pattern();
                out.append(p).append('=');
                DateTimeFormatter f = r(2) == 0 ? DateTimeFormatter.ofPattern(p, r(2) == 0 ? Locale.ENGLISH : Locale.US) : DateTimeFormatter.ofPattern(p, Locale.US);
                out.append(f).append('|');
                TemporalAccessor t;
                switch (r(5)) {
                    case 0: t = ldt(); break;
                    case 1: t = ld(); break;
                    case 2: t = lt(); break;
                    case 3: t = ZonedDateTime.of(ldt(), zone()); break;
                    default: t = OffsetDateTime.of(ldt(), ZoneOffset.ofHours(r(37) - 18)); break;
                }
                String text = f.format(t);
                out.append(text).append('|');
                if (r(3) == 0) {
                    int i = r(text.length() + 1);
                    text = text.substring(0, i) + "0a-:9".charAt(r(5)) + text.substring(Math.min(text.length(), i + 1));
                }
                switch (r(4)) {
                    case 0: out.append(f.parse(text, LocalDateTime::from)); break;
                    case 1: out.append(f.parse(text, LocalDate::from)); break;
                    case 2: out.append(f.parse(text, LocalTime::from)); break;
                    default: out.append(norm(f.parse(text).toString())); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String builder(int seed) {
        s = seed;
        fuzzy = true;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 4; k++) {
            try {
                DateTimeFormatterBuilder b = new DateTimeFormatterBuilder();
                if (r(3) == 0) b.parseCaseInsensitive();
                if (r(3) == 0) b.parseLenient();
                int n = 1 + r(4);
                for (int i = 0; i < n; i++) {
                    ChronoField f = new ChronoField[] {ChronoField.YEAR, ChronoField.MONTH_OF_YEAR, ChronoField.DAY_OF_MONTH,
                        ChronoField.HOUR_OF_DAY, ChronoField.DAY_OF_YEAR, ChronoField.MINUTE_OF_HOUR}[r(6)];
                    switch (r(6)) {
                        case 0: b.appendValue(f); break;
                        case 1: b.appendValue(f, 1 + r(4)); break;
                        case 2: b.appendValue(f, 1 + r(4), 1 + r(10), SignStyle.values()[r(5)]); break;
                        case 3: b.appendValueReduced(r(4) == 0 ? f : ChronoField.YEAR, 1 + r(3), 1 + r(4), r(5) == 0 ? -50 - r(100) : 1950 + r(100)); break;
                        case 4: b.appendLiteral(r(2) == 0 ? "/" : "--"); break;
                        default: b.appendFraction(ChronoField.NANO_OF_SECOND, r(4), 1 + r(9), r(2) == 0); break;
                    }
                }
                if (r(2) == 0) b.parseDefaulting(ChronoField.DAY_OF_MONTH, 1 + r(28));
                DateTimeFormatter f = b.toFormatter(Locale.US).withResolverStyle(ResolverStyle.values()[r(3)]);
                LocalDateTime t = LocalDateTime.of(1 + r(3000), 1 + r(12), 1 + r(28), r(24), r(60), r(60), r(1000000000));
                String text = f.format(t);
                out.append(text).append('|');
                if (r(2) == 0) text = (r(2) == 0 ? "+" : "") + text + (r(3) == 0 ? "1" : "");
                TemporalAccessor ta = f.parse(text);
                out.append(ta.isSupported(ChronoField.YEAR)).append(ta.query(TemporalQueries.localDate())).append(ta.query(TemporalQueries.localTime()));
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String yearMonth(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                java.time.YearMonth a = java.time.YearMonth.of(year(), r(14));
                java.time.Year y = java.time.Year.of(year());
                out.append(a).append('|').append(a.hashCode()).append(a.lengthOfMonth()).append(a.isLeapYear()).append(y).append(y.isLeap())
                    .append(y.length()).append('|');
                long n = r(3) == 0 ? big() : r(2000) - 1000;
                switch (r(8)) {
                    case 0: out.append(a.plusMonths(n)).append(a.minusYears(n)).append(y.plusYears(n)); break;
                    case 1: out.append(a.plus(n, UNITS[r(UNITS.length)])).append(y.minus(n, UNITS[r(UNITS.length)])); break;
                    case 2: { java.time.YearMonth b = java.time.YearMonth.of(year(), 1 + r(12)); out.append(a.until(b, UNITS[r(UNITS.length)]))
                        .append(a.compareTo(b)).append(y.until(java.time.Year.of(year()), UNITS[r(UNITS.length)])); break; }
                    case 3: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.isSupported(f)).append(a.range(f)).append(a.getLong(f))
                        .append(y.get(f)); break; }
                    case 4: out.append(a.atDay(r(33))).append(a.atEndOfMonth()).append(y.atDay(r(368))).append(y.atMonth(r(14))); break;
                    case 5: out.append(java.time.YearMonth.parse(r(2) == 0 ? a.toString() : new String[] {"2024-13", "+12024-01", "12024-01", "2024-1", "-0005-12"}[r(5)]))
                        .append(java.time.Year.parse(r(2) == 0 ? y.toString() : new String[] {"+2024", "-0", "12345678901", "x", "2024x", "-999999999"}[r(6)])); break;
                    case 6: { ChronoField f = FIELDS[r(FIELDS.length)]; out.append(a.with(f, r(30) - 5)).append(y.with(f, r(4) == 0 ? big() : r(3000))); break; }
                    default: out.append(ld().with(a)).append(ld().with(y)).append(java.time.YearMonth.from(ldt())).append(java.time.Year.from(ld())); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String[] TPATS = {"MMM", "MMMM", "MMMMM", "LLL", "LLLL", "EEE", "EEEE", "EEEEE", "E", "a", "G", "GGGG", "GGGGG",
        "ccc", "cccc", "eee", "dd MMM uuuu", "EEE, d MMM yyyy", "h:mm a", "MMMM d, uuuu G", "EEEE dd/MM/uuuu"};
    static final String[] TWORDS = {"Jan", "jan", "JANUARY", "January", "Sept", "Sep", "Mon", "monday", "MONDAY", "AM", "pm", "PM",
        "AD", "BC", "Anno Domini", "before christ", "J", "M", "T", "S", "A", "a", "p", "12", "5", "0", "CE", "BCE", "Thu", "Thursday"};

    public static String textFmt(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                String p = TPATS[r(TPATS.length)];
                DateTimeFormatterBuilder b = new DateTimeFormatterBuilder();
                if (r(2) == 0) b.parseCaseInsensitive();
                if (r(2) == 0) b.parseLenient();
                DateTimeFormatter f = b.appendPattern(p).toFormatter(r(2) == 0 ? Locale.ENGLISH : Locale.US);
                out.append(p).append('=').append(f).append('|');
                LocalDateTime t = ldt();
                String text = f.format(t);
                out.append(text).append('|');
                String in = r(2) == 0 ? text : TWORDS[r(TWORDS.length)];
                if (r(4) == 0) in = in.toUpperCase();
                out.append(in).append("->").append(norm(f.parse(in).toString()));
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String zoneFmt(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                ZoneId z = zone();
                Instant i = inst();
                switch (r(8)) {
                    case 0: out.append(DateTimeFormatter.ofPattern("uuuu-MM-dd HH:mm:ss.SSS XXX", Locale.US).withZone(z).format(i)); break;
                    case 1: out.append(DateTimeFormatter.ISO_LOCAL_DATE_TIME.withZone(z).format(i)).append(DateTimeFormatter.ISO_OFFSET_DATE_TIME.withZone(z).format(i)); break;
                    case 2: out.append(DateTimeFormatter.ISO_ZONED_DATE_TIME.withZone(z).format(i)).append(DateTimeFormatter.ISO_INSTANT.format(i.atZone(z))); break;
                    case 3: out.append(DateTimeFormatter.ISO_LOCAL_DATE.withZone(z).format(ldt())); break;
                    case 4: out.append(DateTimeFormatter.ISO_OFFSET_DATE_TIME.withZone(z).format(OffsetDateTime.of(ldt(), ZoneOffset.ofHours(r(5))))); break;
                    case 5: { DateTimeFormatter f = DateTimeFormatter.ofPattern("uuuu-MM-dd'T'HH:mm[:ss][XXX]", Locale.US).withZone(z);
                        String t = new String[] {"2024-05-06T07:08", "2024-05-06T07:08:09+01:00", "2024-05-06T07:08Z", "2024-05-06T07:08:61"}[r(4)];
                        out.append(f.parse(t, Instant::from)).append(ZonedDateTime.parse(t, f)); break; }
                    case 6: out.append(DateTimeFormatter.ISO_OFFSET_DATE_TIME.withChronology(IsoChronology.INSTANCE).format(ZonedDateTime.ofInstant(i, z)))
                        .append(DateTimeFormatter.ISO_LOCAL_TIME.withChronology(IsoChronology.INSTANCE).format(lt())); break;
                    default: out.append(ZonedDateTime.parse(new String[] {"2024-01-01T10:00Z", "2024-01-01T10:00+02:00", "2024-01-01T10:00:00.5-05:30",
                        "2024-01-01T10:00+02:00[+02:00]", "2024-01-01T10:00Z[UTC]", "2024-01-01T10:00+01:00[GMT+01:00]", "2024-01-01T10:00+02:00[UTC+01:00]"}[r(7)])); break;
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    /** A user unit of two days. */
    static final class TwoDays implements java.time.temporal.TemporalUnit {
        public Duration getDuration() { return Duration.ofDays(2); }
        public boolean isDurationEstimated() { return true; }
        public boolean isDateBased() { return true; }
        public boolean isTimeBased() { return false; }
        @SuppressWarnings("unchecked")
        public <R extends Temporal> R addTo(R temporal, long amount) { return (R) temporal.plus(Math.multiplyExact(amount, 2), ChronoUnit.DAYS); }
        public long between(Temporal a, Temporal b) { return a.until(b, ChronoUnit.DAYS) / 2; }
        public String toString() { return "TwoDays"; }
    }

    /** A user field: the half of the year (1 or 2). */
    static final class HalfOfYear implements java.time.temporal.TemporalField {
        public java.time.temporal.TemporalUnit getBaseUnit() { return ChronoUnit.MONTHS; }
        public java.time.temporal.TemporalUnit getRangeUnit() { return ChronoUnit.YEARS; }
        public ValueRange range() { return ValueRange.of(1, 2); }
        public boolean isDateBased() { return true; }
        public boolean isTimeBased() { return false; }
        public boolean isSupportedBy(TemporalAccessor t) { return t.isSupported(ChronoField.MONTH_OF_YEAR); }
        public ValueRange rangeRefinedBy(TemporalAccessor t) { return range(); }
        public long getFrom(TemporalAccessor t) { return t.get(ChronoField.MONTH_OF_YEAR) > 6 ? 2 : 1; }
        @SuppressWarnings("unchecked")
        public <R extends Temporal> R adjustInto(R t, long v) { range().checkValidValue(v, this);
            return (R) t.with(ChronoField.MONTH_OF_YEAR, (t.get(ChronoField.MONTH_OF_YEAR) - 1) % 6 + 1 + 6 * (v - 1)); }
        public String toString() { return "HalfOfYear"; }
    }

    /** A user amount: n days and m hours. */
    static final class Amount implements java.time.temporal.TemporalAmount {
        final long d, h;
        Amount(long d, long h) { this.d = d; this.h = h; }
        public long get(java.time.temporal.TemporalUnit u) { if (u == ChronoUnit.DAYS) return d; if (u == ChronoUnit.HOURS) return h;
            throw new java.time.temporal.UnsupportedTemporalTypeException("no " + u); }
        public java.util.List<java.time.temporal.TemporalUnit> getUnits() { return h == 0 ? java.util.List.of(ChronoUnit.DAYS) : java.util.List.of(ChronoUnit.DAYS, ChronoUnit.HOURS); }
        public Temporal addTo(Temporal t) { t = t.plus(d, ChronoUnit.DAYS); return h == 0 ? t : t.plus(h, ChronoUnit.HOURS); }
        public Temporal subtractFrom(Temporal t) { t = t.minus(d, ChronoUnit.DAYS); return h == 0 ? t : t.minus(h, ChronoUnit.HOURS); }
    }

    /** A user accessor with only some ChronoFields. */
    static final class Acc implements TemporalAccessor {
        final java.util.TreeMap<Integer, Long> v = new java.util.TreeMap<>();
        Acc put(ChronoField f, long x) { v.put(f.ordinal(), x); return this; }
        public boolean isSupported(java.time.temporal.TemporalField f) { return f instanceof ChronoField && v.containsKey(((ChronoField) f).ordinal()); }
        public long getLong(java.time.temporal.TemporalField f) { Long x = f instanceof ChronoField ? v.get(((ChronoField) f).ordinal()) : null;
            if (x == null) throw new java.time.temporal.UnsupportedTemporalTypeException("Acc: " + f); return x; }
        public String toString() { return "Acc" + v; }
    }

    static Temporal anyTemporal() {
        switch (r(7)) {
            case 0: return ld();
            case 1: return lt();
            case 2: return ldt();
            case 3: return inst();
            case 4: return OffsetDateTime.of(ldt(), ZoneOffset.ofHours(r(5)));
            case 5: return ZonedDateTime.of(ldt(), zone());
            default: return r(2) == 0 ? java.time.Year.of(year()) : java.time.YearMonth.of(year(), 1 + r(12));
        }
    }

    public static String iface(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                Temporal t = anyTemporal();
                out.append(t).append('|');
                switch (r(14)) {
                    case 0: out.append(t.plus(r(100) - 50, new TwoDays())).append(t.isSupported(new TwoDays())); break;
                    case 1: out.append(t.until(anyTemporal(), new TwoDays())); break;
                    case 2: out.append(t.isSupported(new HalfOfYear())).append(t.get(new HalfOfYear())).append(t.getLong(new HalfOfYear())); break;
                    case 3: out.append(t.with(new HalfOfYear(), 1 + r(3))); break;
                    case 4: out.append(t.plus(new Amount(r(40) - 20, r(3) == 0 ? r(50) : 0))).append(t.minus(new Amount(r(9), 0))); break;
                    case 5: out.append(Period.from(new Amount(r(40), r(2) * 3))).append(Duration.from(new Amount(r(9), r(30)))); break;
                    case 6: out.append(t.with(x -> x.plus(1 + r(5), ChronoUnit.DAYS))).append((Object) t.query((java.time.temporal.TemporalQuery<Boolean>) x -> x.isSupported(ChronoField.YEAR))); break;
                    case 7: out.append(t.query(TemporalQueries.zone())).append(t.query(TemporalQueries.offset())).append(t.query(TemporalQueries.localDate()))
                        .append(t.query(TemporalQueries.localTime())).append(t.query(TemporalQueries.precision())).append(t.query(TemporalQueries.chronology()))
                        .append(t.query(TemporalQueries.zoneId())); break;
                    case 8: { Acc a = new Acc(); if (r(2) == 0) a.put(ChronoField.EPOCH_DAY, r(100000)); if (r(2) == 0) a.put(ChronoField.NANO_OF_DAY, r(1000000) * 1000000L);
                        if (r(2) == 0) a.put(ChronoField.INSTANT_SECONDS, big() % 100000000000L); if (r(2) == 0) a.put(ChronoField.OFFSET_SECONDS, r(7200));
                        if (r(2) == 0) a.put(ChronoField.NANO_OF_SECOND, r(1000));
                        switch (r(6)) {
                            case 0: out.append(LocalDate.from(a)).append(LocalTime.from(a)); break;
                            case 1: out.append(LocalDateTime.from(a)); break;
                            case 2: out.append(Instant.from(a)); break;
                            case 3: out.append(OffsetDateTime.from(a)); break;
                            case 4: out.append(ZonedDateTime.from(a)).append(ZoneOffset.from(a)); break;
                            default: out.append(DateTimeFormatter.ISO_LOCAL_DATE.format(a)); break;
                        }
                        break; }
                    case 9: { ChronoLocalDate c = ld(); ChronoLocalDate d = ld(); out.append(c.until(d)).append(c.compareTo(d)).append(ChronoLocalDate.timeLineOrder().compare(c, d))
                        .append(c.isAfter(d)).append(c.isSupported(ChronoUnit.HOURS)).append(c.lengthOfYear()); break; }
                    case 10: { Temporal u = anyTemporal(); out.append(Duration.between(t, u)); break; }
                    case 11: out.append(new DateTimeFormatterBuilder().appendValue(new HalfOfYear()).appendLiteral('/').appendValue(ChronoField.YEAR).toFormatter(Locale.US).format(t)); break;
                    case 12: out.append(norm(new DateTimeFormatterBuilder().appendValue(new HalfOfYear()).toFormatter(Locale.US).parse("" + r(4)).toString())); break;
                    default: { ChronoUnit u = UNITS[r(UNITS.length)]; out.append(u.addTo(t, r(10))).append(u.between(t, anyTemporal())).append(u.isSupportedBy(t)); break; }
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    interface Call { Object call(); }

    static final Call[] NULLS = {
        () -> LocalDate.of(2020, (Month) null, 1), () -> LocalDate.parse(null), () -> LocalDate.parse("2020-01-01", null),
        () -> LocalDate.EPOCH.plus(null), () -> LocalDate.EPOCH.minus(null), () -> LocalDate.EPOCH.format(null),
        () -> LocalDate.EPOCH.isSupported((java.time.temporal.TemporalField) null), () -> LocalDate.EPOCH.isSupported((java.time.temporal.TemporalUnit) null),
        () -> LocalDate.EPOCH.equals(null), () -> LocalDateTime.of(LocalDate.EPOCH, null), () -> LocalDateTime.of(null, LocalTime.NOON),
        () -> Instant.parse(null), () -> ZoneId.of(null), () -> ZoneOffset.of(null), () -> DateTimeFormatter.ofPattern(null),
        () -> DateTimeFormatter.ISO_LOCAL_DATE.format(null), () -> DateTimeFormatter.ISO_LOCAL_DATE.parse(null),
        () -> DateTimeFormatter.ofPattern("yyyy", Locale.US).withLocale(null), () -> DateTimeFormatter.ofPattern("yyyy", null),
        () -> Period.parse(null), () -> LocalDate.from(null), () -> LocalTime.from(null), () -> Instant.from(null),
        () -> ZonedDateTime.of(LocalDateTime.MIN, null), () -> ZonedDateTime.of(null, ZoneOffset.UTC), () -> OffsetDateTime.of(LocalDateTime.MIN, null),
        () -> Instant.EPOCH.atZone(null), () -> LocalDate.EPOCH.atStartOfDay(null), () -> DateTimeFormatter.ISO_LOCAL_DATE.parse("2020-01-01", (java.time.temporal.TemporalQuery<Object>) null),
        () -> DateTimeFormatter.ISO_LOCAL_DATE.withResolverStyle(null), () -> new DateTimeFormatterBuilder().appendPattern(null),
        () -> new DateTimeFormatterBuilder().appendValue(null), () -> new DateTimeFormatterBuilder().appendLiteral(null),
        () -> new DateTimeFormatterBuilder().appendText(null), () -> new DateTimeFormatterBuilder().append(null),
        () -> new DateTimeFormatterBuilder().appendOffset(null, "Z"), () -> new DateTimeFormatterBuilder().appendOffset("+HH", null),
        () -> new DateTimeFormatterBuilder().toFormatter(null), () -> LocalDate.ofInstant(null, ZoneOffset.UTC), () -> LocalDate.ofInstant(Instant.EPOCH, null),
        () -> LocalDateTime.ofEpochSecond(0, 0, null), () -> LocalDateTime.ofInstant(Instant.EPOCH, null), () -> ZoneId.ofOffset(null, ZoneOffset.UTC),
        () -> ZoneId.ofOffset("UTC", null), () -> java.time.YearMonth.of(2020, (Month) null), () -> Period.from(null),
        () -> Duration.from(null), () -> Duration.parse(null), () -> LocalTime.parse(null), () -> LocalDateTime.parse(null),
        () -> ZonedDateTime.parse(null), () -> OffsetDateTime.parse(null), () -> java.time.Year.parse(null), () -> java.time.YearMonth.parse(null),
        () -> TemporalAdjusters.dayOfWeekInMonth(1, null), () -> TemporalAdjusters.ofDateAdjuster(null), () -> ChronoField.YEAR.getDisplayName(null),
        () -> ChronoField.NANO_OF_DAY.getDisplayName(null), () -> Period.ofDays(1).addTo(null), () -> LocalDate.EPOCH.toEpochSecond(null, ZoneOffset.UTC),
        () -> LocalDate.EPOCH.toEpochSecond(LocalTime.NOON, null), () -> LocalDateTime.MIN.toEpochSecond(null), () -> ZonedDateTime.ofInstant(null, ZoneOffset.UTC),
        () -> ZonedDateTime.of(LocalDateTime.MIN, ZoneId.of("UTC")).getZone().getRules(), () -> new DateTimeFormatterBuilder().parseDefaulting(null, 1), () -> IsoChronology.INSTANCE.epochSecond(2000, 1, 1, 0, 0, 0, null),
        () -> { DateTimeFormatter.ISO_INSTANT.formatTo(Instant.EPOCH, null); return "-"; }, () -> DateTimeFormatter.ISO_INSTANT.parse("x", (java.time.temporal.TemporalQuery<Object>) null),
        () -> DateTimeFormatter.ISO_INSTANT.parseBest("x", (java.time.temporal.TemporalQuery<?>[]) null), () -> DateTimeFormatter.ISO_INSTANT.parseBest("1970-01-01T00:00:00Z", Instant::from),
        () -> java.time.chrono.Chronology.of(null), () -> java.time.chrono.Chronology.from(null), () -> IsoChronology.INSTANCE.date((TemporalAccessor) null),
        () -> ZonedDateTime.ofStrict(LocalDateTime.MIN, ZoneOffset.UTC, ZoneOffset.MAX), () -> ZoneId.ofOffset("XYZ", ZoneOffset.UTC),
        () -> DateTimeFormatter.ISO_LOCAL_DATE.withZone(null).withChronology(null), () -> java.time.chrono.Chronology.of("ISO"),
    };

    public static String nulls(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 8; k++) {
            int i = r(NULLS.length);
            try {
                out.append(i).append('=').append(NULLS[i].call());
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static java.time.Clock clock() {
        switch (r(6)) {
            case 0: return java.time.Clock.fixed(inst(), zone());
            case 1: return java.time.Clock.offset(java.time.Clock.fixed(inst(), zone()), Duration.ofSeconds(big() % 100000000000L, r(1000000000)));
            case 2: return java.time.Clock.tick(java.time.Clock.fixed(inst(), zone()), new Duration[] {Duration.ofMillis(1 + r(1000)),
                Duration.ofNanos(1 + r(1000)), Duration.ofSeconds(r(100)), Duration.ZERO, Duration.ofNanos(-r(3)), Duration.ofDays(1)}[r(6)]);
            case 3: return java.time.InstantSource.fixed(inst()).withZone(zone());
            case 4: return java.time.InstantSource.offset(java.time.Clock.fixed(inst(), zone()), Duration.ofMinutes(r(100) - 50)).withZone(zone());
            default: return java.time.Clock.offset(java.time.Clock.fixed(Instant.ofEpochSecond(r(2000000000)), ZoneOffset.UTC), Duration.ZERO);
        }
    }

    public static String clocks(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                java.time.Clock c = clock();
                out.append(c).append('|').append(c.getZone()).append(c.instant()).append(',').append(c.millis()).append('|');
                switch (r(6)) {
                    case 0: out.append(LocalDate.now(c)).append(LocalTime.now(c)).append(LocalDateTime.now(c)); break;
                    case 1: out.append(Instant.now(c)).append(OffsetDateTime.now(c)).append(ZonedDateTime.now(c)); break;
                    case 2: out.append(java.time.Year.now(c)).append(java.time.YearMonth.now(c)).append(IsoChronology.INSTANCE.dateNow(c)); break;
                    case 3: { java.time.Clock d = c.withZone(zone()); out.append(d).append(d.equals(c)).append(c.equals(clock())); break; }
                    case 4: { java.time.Clock d = clock(); out.append(c.equals(d)).append(d.equals(d)); out.append(c.getClass().getName()); break; }
                    default: { java.time.Clock d = java.time.Clock.fixed(c.instant(), c.getZone()); out.append(d.hashCode()).append(d.equals(java.time.Clock.fixed(c.instant(), c.getZone()))); break; }
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static final String[] PIECES = {"yyyy", "uuuu", "yy", "uu", "y", "u", "yyyyy", "MM", "M", "MMM", "dd", "d", "DDD", "D", "HH", "H",
        "hh", "h", "KK", "k", "kk", "mm", "m", "ss", "s", "SSS", "S", "SSSSSSSSS", "n", "nnnnnn", "N", "A", "a", "EEE", "G", "XXX", "X",
        "xx", "Z", "ZZZZZ", "VV", "ppH", "pppd", "'at'", "''", "-", "/", ":", " ", ".", "T", "[", "]", "[:ss]", "[.SSS]", "F", "LLLL", "e", "c"};

    static String pattern2() {
        StringBuilder b = new StringBuilder();
        int depth = 0;
        for (int i = 1 + r(6); i > 0; i--) {
            String p = PIECES[r(PIECES.length)];
            if (p.equals("[")) depth++;
            if (p.equals("]")) {
                if (depth == 0 && r(4) != 0) continue;
                depth--;
            }
            if ((p.equals("e") || p.equals("c")) && r(10) != 0) continue;
            b.append(p);
        }
        return b.toString();
    }

    static String digits() {
        StringBuilder b = new StringBuilder();
        if (r(4) == 0) b.append(r(2) == 0 ? '+' : '-');
        for (int i = r(16); i > 0; i--) b.append(r(10) == 0 ? "-:/ T.aZ".charAt(r(8)) : (char) ('0' + r(10)));
        return b.toString();
    }

    public static String fmt2(int seed) {
        s = seed;
        fuzzy = true;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 5; k++) {
            try {
                String p = pattern2();
                DateTimeFormatterBuilder bb = new DateTimeFormatterBuilder();
                if (r(4) == 0) bb.parseCaseInsensitive();
                if (r(4) == 0) bb.parseLenient();
                bb.appendPattern(p);
                if (r(4) == 0) bb.parseDefaulting(ChronoField.values()[r(30)], r(60));
                DateTimeFormatter f = bb.toFormatter(Locale.US).withResolverStyle(ResolverStyle.values()[r(3)]);
                out.append(p).append('=');
                TemporalAccessor t = r(3) == 0 ? ZonedDateTime.of(ldt(), zone()) : r(2) == 0 ? ldt() : OffsetDateTime.of(ldt(), ZoneOffset.ofHours(r(37) - 18));
                String text;
                try {
                    text = f.format(t);
                    out.append(text);
                } catch (RuntimeException x) {
                    out.append(exc(x));
                    text = digits();
                }
                out.append('|');
                if (r(3) == 0) text = digits();
                else if (r(3) == 0 && text.length() > 0) { int i = r(text.length()); text = text.substring(0, i) + text.substring(i + 1); }
                out.append(text).append("->");
                switch (r(5)) {
                    case 0: out.append(f.parse(text, LocalDateTime::from)); break;
                    case 1: out.append(f.parse(text, LocalDate::from)); break;
                    case 2: out.append(f.parse(text, LocalTime::from)); break;
                    case 3: out.append(f.parse(text, ZonedDateTime::from)); break;
                    default: { TemporalAccessor a = f.parse(text); out.append(norm(a.toString())).append(a.query(DateTimeFormatter.parsedExcessDays()))
                        .append(a.query(DateTimeFormatter.parsedLeapSecond())); break; }
                }
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }

    static final DateTimeFormatter[] ISOS = {DateTimeFormatter.ISO_LOCAL_DATE, DateTimeFormatter.ISO_OFFSET_DATE, DateTimeFormatter.ISO_DATE,
        DateTimeFormatter.ISO_LOCAL_TIME, DateTimeFormatter.ISO_OFFSET_TIME, DateTimeFormatter.ISO_TIME, DateTimeFormatter.ISO_LOCAL_DATE_TIME,
        DateTimeFormatter.ISO_OFFSET_DATE_TIME, DateTimeFormatter.ISO_ZONED_DATE_TIME, DateTimeFormatter.ISO_DATE_TIME,
        DateTimeFormatter.ISO_ORDINAL_DATE, DateTimeFormatter.ISO_INSTANT, DateTimeFormatter.BASIC_ISO_DATE, DateTimeFormatter.RFC_1123_DATE_TIME};

    public static String isoFmt(int seed) {
        s = seed;
        fuzzy = false;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                int fi = r(ISOS.length);
                DateTimeFormatter f = ISOS[fi];
                out.append(fi).append(':');
                if (r(8) == 0) out.append(f).append('|');
                TemporalAccessor t = r(6) == 0 ? ld() : r(5) == 0 ? lt() : r(4) == 0 ? inst() : r(3) == 0 ? ldt()
                    : r(2) == 0 ? OffsetDateTime.of(ldt(), ZoneOffset.ofTotalSeconds((r(145) - 72) * 900 + (r(4) == 0 ? r(60) : 0)))
                    : ZonedDateTime.of(ldt(), zone());
                String text;
                try {
                    text = f.format(t);
                    out.append(text);
                } catch (RuntimeException x) {
                    out.append(exc(x));
                    text = ITEXTS[r(ITEXTS.length)];
                }
                out.append('|');
                if (r(3) == 0 && text.length() > 0) {
                    int i = r(text.length());
                    text = text.substring(0, i) + "0+-:.TZ1x [".charAt(r(11)) + text.substring(i + (r(2) == 0 ? 1 : 0));
                } else if (r(5) == 0) {
                    text = LDTEXTS[r(LDTEXTS.length)];
                }
                out.append(text).append("->");
                TemporalAccessor a = f.parse(text);
                out.append(a.query(TemporalQueries.localDate())).append(a.query(TemporalQueries.localTime())).append(a.query(TemporalQueries.offset()))
                    .append(a.query(TemporalQueries.zoneId())).append(a.isSupported(ChronoField.INSTANT_SECONDS) ? Instant.from(a).toString() : "-")
                    .append(a.query(DateTimeFormatter.parsedLeapSecond())).append(a.query(DateTimeFormatter.parsedExcessDays()));
            } catch (RuntimeException x) {
                out.append(exc(x));
            }
            out.append(';');
        }
        return out.toString();
    }
}

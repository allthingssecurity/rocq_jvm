package org.rocqjvm.jdkmodel;

import java.time.Duration;
import java.time.temporal.ChronoUnit;

/** Differential tests of java.time.Duration: factories, normalisation, arithmetic and overflow,
 *  parse (valid and invalid ISO-8601 text), toString, conversions, truncation, ChronoUnit. */
public final class DurationOps {
    private DurationOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static long big() {
        switch (r(8)) {
            case 0: return Long.MAX_VALUE - r(3);
            case 1: return Long.MIN_VALUE + r(3);
            case 2: return r(2000) - 1000;
            case 3: return (long) (r(2000000) - 1000000) * 1000003L;
            case 4: return 0;
            case 5: return r(100) * 86400L;
            default: return r(1000000) - 500000;
        }
    }

    static Duration dur() {
        switch (r(9)) {
            case 0: return Duration.ofSeconds(big(), big());
            case 1: return Duration.ofMillis(big());
            case 2: return Duration.ofNanos(big());
            case 3: return Duration.ofMinutes(r(200) - 100);
            case 4: return Duration.ofHours(r(50) - 25);
            case 5: return Duration.ofDays(r(10) - 5);
            case 6: return Duration.ZERO;
            case 7: return Duration.of(r(1000) - 500, ChronoUnit.values()[r(8)]);
            default: return Duration.ofSeconds(r(7200) - 3600, r(2000000000) - 1000000000);
        }
    }

    static final String[] TEXTS = {"PT0S", "PT20.345S", "PT15M", "PT10H", "P2D", "P2DT3H4M", "PT-6H3M", "-PT6H3M",
        "-PT-6H+3M", "pt1.5s", "PT0.000000001S", "PT-0.5S", "P", "PT", "PT1.S", "PT1,5S", "1H", "PT1H2", "P1DT",
        "PT9223372036854775807S", "PT9223372036854775808S", "P106751991167301D", "PT1.0123456789S", "PT+3S", "PT-1M-30S"};

    public static String ops(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                Duration d = dur();
                out.append(d).append('|').append(d.getSeconds()).append(',').append(d.getNano()).append('|');
                switch (r(12)) {
                    case 0: out.append(d.plus(dur())).append(d.minus(dur())); break;
                    case 1: out.append(d.multipliedBy(r(7) - 3)).append(d.negated()).append(d.abs()); break;
                    case 2: out.append(d.dividedBy(r(5) - 2)); break;
                    case 3: out.append(d.toMillis()).append(',').append(d.toNanos()); break;
                    case 4: out.append(d.toDays()).append(d.toHoursPart()).append(d.toMinutesPart()).append(d.toSecondsPart()).append(d.toMillisPart()); break;
                    case 5: out.append(d.compareTo(dur())).append(d.equals(dur())).append(d.hashCode()).append(d.isNegative()).append(d.isZero()); break;
                    case 6: out.append(d.truncatedTo(ChronoUnit.values()[r(9)])); break;
                    case 7: out.append(d.plusMillis(big())).append(d.plusNanos(big())); break;
                    case 8: out.append(d.withNanos(r(5) == 0 ? -1 : r(1000))).append(d.withSeconds(big())); break;
                    case 9: out.append(d.dividedBy(dur())); break;
                    case 10: out.append(d.plus(r(100), ChronoUnit.values()[r(16)])); break;
                    default: out.append(d.minusSeconds(big())).append(d.minusMillis(r(10))); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String parse(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 4; k++) {
            String t = TEXTS[r(TEXTS.length)];
            try {
                Duration d = Duration.parse(t);
                out.append(d).append(',').append(d.toMillis());
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName()).append(':').append(e.getMessage());
            }
            out.append(';');
        }
        ChronoUnit u = ChronoUnit.values()[r(16)];
        out.append(u).append(u.getDuration()).append(u.isDurationEstimated()).append(u.isDateBased()).append(u.isTimeBased());
        return out.toString();
    }
}

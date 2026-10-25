/* Clean-room model of java.util.concurrent.TimeUnit (conversions as in the JDK 21 javadoc: truncating,
   saturating at Long.MIN_VALUE/MAX_VALUE). sleep/timedWait/timedJoin go through the thread model. */
package java.util.concurrent;

public enum TimeUnit {
    NANOSECONDS(1L), MICROSECONDS(1000L), MILLISECONDS(1000000L), SECONDS(1000000000L),
    MINUTES(60000000000L), HOURS(3600000000000L), DAYS(86400000000000L);

    private final long scale;   // nanoseconds per unit
    TimeUnit(long scale) { this.scale = scale; }

    private static long cvt(long d, long dst, long src) {
        if (src == dst) return d;
        if (src < dst) return d / (dst / src);
        long r = src / dst;
        long max = Long.MAX_VALUE / r;
        if (d > max) return Long.MAX_VALUE;
        if (d < -max) return Long.MIN_VALUE;
        return d * r;
    }
    public long convert(long sourceDuration, TimeUnit sourceUnit) { return cvt(sourceDuration, scale, sourceUnit.scale); }
    public long toNanos(long d) { return cvt(d, NANOSECONDS.scale, scale); }
    public long toMicros(long d) { return cvt(d, MICROSECONDS.scale, scale); }
    public long toMillis(long d) { return cvt(d, MILLISECONDS.scale, scale); }
    public long toSeconds(long d) { return cvt(d, SECONDS.scale, scale); }
    public long toMinutes(long d) { return cvt(d, MINUTES.scale, scale); }
    public long toHours(long d) { return cvt(d, HOURS.scale, scale); }
    public long toDays(long d) { return cvt(d, DAYS.scale, scale); }
    public void sleep(long timeout) throws InterruptedException { if (timeout > 0) Thread.sleep(toMillis(timeout)); }
    public void timedJoin(Thread thread, long timeout) throws InterruptedException { if (timeout > 0) thread.join(Math.max(1, toMillis(timeout))); }
    public void timedWait(Object obj, long timeout) throws InterruptedException { if (timeout > 0) obj.wait(Math.max(1, toMillis(timeout))); }
}

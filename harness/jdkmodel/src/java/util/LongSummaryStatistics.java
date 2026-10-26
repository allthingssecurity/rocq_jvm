/*
 * rocq-jvm model of java.util.LongSummaryStatistics (clean-room, Apache-2.0), from the Javadoc and JDK 21's
 * observable behaviour: count, long sum, min/max starting at Long.MAX_VALUE/MIN_VALUE, the
 * (count, min, max, sum) constructor checks, toString with %d/%f.
 */
package java.util;

import java.util.function.IntConsumer;
import java.util.function.LongConsumer;

public class LongSummaryStatistics implements LongConsumer, IntConsumer {
    private long count;
    private long sum;
    private long min = Long.MAX_VALUE;
    private long max = Long.MIN_VALUE;

    public LongSummaryStatistics() {
    }

    public LongSummaryStatistics(long count, long min, long max, long sum) throws IllegalArgumentException {
        if (count < 0L) throw new IllegalArgumentException("Negative count value");
        if (count > 0L) {
            if (min > max) throw new IllegalArgumentException("Minimum greater than maximum");
            this.count = count;
            this.sum = sum;
            this.min = min;
            this.max = max;
        }
    }

    public void accept(int value) {
        accept((long) value);
    }

    public void accept(long value) {
        ++count;
        sum += value;
        min = Math.min(min, value);
        max = Math.max(max, value);
    }

    public void combine(LongSummaryStatistics other) {
        count += other.count;
        sum += other.sum;
        min = Math.min(min, other.min);
        max = Math.max(max, other.max);
    }

    public final long getCount() { return count; }
    public final long getSum() { return sum; }
    public final long getMin() { return min; }
    public final long getMax() { return max; }
    public final double getAverage() { return getCount() > 0 ? (double) getSum() / getCount() : 0.0d; }

    public String toString() {
        return String.format("%s{count=%d, sum=%d, min=%d, average=%f, max=%d}", getClass().getSimpleName(), getCount(), getSum(),
                             getMin(), getAverage(), getMax());
    }
}

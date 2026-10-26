/*
 * rocq-jvm model of java.util.DoubleSummaryStatistics (clean-room, Apache-2.0), from the Javadoc and JDK 21's
 * observable behaviour: the compensated (Kahan) sum with its simple sum for
 * infinities, min/max by Math.min/max (NaN propagates), the constructor checks, toString with %f.
 */
package java.util;

import java.util.function.DoubleConsumer;

public class DoubleSummaryStatistics implements DoubleConsumer {
    private long count;
    private double sum;
    private double sumCompensation;
    private double simpleSum;
    private double min = Double.POSITIVE_INFINITY;
    private double max = Double.NEGATIVE_INFINITY;

    public DoubleSummaryStatistics() {
    }

    public DoubleSummaryStatistics(long count, double min, double max, double sum) throws IllegalArgumentException {
        if (count < 0L) throw new IllegalArgumentException("Negative count value");
        if (count > 0L) {
            if (min > max) throw new IllegalArgumentException("Minimum greater than maximum");
            int nan = (Double.isNaN(min) ? 1 : 0) + (Double.isNaN(max) ? 1 : 0) + (Double.isNaN(sum) ? 1 : 0);
            if (nan > 0 && nan < 3) throw new IllegalArgumentException("Some, not all, of the minimum, maximum, or sum is NaN");
            this.count = count;
            this.sum = sum;
            this.simpleSum = sum;
            this.sumCompensation = 0.0d;
            this.min = min;
            this.max = max;
        }
    }

    public void accept(double value) {
        ++count;
        simpleSum += value;
        add(value);
        min = Math.min(min, value);
        max = Math.max(max, value);
    }

    public void combine(DoubleSummaryStatistics other) {
        count += other.count;
        simpleSum += other.simpleSum;
        add(other.sum);
        add(-other.sumCompensation);
        min = Math.min(min, other.min);
        max = Math.max(max, other.max);
    }

    /** One step of compensated summation (the JDK's order of operations). */
    private void add(double value) {
        double t = value - sumCompensation;
        double v = sum + t;
        sumCompensation = (v - sum) - t;
        sum = v;
    }

    public final long getCount() { return count; }

    public final double getSum() {
        double t = sum - sumCompensation;
        return (Double.isNaN(t) && Double.isInfinite(simpleSum)) ? simpleSum : t;
    }

    public final double getMin() { return min; }
    public final double getMax() { return max; }
    public final double getAverage() { return getCount() > 0 ? getSum() / getCount() : 0.0d; }

    public String toString() {
        return String.format("%s{count=%d, sum=%f, min=%f, average=%f, max=%f}", getClass().getSimpleName(), getCount(), getSum(),
                             getMin(), getAverage(), getMax());
    }
}

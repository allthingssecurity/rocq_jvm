/*
 * rocq-jvm model of java.util.random.RandomGenerator (clean-room, Apache-2.0): the JDK 21 default
 * methods (bounded int / long / float / double values by the algorithms of
 * jdk.internal.util.random.RandomSupport: masking for power-of-two ranges, rejection sampling
 * otherwise, scaling for floating point with the correction below the bound; the JDK's
 * IllegalArgumentException messages).
 * Not modelled (STUCK): of / getDefault (named algorithms), the streams (ints, longs, doubles),
 * nextGaussian and nextExponential (StrictMath.log / exp and the ziggurat tables), isDeprecated.
 */
package java.util.random;

public interface RandomGenerator {
    static RandomGenerator of(String name) {
        throw ModelStuckRandom.unsupported("RandomGenerator.of");
    }

    static RandomGenerator getDefault() {
        throw ModelStuckRandom.unsupported("RandomGenerator.getDefault");
    }

    default boolean isDeprecated() {
        throw ModelStuckRandom.unsupported("RandomGenerator.isDeprecated (annotations)");
    }

    default java.util.stream.DoubleStream doubles() {
        throw ModelStuckRandom.unsupported("RandomGenerator.doubles");
    }

    default java.util.stream.DoubleStream doubles(double randomNumberOrigin, double randomNumberBound) {
        throw ModelStuckRandom.unsupported("RandomGenerator.doubles");
    }

    default java.util.stream.DoubleStream doubles(long streamSize) {
        throw ModelStuckRandom.unsupported("RandomGenerator.doubles");
    }

    default java.util.stream.DoubleStream doubles(long streamSize, double randomNumberOrigin, double randomNumberBound) {
        throw ModelStuckRandom.unsupported("RandomGenerator.doubles");
    }

    default java.util.stream.IntStream ints() {
        throw ModelStuckRandom.unsupported("RandomGenerator.ints");
    }

    default java.util.stream.IntStream ints(int randomNumberOrigin, int randomNumberBound) {
        throw ModelStuckRandom.unsupported("RandomGenerator.ints");
    }

    default java.util.stream.IntStream ints(long streamSize) {
        throw ModelStuckRandom.unsupported("RandomGenerator.ints");
    }

    default java.util.stream.IntStream ints(long streamSize, int randomNumberOrigin, int randomNumberBound) {
        throw ModelStuckRandom.unsupported("RandomGenerator.ints");
    }

    default java.util.stream.LongStream longs() {
        throw ModelStuckRandom.unsupported("RandomGenerator.longs");
    }

    default java.util.stream.LongStream longs(long randomNumberOrigin, long randomNumberBound) {
        throw ModelStuckRandom.unsupported("RandomGenerator.longs");
    }

    default java.util.stream.LongStream longs(long streamSize) {
        throw ModelStuckRandom.unsupported("RandomGenerator.longs");
    }

    default java.util.stream.LongStream longs(long streamSize, long randomNumberOrigin, long randomNumberBound) {
        throw ModelStuckRandom.unsupported("RandomGenerator.longs");
    }

    default boolean nextBoolean() {
        return nextInt() < 0;
    }

    default void nextBytes(byte[] bytes) {
        if (bytes == null) throw new NullPointerException("Cannot read the array length because \"bytes\" is null");
        int i = 0;
        int len = bytes.length;
        for (int words = len >> 3; words-- > 0;) {
            long rnd = nextLong();
            for (int n = 8; n-- > 0; rnd >>>= 8) bytes[i++] = (byte) rnd;
        }
        if (i < len) {
            for (long rnd = nextLong(); i < len; rnd >>>= 8) bytes[i++] = (byte) rnd;
        }
    }

    default float nextFloat() {
        return (nextInt() >>> 8) * 0x1.0p-24f;
    }

    default float nextFloat(float bound) {
        if (!(0.0f < bound && bound < Float.POSITIVE_INFINITY))
            throw new IllegalArgumentException("bound must be finite and positive");
        float r = nextFloat();
        r = r * bound;
        if (r >= bound) r = Math.nextDown(bound);
        return r;
    }

    default float nextFloat(float origin, float bound) {
        if (!(Float.NEGATIVE_INFINITY < origin && origin < bound && bound < Float.POSITIVE_INFINITY))
            throw new IllegalArgumentException("bound must be greater than origin");
        float r = nextFloat();
        if (origin < bound) {
            if (bound - origin < Float.POSITIVE_INFINITY) {
                r = r * (bound - origin) + origin;
            } else {
                float halfOrigin = 0.5f * origin;
                r = (r * (0.5f * bound - halfOrigin) + halfOrigin) * 2.0f;
            }
            if (r >= bound) r = Math.nextDown(bound);
        }
        return r;
    }

    default double nextDouble() {
        return (nextLong() >>> 11) * 0x1.0p-53;
    }

    default double nextDouble(double bound) {
        if (!(0.0 < bound && bound < Double.POSITIVE_INFINITY))
            throw new IllegalArgumentException("bound must be finite and positive");
        double r = nextDouble();
        r = r * bound;
        if (r >= bound) r = Math.nextDown(bound);
        return r;
    }

    default double nextDouble(double origin, double bound) {
        if (!(Double.NEGATIVE_INFINITY < origin && origin < bound && bound < Double.POSITIVE_INFINITY))
            throw new IllegalArgumentException("bound must be greater than origin");
        double r = nextDouble();
        if (origin < bound) {
            if (bound - origin < Double.POSITIVE_INFINITY) {
                r = r * (bound - origin) + origin;
            } else {
                double halfOrigin = 0.5 * origin;
                r = (r * (0.5 * bound - halfOrigin) + halfOrigin) * 2.0;
            }
            if (r >= bound) r = Math.nextDown(bound);
        }
        return r;
    }

    default int nextInt() {
        return (int) (nextLong() >>> 32);
    }

    default int nextInt(int bound) {
        if (bound <= 0) throw new IllegalArgumentException("bound must be positive");
        final int m = bound - 1;
        int r = nextInt();
        if ((bound & m) == 0) {
            r &= m;
        } else {
            for (int u = r >>> 1; u + m - (r = u % bound) < 0; u = nextInt() >>> 1) {
            }
        }
        return r;
    }

    default int nextInt(int origin, int bound) {
        if (origin >= bound) throw new IllegalArgumentException("bound must be greater than origin");
        int r = nextInt();
        final int n = bound - origin;
        final int m = n - 1;
        if ((n & m) == 0) {
            r = (r & m) + origin;
        } else if (n > 0) {
            for (int u = r >>> 1; u + m - (r = u % n) < 0; u = nextInt() >>> 1) {
            }
            r += origin;
        } else {
            while (r < origin || r >= bound) r = nextInt();
        }
        return r;
    }

    long nextLong();

    default long nextLong(long bound) {
        if (bound <= 0) throw new IllegalArgumentException("bound must be positive");
        final long m = bound - 1;
        long r = nextLong();
        if ((bound & m) == 0L) {
            r &= m;
        } else {
            for (long u = r >>> 1; u + m - (r = u % bound) < 0L; u = nextLong() >>> 1) {
            }
        }
        return r;
    }

    default long nextLong(long origin, long bound) {
        if (origin >= bound) throw new IllegalArgumentException("bound must be greater than origin");
        long r = nextLong();
        final long n = bound - origin;
        final long m = n - 1;
        if ((n & m) == 0L) {
            r = (r & m) + origin;
        } else if (n > 0L) {
            for (long u = r >>> 1; u + m - (r = u % n) < 0L; u = nextLong() >>> 1) {
            }
            r += origin;
        } else {
            while (r < origin || r >= bound) r = nextLong();
        }
        return r;
    }

    default double nextGaussian() {
        throw ModelStuckRandom.unsupported("RandomGenerator.nextGaussian (StrictMath.log)");
    }

    default double nextGaussian(double mean, double stddev) {
        if (stddev < 0.0) throw new IllegalArgumentException("standard deviation must be non-negative");
        throw ModelStuckRandom.unsupported("RandomGenerator.nextGaussian");
    }

    default double nextExponential() {
        throw ModelStuckRandom.unsupported("RandomGenerator.nextExponential");
    }
}

/*
 * rocq-jvm model of java.util.Random (clean-room, Apache-2.0), JDK 21 behaviour with an explicit
 * seed: the 48-bit linear congruential generator of the class Javadoc (seed scrambled with
 * 0x5DEECE66D; next(bits) the top bits of the 48-bit state; a subclass's constructor calls the
 * overridable setSeed), nextInt / nextInt(bound) (power-of-two shortcut, rejection loop) /
 * nextLong / nextBoolean / nextFloat / nextDouble / nextBytes as the Javadoc specifies, and the
 * RandomGenerator defaults for the other bounded methods.
 * Not modelled (STUCK): new Random() (seeded from System.nanoTime and a global uniquifier: host
 * dependent), nextGaussian (StrictMath.log), the streams (ints, longs, doubles), Random.from of a
 * non-Random generator.
 */
package java.util;

import java.util.random.RandomGenerator;

public class Random implements RandomGenerator, java.io.Serializable {
    static final long serialVersionUID = 3905348978240129619L;

    private static final long MULTIPLIER = 0x5DEECE66DL;
    private static final long ADDEND = 0xBL;
    private static final long MASK = (1L << 48) - 1;

    private long seed;

    public Random() {
        throw ModelStuck.unsupported("new Random() without a seed (host time)");
    }

    public Random(long seed) {
        if (getClass() == Random.class) {
            this.seed = scramble(seed);
        } else {
            this.seed = 0L;
            setSeed(seed);
        }
    }

    private static long scramble(long seed) {
        return (seed ^ MULTIPLIER) & MASK;
    }

    public static Random from(RandomGenerator generator) {
        Objects.requireNonNull(generator);
        if (generator instanceof Random) return (Random) generator;
        throw ModelStuck.unsupported("Random.from of a non-Random generator");
    }

    public synchronized void setSeed(long seed) {
        this.seed = scramble(seed);
    }

    protected int next(int bits) {
        long s;
        synchronized (this) {
            s = (seed * MULTIPLIER + ADDEND) & MASK;
            seed = s;
        }
        return (int) (s >>> (48 - bits));
    }

    public void nextBytes(byte[] bytes) {
        if (bytes == null) throw new NullPointerException("Cannot read the array length because \"bytes\" is null");
        for (int i = 0, len = bytes.length; i < len;) {
            int rnd = nextInt();
            for (int n = Math.min(len - i, 4); n-- > 0; rnd >>= 8) bytes[i++] = (byte) rnd;
        }
    }

    public int nextInt() {
        return next(32);
    }

    public int nextInt(int bound) {
        if (bound <= 0) throw new IllegalArgumentException("bound must be positive");
        int r = next(31);
        int m = bound - 1;
        if ((bound & m) == 0) {
            r = (int) ((bound * (long) r) >> 31);
        } else {
            for (int u = r; u - (r = u % bound) + m < 0; u = next(31)) {
            }
        }
        return r;
    }

    public long nextLong() {
        return ((long) next(32) << 32) + next(32);
    }

    public boolean nextBoolean() {
        return next(1) != 0;
    }

    public float nextFloat() {
        return next(24) * 0x1.0p-24f;
    }

    public double nextDouble() {
        return (((long) next(26) << 27) + next(27)) * 0x1.0p-53;
    }

    public synchronized double nextGaussian() {
        throw ModelStuck.unsupported("Random.nextGaussian (StrictMath.log)");
    }

    public java.util.stream.IntStream ints(long streamSize) {
        throw ModelStuck.unsupported("Random.ints");
    }

    public java.util.stream.IntStream ints() {
        throw ModelStuck.unsupported("Random.ints");
    }

    public java.util.stream.IntStream ints(long streamSize, int randomNumberOrigin, int randomNumberBound) {
        throw ModelStuck.unsupported("Random.ints");
    }

    public java.util.stream.IntStream ints(int randomNumberOrigin, int randomNumberBound) {
        throw ModelStuck.unsupported("Random.ints");
    }

    public java.util.stream.LongStream longs(long streamSize) {
        throw ModelStuck.unsupported("Random.longs");
    }

    public java.util.stream.LongStream longs() {
        throw ModelStuck.unsupported("Random.longs");
    }

    public java.util.stream.LongStream longs(long streamSize, long randomNumberOrigin, long randomNumberBound) {
        throw ModelStuck.unsupported("Random.longs");
    }

    public java.util.stream.LongStream longs(long randomNumberOrigin, long randomNumberBound) {
        throw ModelStuck.unsupported("Random.longs");
    }

    public java.util.stream.DoubleStream doubles(long streamSize) {
        throw ModelStuck.unsupported("Random.doubles");
    }

    public java.util.stream.DoubleStream doubles() {
        throw ModelStuck.unsupported("Random.doubles");
    }

    public java.util.stream.DoubleStream doubles(long streamSize, double randomNumberOrigin, double randomNumberBound) {
        throw ModelStuck.unsupported("Random.doubles");
    }

    public java.util.stream.DoubleStream doubles(double randomNumberOrigin, double randomNumberBound) {
        throw ModelStuck.unsupported("Random.doubles");
    }
}

/*
 * rocq-jvm model of java.util.BitSet (clean-room, Apache-2.0).
 *
 * The JDK's representation: an array of 64-bit words with the number of words in use (the
 * highest word in use is non-zero), growth to max(2 * length, required) words, and the
 * "sticky" size of a BitSet created with an explicit size (kept by clone), so that size(),
 * length(), toString, hashCode, toLongArray and toByteArray are the JDK's. Messages of the
 * index checks are the JDK's.
 * Not modelled (STUCK): valueOf(LongBuffer/ByteBuffer), stream(), serialization.
 */
package java.util;

public class BitSet implements Cloneable, java.io.Serializable {
    private static final int ADDRESS_BITS_PER_WORD = 6;
    private static final int BITS_PER_WORD = 1 << ADDRESS_BITS_PER_WORD;
    private static final int BIT_INDEX_MASK = BITS_PER_WORD - 1;
    private static final long WORD_MASK = 0xffffffffffffffffL;

    private long[] words;
    private transient int wordsInUse = 0;
    private transient boolean sizeIsSticky = false;

    private static int wordIndex(int bitIndex) {
        return bitIndex >> ADDRESS_BITS_PER_WORD;
    }

    private void recalculateWordsInUse() {
        int i;
        for (i = wordsInUse - 1; i >= 0; i--) {
            if (words[i] != 0) break;
        }
        wordsInUse = i + 1;
    }

    public BitSet() {
        initWords(BITS_PER_WORD);
        sizeIsSticky = false;
    }

    public BitSet(int nbits) {
        if (nbits < 0) throw new NegativeArraySizeException("nbits < 0: " + nbits);
        initWords(nbits);
        sizeIsSticky = true;
    }

    private void initWords(int nbits) {
        words = new long[wordIndex(nbits - 1) + 1];
    }

    private BitSet(long[] words) {
        this.words = words;
        this.wordsInUse = words.length;
    }

    public static BitSet valueOf(long[] longs) {
        if (longs == null) throw new NullPointerException("Cannot read the array length because \"longs\" is null");
        int n;
        for (n = longs.length; n > 0 && longs[n - 1] == 0; n--)
            ;
        long[] w = new long[n];
        System.arraycopy(longs, 0, w, 0, n);
        return new BitSet(w);
    }

    public static BitSet valueOf(java.nio.LongBuffer lb) {
        throw ModelStuck.unsupported("BitSet.valueOf(LongBuffer)");
    }

    /** Little-endian bytes: byte i holds bits 8i .. 8i+7. */
    public static BitSet valueOf(byte[] bytes) {
        if (bytes == null) throw new NullPointerException("Cannot read the array length because \"array\" is null");
        int n;
        for (n = bytes.length; n > 0 && bytes[n - 1] == 0; n--)
            ;
        long[] w = new long[(n + 7) / 8];
        for (int i = 0; i < n; i++) w[i >> 3] |= (bytes[i] & 0xffL) << (8 * (i & 7));
        return new BitSet(w);
    }

    public static BitSet valueOf(java.nio.ByteBuffer bb) {
        throw ModelStuck.unsupported("BitSet.valueOf(ByteBuffer)");
    }

    public byte[] toByteArray() {
        int n = wordsInUse;
        if (n == 0) return new byte[0];
        int len = 8 * (n - 1);
        for (long x = words[n - 1]; x != 0; x >>>= 8) len++;
        byte[] bytes = new byte[len];
        int j = 0;
        for (int i = 0; i < n - 1; i++) {
            long x = words[i];
            for (int b = 0; b < 8; b++) {
                bytes[j++] = (byte) (x & 0xff);
                x >>>= 8;
            }
        }
        for (long x = words[n - 1]; x != 0; x >>>= 8) bytes[j++] = (byte) (x & 0xff);
        return bytes;
    }

    public long[] toLongArray() {
        long[] r = new long[wordsInUse];
        System.arraycopy(words, 0, r, 0, wordsInUse);
        return r;
    }

    private void ensureCapacity(int wordsRequired) {
        if (words.length < wordsRequired) {
            int request = Math.max(2 * words.length, wordsRequired);
            long[] n = new long[request];
            System.arraycopy(words, 0, n, 0, words.length);
            words = n;
            sizeIsSticky = false;
        }
    }

    private void expandTo(int wordIndex) {
        int wordsRequired = wordIndex + 1;
        if (wordsInUse < wordsRequired) {
            ensureCapacity(wordsRequired);
            wordsInUse = wordsRequired;
        }
    }

    private static void checkRange(int fromIndex, int toIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        if (toIndex < 0) throw new IndexOutOfBoundsException("toIndex < 0: " + toIndex);
        if (fromIndex > toIndex) throw new IndexOutOfBoundsException("fromIndex: " + fromIndex + " > toIndex: " + toIndex);
    }

    private static NullPointerException nullSet() {
        return new NullPointerException("Cannot read field \"wordsInUse\" because \"set\" is null");
    }

    public void flip(int bitIndex) {
        if (bitIndex < 0) throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);
        int wordIndex = wordIndex(bitIndex);
        expandTo(wordIndex);
        words[wordIndex] ^= (1L << bitIndex);
        recalculateWordsInUse();
    }

    public void flip(int fromIndex, int toIndex) {
        checkRange(fromIndex, toIndex);
        if (fromIndex == toIndex) return;
        int startWordIndex = wordIndex(fromIndex);
        int endWordIndex = wordIndex(toIndex - 1);
        expandTo(endWordIndex);
        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            words[startWordIndex] ^= (firstWordMask & lastWordMask);
        } else {
            words[startWordIndex] ^= firstWordMask;
            for (int i = startWordIndex + 1; i < endWordIndex; i++) words[i] ^= WORD_MASK;
            words[endWordIndex] ^= lastWordMask;
        }
        recalculateWordsInUse();
    }

    public void set(int bitIndex) {
        if (bitIndex < 0) throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);
        int wordIndex = wordIndex(bitIndex);
        expandTo(wordIndex);
        words[wordIndex] |= (1L << bitIndex);
    }

    public void set(int bitIndex, boolean value) {
        if (value) set(bitIndex);
        else clear(bitIndex);
    }

    public void set(int fromIndex, int toIndex) {
        checkRange(fromIndex, toIndex);
        if (fromIndex == toIndex) return;
        int startWordIndex = wordIndex(fromIndex);
        int endWordIndex = wordIndex(toIndex - 1);
        expandTo(endWordIndex);
        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            words[startWordIndex] |= (firstWordMask & lastWordMask);
        } else {
            words[startWordIndex] |= firstWordMask;
            for (int i = startWordIndex + 1; i < endWordIndex; i++) words[i] = WORD_MASK;
            words[endWordIndex] |= lastWordMask;
        }
    }

    public void set(int fromIndex, int toIndex, boolean value) {
        if (value) set(fromIndex, toIndex);
        else clear(fromIndex, toIndex);
    }

    public void clear(int bitIndex) {
        if (bitIndex < 0) throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);
        int wordIndex = wordIndex(bitIndex);
        if (wordIndex >= wordsInUse) return;
        words[wordIndex] &= ~(1L << bitIndex);
        recalculateWordsInUse();
    }

    public void clear(int fromIndex, int toIndex) {
        checkRange(fromIndex, toIndex);
        if (fromIndex == toIndex) return;
        int startWordIndex = wordIndex(fromIndex);
        if (startWordIndex >= wordsInUse) return;
        int endWordIndex = wordIndex(toIndex - 1);
        if (endWordIndex >= wordsInUse) {
            toIndex = length();
            endWordIndex = wordsInUse - 1;
        }
        long firstWordMask = WORD_MASK << fromIndex;
        long lastWordMask = WORD_MASK >>> -toIndex;
        if (startWordIndex == endWordIndex) {
            words[startWordIndex] &= ~(firstWordMask & lastWordMask);
        } else {
            words[startWordIndex] &= ~firstWordMask;
            for (int i = startWordIndex + 1; i < endWordIndex; i++) words[i] = 0;
            words[endWordIndex] &= ~lastWordMask;
        }
        recalculateWordsInUse();
    }

    public void clear() {
        while (wordsInUse > 0) words[--wordsInUse] = 0;
    }

    public boolean get(int bitIndex) {
        if (bitIndex < 0) throw new IndexOutOfBoundsException("bitIndex < 0: " + bitIndex);
        int wordIndex = wordIndex(bitIndex);
        return (wordIndex < wordsInUse) && ((words[wordIndex] & (1L << bitIndex)) != 0);
    }

    public BitSet get(int fromIndex, int toIndex) {
        checkRange(fromIndex, toIndex);
        int len = length();
        if (len <= fromIndex || fromIndex == toIndex) return new BitSet(0);
        if (toIndex > len) toIndex = len;
        BitSet result = new BitSet(toIndex - fromIndex);
        int targetWords = wordIndex(toIndex - fromIndex - 1) + 1;
        int sourceIndex = wordIndex(fromIndex);
        boolean wordAligned = ((fromIndex & BIT_INDEX_MASK) == 0);
        for (int i = 0; i < targetWords - 1; i++, sourceIndex++) {
            result.words[i] = wordAligned ? words[sourceIndex]
                : (words[sourceIndex] >>> fromIndex) | (words[sourceIndex + 1] << -fromIndex);
        }
        long lastWordMask = WORD_MASK >>> -toIndex;
        result.words[targetWords - 1] = ((toIndex - 1) & BIT_INDEX_MASK) < (fromIndex & BIT_INDEX_MASK)
            ? ((words[sourceIndex] >>> fromIndex) | (words[sourceIndex + 1] & lastWordMask) << -fromIndex)
            : ((words[sourceIndex] & lastWordMask) >>> fromIndex);
        result.wordsInUse = targetWords;
        result.recalculateWordsInUse();
        return result;
    }

    public int nextSetBit(int fromIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        int u = wordIndex(fromIndex);
        if (u >= wordsInUse) return -1;
        long word = words[u] & (WORD_MASK << fromIndex);
        while (true) {
            if (word != 0) return (u * BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
            if (++u == wordsInUse) return -1;
            word = words[u];
        }
    }

    public int nextClearBit(int fromIndex) {
        if (fromIndex < 0) throw new IndexOutOfBoundsException("fromIndex < 0: " + fromIndex);
        int u = wordIndex(fromIndex);
        if (u >= wordsInUse) return fromIndex;
        long word = ~words[u] & (WORD_MASK << fromIndex);
        while (true) {
            if (word != 0) return (u * BITS_PER_WORD) + Long.numberOfTrailingZeros(word);
            if (++u == wordsInUse) return wordsInUse * BITS_PER_WORD;
            word = ~words[u];
        }
    }

    public int previousSetBit(int fromIndex) {
        if (fromIndex < 0) {
            if (fromIndex == -1) return -1;
            throw new IndexOutOfBoundsException("fromIndex < -1: " + fromIndex);
        }
        int u = wordIndex(fromIndex);
        if (u >= wordsInUse) return length() - 1;
        long word = words[u] & (WORD_MASK >>> -(fromIndex + 1));
        while (true) {
            if (word != 0) return (u + 1) * BITS_PER_WORD - 1 - Long.numberOfLeadingZeros(word);
            if (u-- == 0) return -1;
            word = words[u];
        }
    }

    public int previousClearBit(int fromIndex) {
        if (fromIndex < 0) {
            if (fromIndex == -1) return -1;
            throw new IndexOutOfBoundsException("fromIndex < -1: " + fromIndex);
        }
        int u = wordIndex(fromIndex);
        if (u >= wordsInUse) return fromIndex;
        long word = ~words[u] & (WORD_MASK >>> -(fromIndex + 1));
        while (true) {
            if (word != 0) return (u + 1) * BITS_PER_WORD - 1 - Long.numberOfLeadingZeros(word);
            if (u-- == 0) return -1;
            word = ~words[u];
        }
    }

    public int length() {
        if (wordsInUse == 0) return 0;
        return BITS_PER_WORD * (wordsInUse - 1) + (BITS_PER_WORD - Long.numberOfLeadingZeros(words[wordsInUse - 1]));
    }

    public boolean isEmpty() {
        return wordsInUse == 0;
    }

    public boolean intersects(BitSet set) {
        if (set == null) throw nullSet();
        for (int i = Math.min(wordsInUse, set.wordsInUse) - 1; i >= 0; i--) {
            if ((words[i] & set.words[i]) != 0) return true;
        }
        return false;
    }

    public int cardinality() {
        int sum = 0;
        for (int i = 0; i < wordsInUse; i++) sum += Long.bitCount(words[i]);
        return sum;
    }

    public void and(BitSet set) {
        if (this == set) return;
        if (set == null) throw nullSet();
        while (wordsInUse > set.wordsInUse) words[--wordsInUse] = 0;
        for (int i = 0; i < wordsInUse; i++) words[i] &= set.words[i];
        recalculateWordsInUse();
    }

    public void or(BitSet set) {
        if (this == set) return;
        if (set == null) throw nullSet();
        int wordsInCommon = Math.min(wordsInUse, set.wordsInUse);
        if (wordsInUse < set.wordsInUse) {
            ensureCapacity(set.wordsInUse);
            wordsInUse = set.wordsInUse;
        }
        for (int i = 0; i < wordsInCommon; i++) words[i] |= set.words[i];
        if (wordsInCommon < set.wordsInUse) System.arraycopy(set.words, wordsInCommon, words, wordsInCommon, wordsInUse - wordsInCommon);
    }

    public void xor(BitSet set) {
        if (set == null) throw nullSet();
        int wordsInCommon = Math.min(wordsInUse, set.wordsInUse);
        if (wordsInUse < set.wordsInUse) {
            ensureCapacity(set.wordsInUse);
            wordsInUse = set.wordsInUse;
        }
        for (int i = 0; i < wordsInCommon; i++) words[i] ^= set.words[i];
        if (wordsInCommon < set.wordsInUse) System.arraycopy(set.words, wordsInCommon, words, wordsInCommon, set.wordsInUse - wordsInCommon);
        recalculateWordsInUse();
    }

    public void andNot(BitSet set) {
        if (set == null) throw nullSet();
        for (int i = Math.min(wordsInUse, set.wordsInUse) - 1; i >= 0; i--) words[i] &= ~set.words[i];
        recalculateWordsInUse();
    }

    public int hashCode() {
        long h = 1234;
        for (int i = wordsInUse; --i >= 0; ) h ^= words[i] * (i + 1);
        return (int) ((h >> 32) ^ h);
    }

    public int size() {
        return words.length * BITS_PER_WORD;
    }

    public boolean equals(Object obj) {
        if (!(obj instanceof BitSet)) return false;
        if (this == obj) return true;
        BitSet set = (BitSet) obj;
        if (wordsInUse != set.wordsInUse) return false;
        for (int i = 0; i < wordsInUse; i++) {
            if (words[i] != set.words[i]) return false;
        }
        return true;
    }

    public Object clone() {
        if (!sizeIsSticky) trimToSize();
        try {
            BitSet result = (BitSet) super.clone();
            long[] w = new long[words.length];
            System.arraycopy(words, 0, w, 0, words.length);
            result.words = w;
            return result;
        } catch (CloneNotSupportedException e) {
            throw new InternalError(e);
        }
    }

    private void trimToSize() {
        if (wordsInUse != words.length) {
            long[] w = new long[wordsInUse];
            System.arraycopy(words, 0, w, 0, wordsInUse);
            words = w;
        }
    }

    /** "{i, j, ...}" in increasing order. */
    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append('{');
        int i = nextSetBit(0);
        if (i != -1) {
            b.append(i);
            while (true) {
                if (++i < 0) break;
                if ((i = nextSetBit(i)) < 0) break;
                int endOfRun = nextClearBit(i);
                do {
                    b.append(", ").append(i);
                } while (++i != endOfRun);
            }
        }
        b.append('}');
        return b.toString();
    }

    public java.util.stream.IntStream stream() {
        throw ModelStuck.unsupported("BitSet.stream");
    }
}

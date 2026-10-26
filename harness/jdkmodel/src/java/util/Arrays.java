/*
 * rocq-jvm model of java.util.Arrays (clean-room, Apache-2.0; written from the Javadoc and the
 * algorithms JDK 21 documents and uses, so that every observable effect is HotSpot's).
 *
 * Modelled (every public static method of JDK 21's Arrays, the exceptions below aside):
 *  - asList: a fixed-size list backed by the array (java.util.Arrays$ArrayList); toString,
 *    hashCode, equals, deepToString/deepEquals/deepHashCode ("[...]" for an array inside itself);
 *    equals/mismatch/compare/compareUnsigned (whole arrays and ranges, with or without a
 *    Comparator) as ArraysSupport.mismatch: float/double by floatToIntBits/doubleToLongBits,
 *    Objects.equals for objects (no equals call for identical elements), the comparator or
 *    compareTo only on elements that are not identical.
 *  - sort/parallelSort of primitive arrays: the sorted order is unique, so a merge sort gives
 *    DualPivotQuicksort's result; float/double run the JDK's phases exactly (-0.0 turned into
 *    0.0 and the NaNs moved to the end in the JDK's order, then the negative zeros put back).
 *  - sort/parallelSort of object arrays: JDK 21's TimSort (ComparableTimSort for the natural
 *    ordering) transcribed, so the sequence of compare/compareTo calls, the partially sorted
 *    array after an exception from a comparator and "Comparison method violates its general
 *    contract!" are the JDK's. parallelSort of at most 8192 elements runs TimSort with
 *    Arrays.NaturalOrder in the caller thread as in the JDK.
 *  - binarySearch (all overloads; the JDK's probe sequence), fill, copyOf/copyOfRange (a clone
 *    for a primitive array of the same length/whole range, Array.newInstance of newType's
 *    component type), setAll, stream (model stream pipelines, ORDERED|SIZED).
 *  - parallelPrefix of at most 16 elements (ArrayPrefixHelpers runs a range of at most
 *    MIN_PARTITION = 16 as one leaf task in the caller thread: a sequential cumulation),
 *    parallelSetAll of at most 1 element (a parallel IntStream.range(0, n).forEach that does
 *    not split).
 *  - Exception classes and messages as HotSpot 21: rangeCheck's IllegalArgumentException /
 *    ArrayIndexOutOfBoundsException, copyOfRange's "from > to", Objects.requireNonNull (null
 *    message), and the helpful NullPointerException texts of the JDK's implicit null checks
 *    (`Cannot read the array length because "a" is null`, `... "original" ...`, `Cannot invoke
 *    "Object.getClass()" because "original" is null`, `Cannot invoke
 *    "java.lang.Comparable.compareTo(Object)" because "midVal" is null`, the TimSort sites
 *    "a[runHi]", "pivot", "key", "a[cursor2]", "tmp[cursor2]" ...), thrown explicitly here.
 *    Natural-ordering compareTo of String/boxes with an argument of another class throws the
 *    ClassCastException of the bridge method's cast with HotSpot's message.
 * STUCK: spliterator (no Spliterator model), parallelSort of more than 8192 objects (the
 * ForkJoin merge depends on the pool), parallelPrefix of more than 16 elements and
 * parallelSetAll of more than one element (the order of the user function's calls depends on
 * the common pool), arrays beyond the machine's bound (2^20 elements).
 * java.util.Arrays.useLegacyMergeSort is assumed unset (the default).
 * This class has no static initialiser.
 */
package java.util;

import java.util.function.BinaryOperator;
import java.util.function.Consumer;
import java.util.function.DoubleBinaryOperator;
import java.util.function.IntBinaryOperator;
import java.util.function.IntFunction;
import java.util.function.IntToDoubleFunction;
import java.util.function.IntToLongFunction;
import java.util.function.IntUnaryOperator;
import java.util.function.LongBinaryOperator;
import java.util.function.UnaryOperator;
import java.util.stream.DoubleStream;
import java.util.stream.IntStream;
import java.util.stream.LongStream;
import java.util.stream.ModelStreams;
import java.util.stream.Stream;

public class Arrays {
    private Arrays() {
    }

    @SafeVarargs
    @SuppressWarnings("varargs")
    public static <T> List<T> asList(T... a) {
        return new ArrayList<>(a);
    }

    // ---- helpers ----

    static void rangeCheck(int arrayLength, int fromIndex, int toIndex) {
        if (fromIndex > toIndex) throw new IllegalArgumentException("fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
        if (fromIndex < 0) throw new ArrayIndexOutOfBoundsException("Array index out of range: " + fromIndex);
        if (toIndex > arrayLength) throw new ArrayIndexOutOfBoundsException("Array index out of range: " + toIndex);
    }

    private static void requireNonNull(Object o) {
        if (o == null) throw new NullPointerException();
    }

    /** Objects.equals. */
    private static boolean oeq(Object a, Object b) {
        return (a == b) || (a != null && a.equals(b));
    }

    private static int icmp(int x, int y) {
        return (x < y) ? -1 : ((x == y) ? 0 : 1);
    }

    private static int lcmp(long x, long y) {
        return (x < y) ? -1 : ((x == y) ? 0 : 1);
    }

    /** Float.compare. */
    private static int fcmp(float f1, float f2) {
        if (f1 < f2) return -1;
        if (f1 > f2) return 1;
        int thisBits = Float.floatToIntBits(f1);
        int anotherBits = Float.floatToIntBits(f2);
        return (thisBits == anotherBits ? 0 : (thisBits < anotherBits ? -1 : 1));
    }

    /** Double.compare. */
    private static int dcmp(double d1, double d2) {
        if (d1 < d2) return -1;
        if (d1 > d2) return 1;
        long thisBits = Double.doubleToLongBits(d1);
        long anotherBits = Double.doubleToLongBits(d2);
        return (thisBits == anotherBits ? 0 : (thisBits < anotherBits ? -1 : 1));
    }

    /**
     * ((Comparable) x).compareTo(y) at a JDK call site whose receiver expression is [site]: the
     * helpful NullPointerException for a null receiver, and the ClassCastException that the
     * bridge compareTo(Object) of String and the boxes throws for an argument of another class.
     */
    @SuppressWarnings({"unchecked", "rawtypes"})
    static int natCmp(Object x, Object y, String site) {
        if (x == null) {
            throw new NullPointerException("Cannot invoke \"java.lang.Comparable.compareTo(Object)\" because \"" + site + "\" is null");
        }
        if (y != null && finalJdkComparable(x) && x.getClass() != y.getClass()) {
            String a = y.getClass().getName(), b = x.getClass().getName();
            if (!javaBaseName(a)) throw ModelStuck.unsupported("compareTo: ClassCastException message for a user class");
            throw new ClassCastException("class " + a + " cannot be cast to class " + b + " (" + a + " and " + b
                + " are in module java.base of loader 'bootstrap')");
        }
        return ((Comparable) x).compareTo(y);
    }

    /** String and the boxes: final classes whose bridge compareTo(Object) casts its argument. */
    private static boolean finalJdkComparable(Object x) {
        return x instanceof String || x instanceof Integer || x instanceof Long || x instanceof Short || x instanceof Byte
            || x instanceof Character || x instanceof Boolean || x instanceof Double || x instanceof Float;
    }

    /** A class of module java.base (the model's classes are java.*), or an array of them or of a
     *  primitive type: HotSpot's ClassCastException message names the bootstrap loader. */
    static boolean javaBaseName(String n) {
        String e = n;
        while (e.startsWith("[")) e = e.substring(1);
        return e.length() == 1 || e.startsWith("java.") || e.startsWith("Ljava.");
    }

    // ---- generated by gen_arrays.py: the primitive overloads ----

    private static int mm(long[] a, int aFrom, long[] b, int bFrom, int length) {
        for (int i = 0; i < length; i++) {
            if (a[aFrom + i] != b[bFrom + i]) return i;
        }
        return -1;
    }

    private static int mm(int[] a, int aFrom, int[] b, int bFrom, int length) {
        for (int i = 0; i < length; i++) {
            if (a[aFrom + i] != b[bFrom + i]) return i;
        }
        return -1;
    }

    private static int mm(short[] a, int aFrom, short[] b, int bFrom, int length) {
        for (int i = 0; i < length; i++) {
            if (a[aFrom + i] != b[bFrom + i]) return i;
        }
        return -1;
    }

    private static int mm(char[] a, int aFrom, char[] b, int bFrom, int length) {
        for (int i = 0; i < length; i++) {
            if (a[aFrom + i] != b[bFrom + i]) return i;
        }
        return -1;
    }

    private static int mm(byte[] a, int aFrom, byte[] b, int bFrom, int length) {
        for (int i = 0; i < length; i++) {
            if (a[aFrom + i] != b[bFrom + i]) return i;
        }
        return -1;
    }

    private static int mm(boolean[] a, int aFrom, boolean[] b, int bFrom, int length) {
        for (int i = 0; i < length; i++) {
            if (a[aFrom + i] != b[bFrom + i]) return i;
        }
        return -1;
    }

    private static int mm(double[] a, int aFrom, double[] b, int bFrom, int length) {
        for (int i = 0; i < length; i++) {
            if (Double.doubleToLongBits(a[aFrom + i]) != Double.doubleToLongBits(b[bFrom + i])) return i;
        }
        return -1;
    }

    private static int mm(float[] a, int aFrom, float[] b, int bFrom, int length) {
        for (int i = 0; i < length; i++) {
            if (Float.floatToIntBits(a[aFrom + i]) != Float.floatToIntBits(b[bFrom + i])) return i;
        }
        return -1;
    }

    public static void sort(int[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void sort(int[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    public static void parallelSort(int[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void parallelSort(int[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    private static void msort(int[] a, int lo, int hi) {
        if (hi - lo < 2) return;
        msort(a, new int[hi - lo], lo, hi);
    }

    private static void msort(int[] a, int[] t, int lo, int hi) {
        if (hi - lo <= 12) {
            for (int i = lo + 1; i < hi; i++) {
                int v = a[i];
                int j = i - 1;
                while (j >= lo && a[j] > v) {
                    a[j + 1] = a[j];
                    j--;
                }
                a[j + 1] = v;
            }
            return;
        }
        int mid = (lo + hi) >>> 1;
        msort(a, t, lo, mid);
        msort(a, t, mid, hi);
        if (a[mid - 1] <= a[mid]) return;
        int i = lo, j = mid, k = 0;
        while (i < mid && j < hi) t[k++] = (a[j] < a[i]) ? a[j++] : a[i++];
        while (i < mid) t[k++] = a[i++];
        while (j < hi) t[k++] = a[j++];
        System.arraycopy(t, 0, a, lo, k);
    }

    public static void sort(long[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void sort(long[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    public static void parallelSort(long[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void parallelSort(long[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    private static void msort(long[] a, int lo, int hi) {
        if (hi - lo < 2) return;
        msort(a, new long[hi - lo], lo, hi);
    }

    private static void msort(long[] a, long[] t, int lo, int hi) {
        if (hi - lo <= 12) {
            for (int i = lo + 1; i < hi; i++) {
                long v = a[i];
                int j = i - 1;
                while (j >= lo && a[j] > v) {
                    a[j + 1] = a[j];
                    j--;
                }
                a[j + 1] = v;
            }
            return;
        }
        int mid = (lo + hi) >>> 1;
        msort(a, t, lo, mid);
        msort(a, t, mid, hi);
        if (a[mid - 1] <= a[mid]) return;
        int i = lo, j = mid, k = 0;
        while (i < mid && j < hi) t[k++] = (a[j] < a[i]) ? a[j++] : a[i++];
        while (i < mid) t[k++] = a[i++];
        while (j < hi) t[k++] = a[j++];
        System.arraycopy(t, 0, a, lo, k);
    }

    public static void sort(short[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void sort(short[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    public static void parallelSort(short[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void parallelSort(short[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    private static void msort(short[] a, int lo, int hi) {
        if (hi - lo < 2) return;
        msort(a, new short[hi - lo], lo, hi);
    }

    private static void msort(short[] a, short[] t, int lo, int hi) {
        if (hi - lo <= 12) {
            for (int i = lo + 1; i < hi; i++) {
                short v = a[i];
                int j = i - 1;
                while (j >= lo && a[j] > v) {
                    a[j + 1] = a[j];
                    j--;
                }
                a[j + 1] = v;
            }
            return;
        }
        int mid = (lo + hi) >>> 1;
        msort(a, t, lo, mid);
        msort(a, t, mid, hi);
        if (a[mid - 1] <= a[mid]) return;
        int i = lo, j = mid, k = 0;
        while (i < mid && j < hi) t[k++] = (a[j] < a[i]) ? a[j++] : a[i++];
        while (i < mid) t[k++] = a[i++];
        while (j < hi) t[k++] = a[j++];
        System.arraycopy(t, 0, a, lo, k);
    }

    public static void sort(char[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void sort(char[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    public static void parallelSort(char[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void parallelSort(char[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    private static void msort(char[] a, int lo, int hi) {
        if (hi - lo < 2) return;
        msort(a, new char[hi - lo], lo, hi);
    }

    private static void msort(char[] a, char[] t, int lo, int hi) {
        if (hi - lo <= 12) {
            for (int i = lo + 1; i < hi; i++) {
                char v = a[i];
                int j = i - 1;
                while (j >= lo && a[j] > v) {
                    a[j + 1] = a[j];
                    j--;
                }
                a[j + 1] = v;
            }
            return;
        }
        int mid = (lo + hi) >>> 1;
        msort(a, t, lo, mid);
        msort(a, t, mid, hi);
        if (a[mid - 1] <= a[mid]) return;
        int i = lo, j = mid, k = 0;
        while (i < mid && j < hi) t[k++] = (a[j] < a[i]) ? a[j++] : a[i++];
        while (i < mid) t[k++] = a[i++];
        while (j < hi) t[k++] = a[j++];
        System.arraycopy(t, 0, a, lo, k);
    }

    public static void sort(byte[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void sort(byte[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    public static void parallelSort(byte[] a) {
        msort(a, 0, len(a, "a"));
    }

    public static void parallelSort(byte[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        msort(a, fromIndex, toIndex);
    }

    private static void msort(byte[] a, int lo, int hi) {
        if (hi - lo < 2) return;
        msort(a, new byte[hi - lo], lo, hi);
    }

    private static void msort(byte[] a, byte[] t, int lo, int hi) {
        if (hi - lo <= 12) {
            for (int i = lo + 1; i < hi; i++) {
                byte v = a[i];
                int j = i - 1;
                while (j >= lo && a[j] > v) {
                    a[j + 1] = a[j];
                    j--;
                }
                a[j + 1] = v;
            }
            return;
        }
        int mid = (lo + hi) >>> 1;
        msort(a, t, lo, mid);
        msort(a, t, mid, hi);
        if (a[mid - 1] <= a[mid]) return;
        int i = lo, j = mid, k = 0;
        while (i < mid && j < hi) t[k++] = (a[j] < a[i]) ? a[j++] : a[i++];
        while (i < mid) t[k++] = a[i++];
        while (j < hi) t[k++] = a[j++];
        System.arraycopy(t, 0, a, lo, k);
    }

    public static void sort(float[] a) {
        sortFD(a, 0, len(a, "a"));
    }

    public static void sort(float[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        sortFD(a, fromIndex, toIndex);
    }

    public static void parallelSort(float[] a) {
        sortFD(a, 0, len(a, "a"));
    }

    public static void parallelSort(float[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        sortFD(a, fromIndex, toIndex);
    }

    private static void msort(float[] a, int lo, int hi) {
        if (hi - lo < 2) return;
        msort(a, new float[hi - lo], lo, hi);
    }

    private static void msort(float[] a, float[] t, int lo, int hi) {
        if (hi - lo <= 12) {
            for (int i = lo + 1; i < hi; i++) {
                float v = a[i];
                int j = i - 1;
                while (j >= lo && a[j] > v) {
                    a[j + 1] = a[j];
                    j--;
                }
                a[j + 1] = v;
            }
            return;
        }
        int mid = (lo + hi) >>> 1;
        msort(a, t, lo, mid);
        msort(a, t, mid, hi);
        if (a[mid - 1] <= a[mid]) return;
        int i = lo, j = mid, k = 0;
        while (i < mid && j < hi) t[k++] = (a[j] < a[i]) ? a[j++] : a[i++];
        while (i < mid) t[k++] = a[i++];
        while (j < hi) t[k++] = a[j++];
        System.arraycopy(t, 0, a, lo, k);
    }

    public static void sort(double[] a) {
        sortFD(a, 0, len(a, "a"));
    }

    public static void sort(double[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        sortFD(a, fromIndex, toIndex);
    }

    public static void parallelSort(double[] a) {
        sortFD(a, 0, len(a, "a"));
    }

    public static void parallelSort(double[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        sortFD(a, fromIndex, toIndex);
    }

    private static void msort(double[] a, int lo, int hi) {
        if (hi - lo < 2) return;
        msort(a, new double[hi - lo], lo, hi);
    }

    private static void msort(double[] a, double[] t, int lo, int hi) {
        if (hi - lo <= 12) {
            for (int i = lo + 1; i < hi; i++) {
                double v = a[i];
                int j = i - 1;
                while (j >= lo && a[j] > v) {
                    a[j + 1] = a[j];
                    j--;
                }
                a[j + 1] = v;
            }
            return;
        }
        int mid = (lo + hi) >>> 1;
        msort(a, t, lo, mid);
        msort(a, t, mid, hi);
        if (a[mid - 1] <= a[mid]) return;
        int i = lo, j = mid, k = 0;
        while (i < mid && j < hi) t[k++] = (a[j] < a[i]) ? a[j++] : a[i++];
        while (i < mid) t[k++] = a[i++];
        while (j < hi) t[k++] = a[j++];
        System.arraycopy(t, 0, a, lo, k);
    }

    /** DualPivotQuicksort.sort(float[], parallelism, low, high): phase 1 turns -0.0 into 0.0 and moves the
     *  NaNs to the end (in the JDK's order), the rest is sorted, phase 3 restores the negative zeros. */
    private static void sortFD(float[] a, int low, int high) {
        int numNegativeZero = 0;
        for (int k = high; k > low; ) {
            float ak = a[--k];
            if (ak == 0.0f && Float.floatToRawIntBits(ak) < 0) {
                numNegativeZero += 1;
                a[k] = 0.0f;
            } else if (ak != ak) {
                a[k] = a[--high];
                a[high] = ak;
            }
        }
        msort(a, low, high);
        if (++numNegativeZero == 1) return;
        while (low <= high) {
            int middle = (low + high) >>> 1;
            if (a[middle] < 0) low = middle + 1;
            else high = middle - 1;
        }
        while (--numNegativeZero > 0) a[++high] = -0.0f;
    }

    /** DualPivotQuicksort.sort(double[], parallelism, low, high): phase 1 turns -0.0 into 0.0 and moves the
     *  NaNs to the end (in the JDK's order), the rest is sorted, phase 3 restores the negative zeros. */
    private static void sortFD(double[] a, int low, int high) {
        int numNegativeZero = 0;
        for (int k = high; k > low; ) {
            double ak = a[--k];
            if (ak == 0.0d && Double.doubleToRawLongBits(ak) < 0) {
                numNegativeZero += 1;
                a[k] = 0.0d;
            } else if (ak != ak) {
                a[k] = a[--high];
                a[high] = ak;
            }
        }
        msort(a, low, high);
        if (++numNegativeZero == 1) return;
        while (low <= high) {
            int middle = (low + high) >>> 1;
            if (a[middle] < 0) low = middle + 1;
            else high = middle - 1;
        }
        while (--numNegativeZero > 0) a[++high] = -0.0d;
    }

    public static int binarySearch(int[] a, int key) {
        return binarySearch0(a, 0, len(a, "a"), key);
    }

    public static int binarySearch(int[] a, int fromIndex, int toIndex, int key) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key);
    }

    private static int binarySearch0(int[] a, int fromIndex, int toIndex, int key) {
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            int midVal = a[mid];
            if (midVal < key) low = mid + 1;
            else if (midVal > key) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    public static int binarySearch(long[] a, long key) {
        return binarySearch0(a, 0, len(a, "a"), key);
    }

    public static int binarySearch(long[] a, int fromIndex, int toIndex, long key) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key);
    }

    private static int binarySearch0(long[] a, int fromIndex, int toIndex, long key) {
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            long midVal = a[mid];
            if (midVal < key) low = mid + 1;
            else if (midVal > key) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    public static int binarySearch(short[] a, short key) {
        return binarySearch0(a, 0, len(a, "a"), key);
    }

    public static int binarySearch(short[] a, int fromIndex, int toIndex, short key) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key);
    }

    private static int binarySearch0(short[] a, int fromIndex, int toIndex, short key) {
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            short midVal = a[mid];
            if (midVal < key) low = mid + 1;
            else if (midVal > key) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    public static int binarySearch(char[] a, char key) {
        return binarySearch0(a, 0, len(a, "a"), key);
    }

    public static int binarySearch(char[] a, int fromIndex, int toIndex, char key) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key);
    }

    private static int binarySearch0(char[] a, int fromIndex, int toIndex, char key) {
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            char midVal = a[mid];
            if (midVal < key) low = mid + 1;
            else if (midVal > key) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    public static int binarySearch(byte[] a, byte key) {
        return binarySearch0(a, 0, len(a, "a"), key);
    }

    public static int binarySearch(byte[] a, int fromIndex, int toIndex, byte key) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key);
    }

    private static int binarySearch0(byte[] a, int fromIndex, int toIndex, byte key) {
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            byte midVal = a[mid];
            if (midVal < key) low = mid + 1;
            else if (midVal > key) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    public static int binarySearch(float[] a, float key) {
        return binarySearch0(a, 0, len(a, "a"), key);
    }

    public static int binarySearch(float[] a, int fromIndex, int toIndex, float key) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key);
    }

    private static int binarySearch0(float[] a, int fromIndex, int toIndex, float key) {
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            float midVal = a[mid];
            if (midVal < key) low = mid + 1;
            else if (midVal > key) high = mid - 1;
            else {
                int midBits = Float.floatToIntBits(midVal);
                int keyBits = Float.floatToIntBits(key);
                if (midBits == keyBits) return mid;
                else if (midBits < keyBits) low = mid + 1;
                else high = mid - 1;
            }
        }
        return -(low + 1);
    }

    public static int binarySearch(double[] a, double key) {
        return binarySearch0(a, 0, len(a, "a"), key);
    }

    public static int binarySearch(double[] a, int fromIndex, int toIndex, double key) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key);
    }

    private static int binarySearch0(double[] a, int fromIndex, int toIndex, double key) {
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            double midVal = a[mid];
            if (midVal < key) low = mid + 1;
            else if (midVal > key) high = mid - 1;
            else {
                long midBits = Double.doubleToLongBits(midVal);
                long keyBits = Double.doubleToLongBits(key);
                if (midBits == keyBits) return mid;
                else if (midBits < keyBits) low = mid + 1;
                else high = mid - 1;
            }
        }
        return -(low + 1);
    }

    public static boolean equals(long[] a, long[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        return mm(a, 0, a2, 0, length) < 0;
    }

    public static boolean equals(long[] a, int aFromIndex, int aToIndex, long[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        return mm(a, aFromIndex, b, bFromIndex, aLength) < 0;
    }

    public static boolean equals(int[] a, int[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        return mm(a, 0, a2, 0, length) < 0;
    }

    public static boolean equals(int[] a, int aFromIndex, int aToIndex, int[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        return mm(a, aFromIndex, b, bFromIndex, aLength) < 0;
    }

    public static boolean equals(short[] a, short[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        return mm(a, 0, a2, 0, length) < 0;
    }

    public static boolean equals(short[] a, int aFromIndex, int aToIndex, short[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        return mm(a, aFromIndex, b, bFromIndex, aLength) < 0;
    }

    public static boolean equals(char[] a, char[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        return mm(a, 0, a2, 0, length) < 0;
    }

    public static boolean equals(char[] a, int aFromIndex, int aToIndex, char[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        return mm(a, aFromIndex, b, bFromIndex, aLength) < 0;
    }

    public static boolean equals(byte[] a, byte[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        return mm(a, 0, a2, 0, length) < 0;
    }

    public static boolean equals(byte[] a, int aFromIndex, int aToIndex, byte[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        return mm(a, aFromIndex, b, bFromIndex, aLength) < 0;
    }

    public static boolean equals(boolean[] a, boolean[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        return mm(a, 0, a2, 0, length) < 0;
    }

    public static boolean equals(boolean[] a, int aFromIndex, int aToIndex, boolean[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        return mm(a, aFromIndex, b, bFromIndex, aLength) < 0;
    }

    public static boolean equals(double[] a, double[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        return mm(a, 0, a2, 0, length) < 0;
    }

    public static boolean equals(double[] a, int aFromIndex, int aToIndex, double[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        return mm(a, aFromIndex, b, bFromIndex, aLength) < 0;
    }

    public static boolean equals(float[] a, float[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        return mm(a, 0, a2, 0, length) < 0;
    }

    public static boolean equals(float[] a, int aFromIndex, int aToIndex, float[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        return mm(a, aFromIndex, b, bFromIndex, aLength) < 0;
    }

    public static void fill(long[] a, long val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(long[] a, int fromIndex, int toIndex, long val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    public static void fill(int[] a, int val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(int[] a, int fromIndex, int toIndex, int val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    public static void fill(short[] a, short val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(short[] a, int fromIndex, int toIndex, short val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    public static void fill(char[] a, char val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(char[] a, int fromIndex, int toIndex, char val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    public static void fill(byte[] a, byte val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(byte[] a, int fromIndex, int toIndex, byte val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    public static void fill(boolean[] a, boolean val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(boolean[] a, int fromIndex, int toIndex, boolean val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    public static void fill(double[] a, double val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(double[] a, int fromIndex, int toIndex, double val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    public static void fill(float[] a, float val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(float[] a, int fromIndex, int toIndex, float val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    public static byte[] copyOf(byte[] original, int newLength) {
        if (newLength == len(original, "original")) return original.clone();
        byte[] copy = new byte[newLength];
        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));
        return copy;
    }

    public static byte[] copyOfRange(byte[] original, int from, int to) {
        if (from != 0 || to != len(original, "original")) {
            if (to < from) throw new IllegalArgumentException(from + " > " + to);
            int newLength = to - from;
            byte[] copy = new byte[newLength];
            System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
            return copy;
        }
        return original.clone();
    }

    public static short[] copyOf(short[] original, int newLength) {
        if (newLength == len(original, "original")) return original.clone();
        short[] copy = new short[newLength];
        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));
        return copy;
    }

    public static short[] copyOfRange(short[] original, int from, int to) {
        if (from != 0 || to != len(original, "original")) {
            if (to < from) throw new IllegalArgumentException(from + " > " + to);
            int newLength = to - from;
            short[] copy = new short[newLength];
            System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
            return copy;
        }
        return original.clone();
    }

    public static int[] copyOf(int[] original, int newLength) {
        if (newLength == len(original, "original")) return original.clone();
        int[] copy = new int[newLength];
        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));
        return copy;
    }

    public static int[] copyOfRange(int[] original, int from, int to) {
        if (from != 0 || to != len(original, "original")) {
            if (to < from) throw new IllegalArgumentException(from + " > " + to);
            int newLength = to - from;
            int[] copy = new int[newLength];
            System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
            return copy;
        }
        return original.clone();
    }

    public static long[] copyOf(long[] original, int newLength) {
        if (newLength == len(original, "original")) return original.clone();
        long[] copy = new long[newLength];
        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));
        return copy;
    }

    public static long[] copyOfRange(long[] original, int from, int to) {
        if (from != 0 || to != len(original, "original")) {
            if (to < from) throw new IllegalArgumentException(from + " > " + to);
            int newLength = to - from;
            long[] copy = new long[newLength];
            System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
            return copy;
        }
        return original.clone();
    }

    public static char[] copyOf(char[] original, int newLength) {
        if (newLength == len(original, "original")) return original.clone();
        char[] copy = new char[newLength];
        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));
        return copy;
    }

    public static char[] copyOfRange(char[] original, int from, int to) {
        if (from != 0 || to != len(original, "original")) {
            if (to < from) throw new IllegalArgumentException(from + " > " + to);
            int newLength = to - from;
            char[] copy = new char[newLength];
            System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
            return copy;
        }
        return original.clone();
    }

    public static float[] copyOf(float[] original, int newLength) {
        if (newLength == len(original, "original")) return original.clone();
        float[] copy = new float[newLength];
        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));
        return copy;
    }

    public static float[] copyOfRange(float[] original, int from, int to) {
        if (from != 0 || to != len(original, "original")) {
            if (to < from) throw new IllegalArgumentException(from + " > " + to);
            int newLength = to - from;
            float[] copy = new float[newLength];
            System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
            return copy;
        }
        return original.clone();
    }

    public static double[] copyOf(double[] original, int newLength) {
        if (newLength == len(original, "original")) return original.clone();
        double[] copy = new double[newLength];
        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));
        return copy;
    }

    public static double[] copyOfRange(double[] original, int from, int to) {
        if (from != 0 || to != len(original, "original")) {
            if (to < from) throw new IllegalArgumentException(from + " > " + to);
            int newLength = to - from;
            double[] copy = new double[newLength];
            System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
            return copy;
        }
        return original.clone();
    }

    public static boolean[] copyOf(boolean[] original, int newLength) {
        if (newLength == len(original, "original")) return original.clone();
        boolean[] copy = new boolean[newLength];
        System.arraycopy(original, 0, copy, 0, Math.min(original.length, newLength));
        return copy;
    }

    public static boolean[] copyOfRange(boolean[] original, int from, int to) {
        if (from != 0 || to != len(original, "original")) {
            if (to < from) throw new IllegalArgumentException(from + " > " + to);
            int newLength = to - from;
            boolean[] copy = new boolean[newLength];
            System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
            return copy;
        }
        return original.clone();
    }

    public static int compare(long[] a, long[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return lcmp(a[i], b[i]);
        return a.length - b.length;
    }

    public static int compare(long[] a, int aFromIndex, int aToIndex, long[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return lcmp(a[aFromIndex + i], b[bFromIndex + i]);
        return aLength - bLength;
    }

    public static int compareUnsigned(long[] a, long[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return lcmp(a[i] + Long.MIN_VALUE, b[i] + Long.MIN_VALUE);
        return a.length - b.length;
    }

    public static int compareUnsigned(long[] a, int aFromIndex, int aToIndex, long[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return lcmp(a[aFromIndex + i] + Long.MIN_VALUE, b[bFromIndex + i] + Long.MIN_VALUE);
        return aLength - bLength;
    }

    public static int compare(int[] a, int[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return icmp(a[i], b[i]);
        return a.length - b.length;
    }

    public static int compare(int[] a, int aFromIndex, int aToIndex, int[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return icmp(a[aFromIndex + i], b[bFromIndex + i]);
        return aLength - bLength;
    }

    public static int compareUnsigned(int[] a, int[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return icmp(a[i] + Integer.MIN_VALUE, b[i] + Integer.MIN_VALUE);
        return a.length - b.length;
    }

    public static int compareUnsigned(int[] a, int aFromIndex, int aToIndex, int[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return icmp(a[aFromIndex + i] + Integer.MIN_VALUE, b[bFromIndex + i] + Integer.MIN_VALUE);
        return aLength - bLength;
    }

    public static int compare(short[] a, short[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return a[i] - b[i];
        return a.length - b.length;
    }

    public static int compare(short[] a, int aFromIndex, int aToIndex, short[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return a[aFromIndex + i] - b[bFromIndex + i];
        return aLength - bLength;
    }

    public static int compareUnsigned(short[] a, short[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return (a[i] & 0xffff) - (b[i] & 0xffff);
        return a.length - b.length;
    }

    public static int compareUnsigned(short[] a, int aFromIndex, int aToIndex, short[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return (a[aFromIndex + i] & 0xffff) - (b[bFromIndex + i] & 0xffff);
        return aLength - bLength;
    }

    public static int compare(char[] a, char[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return a[i] - b[i];
        return a.length - b.length;
    }

    public static int compare(char[] a, int aFromIndex, int aToIndex, char[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return a[aFromIndex + i] - b[bFromIndex + i];
        return aLength - bLength;
    }

    public static int compare(byte[] a, byte[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return a[i] - b[i];
        return a.length - b.length;
    }

    public static int compare(byte[] a, int aFromIndex, int aToIndex, byte[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return a[aFromIndex + i] - b[bFromIndex + i];
        return aLength - bLength;
    }

    public static int compareUnsigned(byte[] a, byte[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return (a[i] & 0xff) - (b[i] & 0xff);
        return a.length - b.length;
    }

    public static int compareUnsigned(byte[] a, int aFromIndex, int aToIndex, byte[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return (a[aFromIndex + i] & 0xff) - (b[bFromIndex + i] & 0xff);
        return aLength - bLength;
    }

    public static int compare(boolean[] a, boolean[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return (a[i] == b[i]) ? 0 : (a[i] ? 1 : -1);
        return a.length - b.length;
    }

    public static int compare(boolean[] a, int aFromIndex, int aToIndex, boolean[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return (a[aFromIndex + i] == b[bFromIndex + i]) ? 0 : (a[aFromIndex + i] ? 1 : -1);
        return aLength - bLength;
    }

    public static int compare(double[] a, double[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return dcmp(a[i], b[i]);
        return a.length - b.length;
    }

    public static int compare(double[] a, int aFromIndex, int aToIndex, double[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return dcmp(a[aFromIndex + i], b[bFromIndex + i]);
        return aLength - bLength;
    }

    public static int compare(float[] a, float[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int i = mm(a, 0, b, 0, Math.min(a.length, b.length));
        if (i >= 0) return fcmp(a[i], b[i]);
        return a.length - b.length;
    }

    public static int compare(float[] a, int aFromIndex, int aToIndex, float[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int i = mm(a, aFromIndex, b, bFromIndex, Math.min(aLength, bLength));
        if (i >= 0) return fcmp(a[aFromIndex + i], b[bFromIndex + i]);
        return aLength - bLength;
    }

    public static int mismatch(long[] a, long[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        int i = mm(a, 0, b, 0, length);
        return (i < 0 && a.length != b.length) ? length : i;
    }

    public static int mismatch(long[] a, int aFromIndex, int aToIndex, long[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        int i = mm(a, aFromIndex, b, bFromIndex, length);
        return (i < 0 && aLength != bLength) ? length : i;
    }

    public static int mismatch(int[] a, int[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        int i = mm(a, 0, b, 0, length);
        return (i < 0 && a.length != b.length) ? length : i;
    }

    public static int mismatch(int[] a, int aFromIndex, int aToIndex, int[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        int i = mm(a, aFromIndex, b, bFromIndex, length);
        return (i < 0 && aLength != bLength) ? length : i;
    }

    public static int mismatch(short[] a, short[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        int i = mm(a, 0, b, 0, length);
        return (i < 0 && a.length != b.length) ? length : i;
    }

    public static int mismatch(short[] a, int aFromIndex, int aToIndex, short[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        int i = mm(a, aFromIndex, b, bFromIndex, length);
        return (i < 0 && aLength != bLength) ? length : i;
    }

    public static int mismatch(char[] a, char[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        int i = mm(a, 0, b, 0, length);
        return (i < 0 && a.length != b.length) ? length : i;
    }

    public static int mismatch(char[] a, int aFromIndex, int aToIndex, char[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        int i = mm(a, aFromIndex, b, bFromIndex, length);
        return (i < 0 && aLength != bLength) ? length : i;
    }

    public static int mismatch(byte[] a, byte[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        int i = mm(a, 0, b, 0, length);
        return (i < 0 && a.length != b.length) ? length : i;
    }

    public static int mismatch(byte[] a, int aFromIndex, int aToIndex, byte[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        int i = mm(a, aFromIndex, b, bFromIndex, length);
        return (i < 0 && aLength != bLength) ? length : i;
    }

    public static int mismatch(boolean[] a, boolean[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        int i = mm(a, 0, b, 0, length);
        return (i < 0 && a.length != b.length) ? length : i;
    }

    public static int mismatch(boolean[] a, int aFromIndex, int aToIndex, boolean[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        int i = mm(a, aFromIndex, b, bFromIndex, length);
        return (i < 0 && aLength != bLength) ? length : i;
    }

    public static int mismatch(double[] a, double[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        int i = mm(a, 0, b, 0, length);
        return (i < 0 && a.length != b.length) ? length : i;
    }

    public static int mismatch(double[] a, int aFromIndex, int aToIndex, double[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        int i = mm(a, aFromIndex, b, bFromIndex, length);
        return (i < 0 && aLength != bLength) ? length : i;
    }

    public static int mismatch(float[] a, float[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        int i = mm(a, 0, b, 0, length);
        return (i < 0 && a.length != b.length) ? length : i;
    }

    public static int mismatch(float[] a, int aFromIndex, int aToIndex, float[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        int i = mm(a, aFromIndex, b, bFromIndex, length);
        return (i < 0 && aLength != bLength) ? length : i;
    }

    private static int len(long[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    private static int len(int[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    private static int len(short[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    private static int len(char[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    private static int len(byte[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    private static int len(boolean[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    private static int len(double[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    private static int len(float[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    private static int len(Object[] a, String what) {
        if (a == null) throw ImmutableCollections.lengthOfNull(what);
        return a.length;
    }

    // ---- end of the generated part ----

    // ---- toString / hashCode (whole arrays) ----

    public static String toString(Object[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(String.valueOf(a[i]));
        }
        return b.append(']').toString();
    }

    public static String toString(int[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static String toString(long[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static String toString(byte[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static String toString(short[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static String toString(char[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static String toString(boolean[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static String toString(float[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static String toString(double[] a) {
        if (a == null) return "null";
        StringBuilder b = new StringBuilder("[");
        for (int i = 0; i < a.length; i++) {
            if (i > 0) b.append(", ");
            b.append(a[i]);
        }
        return b.append(']').toString();
    }

    public static int hashCode(byte[] a) {
        if (a == null) return 0;
        int result = 1;
        for (byte e : a) result = 31 * result + e;
        return result;
    }

    public static int hashCode(short[] a) {
        if (a == null) return 0;
        int result = 1;
        for (short e : a) result = 31 * result + e;
        return result;
    }

    public static int hashCode(char[] a) {
        if (a == null) return 0;
        int result = 1;
        for (char e : a) result = 31 * result + e;
        return result;
    }

    public static int hashCode(boolean[] a) {
        if (a == null) return 0;
        int result = 1;
        for (boolean e : a) result = 31 * result + (e ? 1231 : 1237);
        return result;
    }

    public static int hashCode(float[] a) {
        if (a == null) return 0;
        int result = 1;
        for (float e : a) result = 31 * result + Float.floatToIntBits(e);
        return result;
    }

    public static int hashCode(double[] a) {
        if (a == null) return 0;
        int result = 1;
        for (double e : a) result = 31 * result + (int) (Double.doubleToLongBits(e) ^ (Double.doubleToLongBits(e) >>> 32));
        return result;
    }

    public static int hashCode(long[] a) {
        if (a == null) return 0;
        int result = 1;
        for (long e : a) result = 31 * result + (int) (e ^ (e >>> 32));
        return result;
    }

    public static int hashCode(int[] a) {
        if (a == null) return 0;
        int h = 1;
        for (int e : a) h = 31 * h + e;
        return h;
    }

    public static int hashCode(Object[] a) {
        if (a == null) return 0;
        int h = 1;
        for (Object e : a) h = 31 * h + (e == null ? 0 : e.hashCode());
        return h;
    }

    // ---- deep operations ----

    public static String deepToString(Object[] a) {
        if (a == null) return "null";
        StringBuilder buf = new StringBuilder();
        deepToString(a, buf, new java.util.ArrayList<>());
        return buf.toString();
    }

    /** dejaVu: the arrays being printed (identity, as the JDK's HashSet of arrays). */
    private static void deepToString(Object[] a, StringBuilder buf, java.util.ArrayList<Object[]> dejaVu) {
        if (a == null) {
            buf.append("null");
            return;
        }
        int iMax = a.length - 1;
        if (iMax == -1) {
            buf.append("[]");
            return;
        }
        dejaVu.add(a);
        buf.append('[');
        for (int i = 0; ; i++) {
            Object element = a[i];
            if (element == null) {
                buf.append("null");
            } else if (element instanceof byte[]) buf.append(toString((byte[]) element));
            else if (element instanceof short[]) buf.append(toString((short[]) element));
            else if (element instanceof int[]) buf.append(toString((int[]) element));
            else if (element instanceof long[]) buf.append(toString((long[]) element));
            else if (element instanceof char[]) buf.append(toString((char[]) element));
            else if (element instanceof float[]) buf.append(toString((float[]) element));
            else if (element instanceof double[]) buf.append(toString((double[]) element));
            else if (element instanceof boolean[]) buf.append(toString((boolean[]) element));
            else if (element.getClass().isArray()) {
                boolean seen = false;
                for (Object[] d : dejaVu) if (d == element) seen = true;
                if (seen) buf.append("[...]");
                else deepToString((Object[]) element, buf, dejaVu);
            } else {
                buf.append(element.toString());
            }
            if (i == iMax) break;
            buf.append(", ");
        }
        buf.append(']');
        for (int k = dejaVu.size() - 1; k >= 0; k--) if (dejaVu.get(k) == a) { dejaVu.remove(k); break; }
    }

    public static boolean deepEquals(Object[] a1, Object[] a2) {
        if (a1 == a2) return true;
        if (a1 == null || a2 == null) return false;
        int length = a1.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) {
            Object e1 = a1[i];
            Object e2 = a2[i];
            if (e1 == e2) continue;
            if (e1 == null) return false;
            if (!deepEquals0(e1, e2)) return false;
        }
        return true;
    }

    static boolean deepEquals0(Object e1, Object e2) {
        if (e1 instanceof Object[] && e2 instanceof Object[]) return deepEquals((Object[]) e1, (Object[]) e2);
        else if (e1 instanceof byte[] && e2 instanceof byte[]) return equals((byte[]) e1, (byte[]) e2);
        else if (e1 instanceof short[] && e2 instanceof short[]) return equals((short[]) e1, (short[]) e2);
        else if (e1 instanceof int[] && e2 instanceof int[]) return equals((int[]) e1, (int[]) e2);
        else if (e1 instanceof long[] && e2 instanceof long[]) return equals((long[]) e1, (long[]) e2);
        else if (e1 instanceof char[] && e2 instanceof char[]) return equals((char[]) e1, (char[]) e2);
        else if (e1 instanceof float[] && e2 instanceof float[]) return equals((float[]) e1, (float[]) e2);
        else if (e1 instanceof double[] && e2 instanceof double[]) return equals((double[]) e1, (double[]) e2);
        else if (e1 instanceof boolean[] && e2 instanceof boolean[]) return equals((boolean[]) e1, (boolean[]) e2);
        else return e1.equals(e2);
    }

    public static int deepHashCode(Object[] a) {
        if (a == null) return 0;
        int result = 1;
        for (Object element : a) {
            int h;
            if (element == null) h = 0;
            else if (!element.getClass().isArray()) h = element.hashCode();
            else if (element instanceof Object[]) h = deepHashCode((Object[]) element);
            else if (element instanceof byte[]) h = hashCode((byte[]) element);
            else if (element instanceof int[]) h = hashCode((int[]) element);
            else if (element instanceof long[]) h = hashCode((long[]) element);
            else if (element instanceof char[]) h = hashCode((char[]) element);
            else if (element instanceof short[]) h = hashCode((short[]) element);
            else if (element instanceof boolean[]) h = hashCode((boolean[]) element);
            else if (element instanceof double[]) h = hashCode((double[]) element);
            else h = hashCode((float[]) element);
            result = 31 * result + h;
        }
        return result;
    }

    // ---- object arrays: equals / compare / mismatch ----

    public static boolean equals(Object[] a, Object[] a2) {
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) {
            if (!oeq(a[i], a2[i])) return false;
        }
        return true;
    }

    public static boolean equals(Object[] a, int aFromIndex, int aToIndex, Object[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        for (int i = 0; i < aLength; i++) {
            if (!oeq(a[aFromIndex++], b[bFromIndex++])) return false;
        }
        return true;
    }

    public static <T> boolean equals(T[] a, T[] a2, Comparator<? super T> cmp) {
        requireNonNull(cmp);
        if (a == a2) return true;
        if (a == null || a2 == null) return false;
        int length = a.length;
        if (a2.length != length) return false;
        for (int i = 0; i < length; i++) {
            if (cmp.compare(a[i], a2[i]) != 0) return false;
        }
        return true;
    }

    public static <T> boolean equals(T[] a, int aFromIndex, int aToIndex, T[] b, int bFromIndex, int bToIndex,
                                     Comparator<? super T> cmp) {
        requireNonNull(cmp);
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        if (aLength != bLength) return false;
        for (int i = 0; i < aLength; i++) {
            if (cmp.compare(a[aFromIndex++], b[bFromIndex++]) != 0) return false;
        }
        return true;
    }

    public static <T extends Comparable<? super T>> int compare(T[] a, T[] b) {
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int length = Math.min(a.length, b.length);
        for (int i = 0; i < length; i++) {
            T oa = a[i];
            T ob = b[i];
            if (oa != ob) {
                if (oa == null || ob == null) return oa == null ? -1 : 1;
                int v = natCmp(oa, ob, "oa");
                if (v != 0) return v;
            }
        }
        return a.length - b.length;
    }

    public static <T extends Comparable<? super T>> int compare(T[] a, int aFromIndex, int aToIndex,
                                                                T[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        for (int i = 0; i < length; i++) {
            T oa = a[aFromIndex++];
            T ob = b[bFromIndex++];
            if (oa != ob) {
                if (oa == null || ob == null) return oa == null ? -1 : 1;
                int v = natCmp(oa, ob, "oa");
                if (v != 0) return v;
            }
        }
        return aLength - bLength;
    }

    public static <T> int compare(T[] a, T[] b, Comparator<? super T> cmp) {
        requireNonNull(cmp);
        if (a == b) return 0;
        if (a == null || b == null) return a == null ? -1 : 1;
        int length = Math.min(a.length, b.length);
        for (int i = 0; i < length; i++) {
            T oa = a[i];
            T ob = b[i];
            if (oa != ob) {
                int v = cmp.compare(oa, ob);
                if (v != 0) return v;
            }
        }
        return a.length - b.length;
    }

    public static <T> int compare(T[] a, int aFromIndex, int aToIndex, T[] b, int bFromIndex, int bToIndex,
                                  Comparator<? super T> cmp) {
        requireNonNull(cmp);
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        for (int i = 0; i < length; i++) {
            T oa = a[aFromIndex++];
            T ob = b[bFromIndex++];
            if (oa != ob) {
                int v = cmp.compare(oa, ob);
                if (v != 0) return v;
            }
        }
        return aLength - bLength;
    }

    public static int mismatch(Object[] a, Object[] b) {
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        for (int i = 0; i < length; i++) {
            if (!oeq(a[i], b[i])) return i;
        }
        return a.length != b.length ? length : -1;
    }

    public static int mismatch(Object[] a, int aFromIndex, int aToIndex, Object[] b, int bFromIndex, int bToIndex) {
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        for (int i = 0; i < length; i++) {
            if (!oeq(a[aFromIndex++], b[bFromIndex++])) return i;
        }
        return aLength != bLength ? length : -1;
    }

    public static <T> int mismatch(T[] a, T[] b, Comparator<? super T> cmp) {
        requireNonNull(cmp);
        int length = Math.min(len(a, "a"), len(b, "b"));
        if (a == b) return -1;
        for (int i = 0; i < length; i++) {
            T oa = a[i];
            T ob = b[i];
            if (oa != ob) {
                int v = cmp.compare(oa, ob);
                if (v != 0) return i;
            }
        }
        return a.length != b.length ? length : -1;
    }

    public static <T> int mismatch(T[] a, int aFromIndex, int aToIndex, T[] b, int bFromIndex, int bToIndex,
                                   Comparator<? super T> cmp) {
        requireNonNull(cmp);
        rangeCheck(len(a, "a"), aFromIndex, aToIndex);
        rangeCheck(len(b, "b"), bFromIndex, bToIndex);
        int aLength = aToIndex - aFromIndex;
        int bLength = bToIndex - bFromIndex;
        int length = Math.min(aLength, bLength);
        for (int i = 0; i < length; i++) {
            T oa = a[aFromIndex++];
            T ob = b[bFromIndex++];
            if (oa != ob) {
                int v = cmp.compare(oa, ob);
                if (v != 0) return i;
            }
        }
        return aLength != bLength ? length : -1;
    }

    // ---- object arrays: fill / copyOf / copyOfRange ----

    public static void fill(Object[] a, Object val) {
        for (int i = 0, len = len(a, "a"); i < len; i++) a[i] = val;
    }

    public static void fill(Object[] a, int fromIndex, int toIndex, Object val) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        for (int i = fromIndex; i < toIndex; i++) a[i] = val;
    }

    private static NullPointerException getClassOfNull(String what) {
        return new NullPointerException("Cannot invoke \"Object.getClass()\" because \"" + what + "\" is null");
    }

    /** The new array of copyOf / copyOfRange: new Object[n] for Object[].class, otherwise
     *  Array.newInstance(newType.getComponentType(), n) cast to an object array. */
    private static Object[] newArrayOf(Class<?> newType, int n) {
        if ((Object) newType == (Object) Object[].class) return new Object[n];
        if (newType == null) throw ImmutableCollections.invokeOnNull("java.lang.Class.getComponentType()", "newType");
        Class<?> ct = newType.getComponentType();
        if (ct == null) throw new NullPointerException();   // Array.newInstance(null, n)
        Object arr = java.lang.reflect.Array.newInstance(ct, n);
        if (!(arr instanceof Object[])) {
            String x = arr.getClass().getName();
            throw new ClassCastException("class " + x + " cannot be cast to class [Ljava.lang.Object; (" + x
                + " and [Ljava.lang.Object; are in module java.base of loader 'bootstrap')");
        }
        return (Object[]) arr;
    }

    @SuppressWarnings("unchecked")
    public static <T> T[] copyOf(T[] original, int newLength) {
        if (original == null) throw getClassOfNull("original");
        return (T[]) copyOf(original, newLength, original.getClass());
    }

    @SuppressWarnings("unchecked")
    public static <T, U> T[] copyOf(U[] original, int newLength, Class<? extends T[]> newType) {
        Object[] copy = newArrayOf(newType, newLength);
        System.arraycopy(original, 0, copy, 0, Math.min(len(original, "original"), newLength));
        return (T[]) copy;
    }

    @SuppressWarnings("unchecked")
    public static <T> T[] copyOfRange(T[] original, int from, int to) {
        if (original == null) throw getClassOfNull("original");
        return copyOfRange(original, from, to, (Class<? extends T[]>) original.getClass());
    }

    @SuppressWarnings("unchecked")
    public static <T, U> T[] copyOfRange(U[] original, int from, int to, Class<? extends T[]> newType) {
        int newLength = to - from;
        if (newLength < 0) throw new IllegalArgumentException(from + " > " + to);
        Object[] copy = newArrayOf(newType, newLength);
        System.arraycopy(original, from, copy, 0, Math.min(len(original, "original") - from, newLength));
        return (T[]) copy;
    }

    // ---- object arrays: binarySearch ----

    public static int binarySearch(Object[] a, Object key) {
        return binarySearch0(a, 0, len(a, "a"), key);
    }

    public static int binarySearch(Object[] a, int fromIndex, int toIndex, Object key) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key);
    }

    private static int binarySearch0(Object[] a, int fromIndex, int toIndex, Object key) {
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            Object midVal = a[mid];
            checkComparable(midVal);
            int cmp = natCmp(midVal, key, "midVal");
            if (cmp < 0) low = mid + 1;
            else if (cmp > 0) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    /** The checkcast to Comparable of a JDK call site: HotSpot's message for java.base classes
     *  (and arrays of primitives); for other classes the cast itself (its message names the
     *  class loaders: the machine makes no claim about it). */
    @SuppressWarnings("rawtypes")
    static void checkComparable(Object o) {
        if (o == null || o instanceof Comparable) return;
        String n = o.getClass().getName();
        if (javaBaseName(n)) {
            throw new ClassCastException("class " + n + " cannot be cast to class java.lang.Comparable (" + n
                + " and java.lang.Comparable are in module java.base of loader 'bootstrap')");
        }
        Comparable c = (Comparable) o;
    }

    public static <T> int binarySearch(T[] a, T key, Comparator<? super T> c) {
        return binarySearch0(a, 0, len(a, "a"), key, c);
    }

    public static <T> int binarySearch(T[] a, int fromIndex, int toIndex, T key, Comparator<? super T> c) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        return binarySearch0(a, fromIndex, toIndex, key, c);
    }

    private static <T> int binarySearch0(T[] a, int fromIndex, int toIndex, T key, Comparator<? super T> c) {
        if (c == null) return binarySearch0(a, fromIndex, toIndex, key);
        int low = fromIndex;
        int high = toIndex - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            T midVal = a[mid];
            int cmp = c.compare(midVal, key);
            if (cmp < 0) low = mid + 1;
            else if (cmp > 0) high = mid - 1;
            else return mid;
        }
        return -(low + 1);
    }

    // ---- object arrays: sort / parallelSort (TimSort) ----

    public static void sort(Object[] a) {
        TimSorter.sort(a, 0, len(a, "a"), null, null);
    }

    public static void sort(Object[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        TimSorter.sort(a, fromIndex, toIndex, null, null);
    }

    public static <T> void sort(T[] a, Comparator<? super T> c) {
        if (c == null) {
            sort(a);
        } else {
            TimSorter.sort(a, 0, len(a, "a"), c, null);
        }
    }

    public static <T> void sort(T[] a, int fromIndex, int toIndex, Comparator<? super T> c) {
        if (c == null) {
            sort(a, fromIndex, toIndex);
        } else {
            rangeCheck(len(a, "a"), fromIndex, toIndex);
            TimSorter.sort(a, fromIndex, toIndex, c, null);
        }
    }

    /** Arrays.sort(a, lo, hi, c) for the model's ArrayList (a valid range). */
    @SuppressWarnings("rawtypes")
    static void sortRange(Object[] a, int lo, int hi, Comparator c) {
        TimSorter.sort(a, lo, hi, c, null);
    }

    private static final int MIN_ARRAY_SORT_GRAN = 1 << 13;

    public static <T extends Comparable<? super T>> void parallelSort(T[] a) {
        int n = len(a, "a");
        if (n > MIN_ARRAY_SORT_GRAN) throw ModelStuck.unsupported("Arrays.parallelSort of more than 8192 objects");
        TimSorter.sort(a, 0, n, null, "first");
    }

    public static <T extends Comparable<? super T>> void parallelSort(T[] a, int fromIndex, int toIndex) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        if (toIndex - fromIndex > MIN_ARRAY_SORT_GRAN) throw ModelStuck.unsupported("Arrays.parallelSort of more than 8192 objects");
        TimSorter.sort(a, fromIndex, toIndex, null, "first");
    }

    public static <T> void parallelSort(T[] a, Comparator<? super T> cmp) {
        int n = len(a, "a");
        if (n > MIN_ARRAY_SORT_GRAN) throw ModelStuck.unsupported("Arrays.parallelSort of more than 8192 objects");
        TimSorter.sort(a, 0, n, cmp, cmp == null ? "first" : null);
    }

    public static <T> void parallelSort(T[] a, int fromIndex, int toIndex, Comparator<? super T> cmp) {
        rangeCheck(len(a, "a"), fromIndex, toIndex);
        if (toIndex - fromIndex > MIN_ARRAY_SORT_GRAN) throw ModelStuck.unsupported("Arrays.parallelSort of more than 8192 objects");
        TimSorter.sort(a, fromIndex, toIndex, cmp, cmp == null ? "first" : null);
    }

    /**
     * JDK 21's TimSort / ComparableTimSort (Tim Peters' list sort as the JDK implements it: runs,
     * binary insertion sort below MIN_MERGE, the run stack and its collapse rules, galloping with
     * the adaptive minGallop, mergeLo/mergeHi and their contract checks). c == null: the natural
     * ordering, compareTo called at the JDK's sites (natSite != null: Arrays.NaturalOrder of
     * parallelSort, whose receiver is "first" at every site).
     */
    @SuppressWarnings({"rawtypes", "unchecked"})
    private static final class TimSorter {
        private static final int MIN_MERGE = 32;
        private static final int MIN_GALLOP = 7;
        private static final int INITIAL_TMP_STORAGE_LENGTH = 256;

        private final Object[] a;
        private final Comparator c;
        private final String natSite;
        private int minGallop = MIN_GALLOP;
        private Object[] tmp;
        private int tmpBase;
        private int tmpLen;
        private int stackSize = 0;
        private final int[] runBase;
        private final int[] runLen;

        private TimSorter(Object[] a, Comparator c, String natSite) {
            this.a = a;
            this.c = c;
            this.natSite = natSite;
            int len = a.length;
            int tlen = (len < 2 * INITIAL_TMP_STORAGE_LENGTH) ? len >>> 1 : INITIAL_TMP_STORAGE_LENGTH;
            tmp = new Object[tlen];
            tmpBase = 0;
            tmpLen = tlen;
            int stackLen = (len < 120 ? 5 : len < 1542 ? 10 : len < 119151 ? 24 : 49);
            runBase = new int[stackLen];
            runLen = new int[stackLen];
        }

        private static int cmp(Comparator c, String natSite, Object x, Object y, String site) {
            if (c != null) return c.compare(x, y);
            return natCmp(x, y, natSite != null ? natSite : site);
        }

        /** The checkcast to Comparable of ComparableTimSort / NaturalOrder. */
        private static void castCheck(Comparator c, Object x) {
            if (c == null) checkComparable(x);
        }

        static void sort(Object[] a, int lo, int hi, Comparator c, String natSite) {
            int nRemaining = hi - lo;
            if (nRemaining < 2) return;
            if (nRemaining < MIN_MERGE) {
                int initRunLen = countRunAndMakeAscending(a, lo, hi, c, natSite);
                binarySort(a, lo, hi, lo + initRunLen, c, natSite);
                return;
            }
            TimSorter ts = new TimSorter(a, c, natSite);
            int minRun = minRunLength(nRemaining);
            do {
                int runLen = countRunAndMakeAscending(a, lo, hi, c, natSite);
                if (runLen < minRun) {
                    int force = nRemaining <= minRun ? nRemaining : minRun;
                    binarySort(a, lo, lo + force, lo + runLen, c, natSite);
                    runLen = force;
                }
                ts.pushRun(lo, runLen);
                ts.mergeCollapse();
                lo += runLen;
                nRemaining -= runLen;
            } while (nRemaining != 0);
            ts.mergeForceCollapse();
        }

        private static void binarySort(Object[] a, int lo, int hi, int start, Comparator c, String natSite) {
            if (start == lo) start++;
            for (; start < hi; start++) {
                Object pivot = a[start];
                castCheck(c, pivot);
                int left = lo;
                int right = start;
                while (left < right) {
                    int mid = (left + right) >>> 1;
                    if (cmp(c, natSite, pivot, a[mid], "pivot") < 0) right = mid;
                    else left = mid + 1;
                }
                int n = start - left;
                switch (n) {
                    case 2:
                        a[left + 2] = a[left + 1];
                        a[left + 1] = a[left];
                        break;
                    case 1:
                        a[left + 1] = a[left];
                        break;
                    default:
                        System.arraycopy(a, left, a, left + 1, n);
                }
                a[left] = pivot;
            }
        }

        private static int countRunAndMakeAscending(Object[] a, int lo, int hi, Comparator c, String natSite) {
            int runHi = lo + 1;
            if (runHi == hi) return 1;
            Object x = a[runHi++];
            castCheck(c, x);
            if (cmp(c, natSite, x, a[lo], "a[runHi]") < 0) {
                while (runHi < hi && cmpAt(a, runHi, c, natSite) < 0) runHi++;
                reverseRange(a, lo, runHi);
            } else {
                while (runHi < hi && cmpAt(a, runHi, c, natSite) >= 0) runHi++;
            }
            return runHi - lo;
        }

        private static int cmpAt(Object[] a, int runHi, Comparator c, String natSite) {
            Object x = a[runHi];
            castCheck(c, x);
            return cmp(c, natSite, x, a[runHi - 1], "a[runHi]");
        }

        private static void reverseRange(Object[] a, int lo, int hi) {
            hi--;
            while (lo < hi) {
                Object t = a[lo];
                a[lo++] = a[hi];
                a[hi--] = t;
            }
        }

        private static int minRunLength(int n) {
            int r = 0;
            while (n >= MIN_MERGE) {
                r |= (n & 1);
                n >>= 1;
            }
            return n + r;
        }

        private void pushRun(int runBase, int runLen) {
            this.runBase[stackSize] = runBase;
            this.runLen[stackSize] = runLen;
            stackSize++;
        }

        private void mergeCollapse() {
            while (stackSize > 1) {
                int n = stackSize - 2;
                if (n > 0 && runLen[n - 1] <= runLen[n] + runLen[n + 1] || n > 1 && runLen[n - 2] <= runLen[n] + runLen[n - 1]) {
                    if (runLen[n - 1] < runLen[n + 1]) n--;
                } else if (n < 0 || runLen[n] > runLen[n + 1]) {
                    break;
                }
                mergeAt(n);
            }
        }

        private void mergeForceCollapse() {
            while (stackSize > 1) {
                int n = stackSize - 2;
                if (n > 0 && runLen[n - 1] < runLen[n + 1]) n--;
                mergeAt(n);
            }
        }

        private void mergeAt(int i) {
            int base1 = runBase[i];
            int len1 = runLen[i];
            int base2 = runBase[i + 1];
            int len2 = runLen[i + 1];
            runLen[i] = len1 + len2;
            if (i == stackSize - 3) {
                runBase[i + 1] = runBase[i + 2];
                runLen[i + 1] = runLen[i + 2];
            }
            stackSize--;
            Object k1 = a[base2];
            castCheck(c, k1);
            int k = gallopRight(k1, a, base1, len1, 0, c, natSite);
            base1 += k;
            len1 -= k;
            if (len1 == 0) return;
            Object k2 = a[base1 + len1 - 1];
            castCheck(c, k2);
            len2 = gallopLeft(k2, a, base2, len2, len2 - 1, c, natSite);
            if (len2 == 0) return;
            if (len1 <= len2) mergeLo(base1, len1, base2, len2);
            else mergeHi(base1, len1, base2, len2);
        }

        private static int gallopLeft(Object key, Object[] a, int base, int len, int hint, Comparator c, String ns) {
            int lastOfs = 0;
            int ofs = 1;
            if (cmp(c, ns, key, a[base + hint], "key") > 0) {
                int maxOfs = len - hint;
                while (ofs < maxOfs && cmp(c, ns, key, a[base + hint + ofs], "key") > 0) {
                    lastOfs = ofs;
                    ofs = (ofs << 1) + 1;
                    if (ofs <= 0) ofs = maxOfs;
                }
                if (ofs > maxOfs) ofs = maxOfs;
                lastOfs += hint;
                ofs += hint;
            } else {
                final int maxOfs = hint + 1;
                while (ofs < maxOfs && cmp(c, ns, key, a[base + hint - ofs], "key") <= 0) {
                    lastOfs = ofs;
                    ofs = (ofs << 1) + 1;
                    if (ofs <= 0) ofs = maxOfs;
                }
                if (ofs > maxOfs) ofs = maxOfs;
                int t = lastOfs;
                lastOfs = hint - ofs;
                ofs = hint - t;
            }
            lastOfs++;
            while (lastOfs < ofs) {
                int m = lastOfs + ((ofs - lastOfs) >>> 1);
                if (cmp(c, ns, key, a[base + m], "key") > 0) lastOfs = m + 1;
                else ofs = m;
            }
            return ofs;
        }

        private static int gallopRight(Object key, Object[] a, int base, int len, int hint, Comparator c, String ns) {
            int ofs = 1;
            int lastOfs = 0;
            if (cmp(c, ns, key, a[base + hint], "key") < 0) {
                int maxOfs = hint + 1;
                while (ofs < maxOfs && cmp(c, ns, key, a[base + hint - ofs], "key") < 0) {
                    lastOfs = ofs;
                    ofs = (ofs << 1) + 1;
                    if (ofs <= 0) ofs = maxOfs;
                }
                if (ofs > maxOfs) ofs = maxOfs;
                int t = lastOfs;
                lastOfs = hint - ofs;
                ofs = hint - t;
            } else {
                int maxOfs = len - hint;
                while (ofs < maxOfs && cmp(c, ns, key, a[base + hint + ofs], "key") >= 0) {
                    lastOfs = ofs;
                    ofs = (ofs << 1) + 1;
                    if (ofs <= 0) ofs = maxOfs;
                }
                if (ofs > maxOfs) ofs = maxOfs;
                lastOfs += hint;
                ofs += hint;
            }
            lastOfs++;
            while (lastOfs < ofs) {
                int m = lastOfs + ((ofs - lastOfs) >>> 1);
                if (cmp(c, ns, key, a[base + m], "key") < 0) ofs = m;
                else lastOfs = m + 1;
            }
            return ofs;
        }

        private void mergeLo(int base1, int len1, int base2, int len2) {
            Object[] a = this.a;
            Object[] tmp = ensureCapacity(len1);
            int cursor1 = tmpBase;
            int cursor2 = base2;
            int dest = base1;
            System.arraycopy(a, base1, tmp, cursor1, len1);
            a[dest++] = a[cursor2++];
            if (--len2 == 0) {
                System.arraycopy(tmp, cursor1, a, dest, len1);
                return;
            }
            if (len1 == 1) {
                System.arraycopy(a, cursor2, a, dest, len2);
                a[dest + len2] = tmp[cursor1];
                return;
            }
            Comparator c = this.c;
            String ns = this.natSite;
            int minGallop = this.minGallop;
            outer:
            while (true) {
                int count1 = 0;
                int count2 = 0;
                do {
                    Object x = a[cursor2];
                    castCheck(c, x);
                    if (cmp(c, ns, x, tmp[cursor1], "a[cursor2]") < 0) {
                        a[dest++] = a[cursor2++];
                        count2++;
                        count1 = 0;
                        if (--len2 == 0) break outer;
                    } else {
                        a[dest++] = tmp[cursor1++];
                        count1++;
                        count2 = 0;
                        if (--len1 == 1) break outer;
                    }
                } while ((count1 | count2) < minGallop);
                do {
                    Object k1 = a[cursor2];
                    castCheck(c, k1);
                    count1 = gallopRight(k1, tmp, cursor1, len1, 0, c, ns);
                    if (count1 != 0) {
                        System.arraycopy(tmp, cursor1, a, dest, count1);
                        dest += count1;
                        cursor1 += count1;
                        len1 -= count1;
                        if (len1 <= 1) break outer;
                    }
                    a[dest++] = a[cursor2++];
                    if (--len2 == 0) break outer;
                    Object k2 = tmp[cursor1];
                    castCheck(c, k2);
                    count2 = gallopLeft(k2, a, cursor2, len2, 0, c, ns);
                    if (count2 != 0) {
                        System.arraycopy(a, cursor2, a, dest, count2);
                        dest += count2;
                        cursor2 += count2;
                        len2 -= count2;
                        if (len2 == 0) break outer;
                    }
                    a[dest++] = tmp[cursor1++];
                    if (--len1 == 1) break outer;
                    minGallop--;
                } while (count1 >= MIN_GALLOP | count2 >= MIN_GALLOP);
                if (minGallop < 0) minGallop = 0;
                minGallop += 2;
            }
            this.minGallop = minGallop < 1 ? 1 : minGallop;
            if (len1 == 1) {
                System.arraycopy(a, cursor2, a, dest, len2);
                a[dest + len2] = tmp[cursor1];
            } else if (len1 == 0) {
                throw new IllegalArgumentException("Comparison method violates its general contract!");
            } else {
                System.arraycopy(tmp, cursor1, a, dest, len1);
            }
        }

        private void mergeHi(int base1, int len1, int base2, int len2) {
            Object[] a = this.a;
            Object[] tmp = ensureCapacity(len2);
            int tmpBase = this.tmpBase;
            System.arraycopy(a, base2, tmp, tmpBase, len2);
            int cursor1 = base1 + len1 - 1;
            int cursor2 = tmpBase + len2 - 1;
            int dest = base2 + len2 - 1;
            a[dest--] = a[cursor1--];
            if (--len1 == 0) {
                System.arraycopy(tmp, tmpBase, a, dest - (len2 - 1), len2);
                return;
            }
            if (len2 == 1) {
                dest -= len1;
                cursor1 -= len1;
                System.arraycopy(a, cursor1 + 1, a, dest + 1, len1);
                a[dest] = tmp[cursor2];
                return;
            }
            Comparator c = this.c;
            String ns = this.natSite;
            int minGallop = this.minGallop;
            outer:
            while (true) {
                int count1 = 0;
                int count2 = 0;
                do {
                    Object x = tmp[cursor2];
                    castCheck(c, x);
                    if (cmp(c, ns, x, a[cursor1], "tmp[cursor2]") < 0) {
                        a[dest--] = a[cursor1--];
                        count1++;
                        count2 = 0;
                        if (--len1 == 0) break outer;
                    } else {
                        a[dest--] = tmp[cursor2--];
                        count2++;
                        count1 = 0;
                        if (--len2 == 1) break outer;
                    }
                } while ((count1 | count2) < minGallop);
                do {
                    Object k1 = tmp[cursor2];
                    castCheck(c, k1);
                    count1 = len1 - gallopRight(k1, a, base1, len1, len1 - 1, c, ns);
                    if (count1 != 0) {
                        dest -= count1;
                        cursor1 -= count1;
                        len1 -= count1;
                        System.arraycopy(a, cursor1 + 1, a, dest + 1, count1);
                        if (len1 == 0) break outer;
                    }
                    a[dest--] = tmp[cursor2--];
                    if (--len2 == 1) break outer;
                    Object k2 = a[cursor1];
                    castCheck(c, k2);
                    count2 = len2 - gallopLeft(k2, tmp, tmpBase, len2, len2 - 1, c, ns);
                    if (count2 != 0) {
                        dest -= count2;
                        cursor2 -= count2;
                        len2 -= count2;
                        System.arraycopy(tmp, cursor2 + 1, a, dest + 1, count2);
                        if (len2 <= 1) break outer;
                    }
                    a[dest--] = a[cursor1--];
                    if (--len1 == 0) break outer;
                    minGallop--;
                } while (count1 >= MIN_GALLOP | count2 >= MIN_GALLOP);
                if (minGallop < 0) minGallop = 0;
                minGallop += 2;
            }
            this.minGallop = minGallop < 1 ? 1 : minGallop;
            if (len2 == 1) {
                dest -= len1;
                cursor1 -= len1;
                System.arraycopy(a, cursor1 + 1, a, dest + 1, len1);
                a[dest] = tmp[cursor2];
            } else if (len2 == 0) {
                throw new IllegalArgumentException("Comparison method violates its general contract!");
            } else {
                System.arraycopy(tmp, tmpBase, a, dest - (len2 - 1), len2);
            }
        }

        private Object[] ensureCapacity(int minCapacity) {
            if (tmpLen < minCapacity) {
                int newSize = -1 >>> Integer.numberOfLeadingZeros(minCapacity);
                newSize++;
                if (newSize < 0) newSize = minCapacity;
                else newSize = Math.min(newSize, a.length >>> 1);
                tmp = new Object[newSize];
                tmpLen = newSize;
                tmpBase = 0;
            }
            return tmp;
        }
    }

    // ---- parallelPrefix (sequential where the JDK's task does not split) ----

    private static final int MIN_PARTITION = 16;

    private static void prefixBound(int n) {
        if (n > MIN_PARTITION) throw ModelStuck.unsupported("Arrays.parallelPrefix of more than 16 elements");
    }

    public static <T> void parallelPrefix(T[] array, BinaryOperator<T> op) {
        requireNonNull(op);
        int n = len(array, "array");
        if (n > 0) {
            prefixBound(n);
            T sum = array[0];
            for (int i = 1; i < n; ++i) array[i] = sum = op.apply(sum, array[i]);
        }
    }

    public static <T> void parallelPrefix(T[] array, int fromIndex, int toIndex, BinaryOperator<T> op) {
        requireNonNull(op);
        rangeCheck(len(array, "array"), fromIndex, toIndex);
        if (fromIndex < toIndex) {
            prefixBound(toIndex - fromIndex);
            T sum = array[fromIndex];
            for (int i = fromIndex + 1; i < toIndex; ++i) array[i] = sum = op.apply(sum, array[i]);
        }
    }

    public static void parallelPrefix(long[] array, LongBinaryOperator op) {
        requireNonNull(op);
        int n = len(array, "array");
        if (n > 0) {
            prefixBound(n);
            long sum = array[0];
            for (int i = 1; i < n; ++i) array[i] = sum = op.applyAsLong(sum, array[i]);
        }
    }

    public static void parallelPrefix(long[] array, int fromIndex, int toIndex, LongBinaryOperator op) {
        requireNonNull(op);
        rangeCheck(len(array, "array"), fromIndex, toIndex);
        if (fromIndex < toIndex) {
            prefixBound(toIndex - fromIndex);
            long sum = array[fromIndex];
            for (int i = fromIndex + 1; i < toIndex; ++i) array[i] = sum = op.applyAsLong(sum, array[i]);
        }
    }

    public static void parallelPrefix(double[] array, DoubleBinaryOperator op) {
        requireNonNull(op);
        int n = len(array, "array");
        if (n > 0) {
            prefixBound(n);
            double sum = array[0];
            for (int i = 1; i < n; ++i) array[i] = sum = op.applyAsDouble(sum, array[i]);
        }
    }

    public static void parallelPrefix(double[] array, int fromIndex, int toIndex, DoubleBinaryOperator op) {
        requireNonNull(op);
        rangeCheck(len(array, "array"), fromIndex, toIndex);
        if (fromIndex < toIndex) {
            prefixBound(toIndex - fromIndex);
            double sum = array[fromIndex];
            for (int i = fromIndex + 1; i < toIndex; ++i) array[i] = sum = op.applyAsDouble(sum, array[i]);
        }
    }

    public static void parallelPrefix(int[] array, IntBinaryOperator op) {
        requireNonNull(op);
        int n = len(array, "array");
        if (n > 0) {
            prefixBound(n);
            int sum = array[0];
            for (int i = 1; i < n; ++i) array[i] = sum = op.applyAsInt(sum, array[i]);
        }
    }

    public static void parallelPrefix(int[] array, int fromIndex, int toIndex, IntBinaryOperator op) {
        requireNonNull(op);
        rangeCheck(len(array, "array"), fromIndex, toIndex);
        if (fromIndex < toIndex) {
            prefixBound(toIndex - fromIndex);
            int sum = array[fromIndex];
            for (int i = fromIndex + 1; i < toIndex; ++i) array[i] = sum = op.applyAsInt(sum, array[i]);
        }
    }

    // ---- setAll / parallelSetAll ----

    public static <T> void setAll(T[] array, IntFunction<? extends T> generator) {
        requireNonNull(generator);
        for (int i = 0; i < len(array, "array"); i++) array[i] = generator.apply(i);
    }

    public static void setAll(int[] array, IntUnaryOperator generator) {
        requireNonNull(generator);
        for (int i = 0; i < len(array, "array"); i++) array[i] = generator.applyAsInt(i);
    }

    public static void setAll(long[] array, IntToLongFunction generator) {
        requireNonNull(generator);
        for (int i = 0; i < len(array, "array"); i++) array[i] = generator.applyAsLong(i);
    }

    public static void setAll(double[] array, IntToDoubleFunction generator) {
        requireNonNull(generator);
        for (int i = 0; i < len(array, "array"); i++) array[i] = generator.applyAsDouble(i);
    }

    private static void setAllBound(int n) {
        if (n > 1) throw ModelStuck.unsupported("Arrays.parallelSetAll of more than one element (order of the generator calls)");
    }

    public static <T> void parallelSetAll(T[] array, IntFunction<? extends T> generator) {
        requireNonNull(generator);
        int n = len(array, "array");
        setAllBound(n);
        for (int i = 0; i < n; i++) array[i] = generator.apply(i);
    }

    public static void parallelSetAll(int[] array, IntUnaryOperator generator) {
        requireNonNull(generator);
        int n = len(array, "array");
        setAllBound(n);
        for (int i = 0; i < n; i++) array[i] = generator.applyAsInt(i);
    }

    public static void parallelSetAll(long[] array, IntToLongFunction generator) {
        requireNonNull(generator);
        int n = len(array, "array");
        setAllBound(n);
        for (int i = 0; i < n; i++) array[i] = generator.applyAsLong(i);
    }

    public static void parallelSetAll(double[] array, IntToDoubleFunction generator) {
        requireNonNull(generator);
        int n = len(array, "array");
        setAllBound(n);
        for (int i = 0; i < n; i++) array[i] = generator.applyAsDouble(i);
    }

    // ---- spliterator: no Spliterator model ----

    public static <T> Spliterator<T> spliterator(T[] array) {
        throw ModelStuck.unsupported("Arrays.spliterator");
    }

    public static <T> Spliterator<T> spliterator(T[] array, int startInclusive, int endExclusive) {
        throw ModelStuck.unsupported("Arrays.spliterator");
    }

    public static Spliterator.OfInt spliterator(int[] array) {
        throw ModelStuck.unsupported("Arrays.spliterator");
    }

    public static Spliterator.OfInt spliterator(int[] array, int startInclusive, int endExclusive) {
        throw ModelStuck.unsupported("Arrays.spliterator");
    }

    public static Spliterator.OfLong spliterator(long[] array) {
        throw ModelStuck.unsupported("Arrays.spliterator");
    }

    public static Spliterator.OfLong spliterator(long[] array, int startInclusive, int endExclusive) {
        throw ModelStuck.unsupported("Arrays.spliterator");
    }

    public static Spliterator.OfDouble spliterator(double[] array) {
        throw ModelStuck.unsupported("Arrays.spliterator");
    }

    public static Spliterator.OfDouble spliterator(double[] array, int startInclusive, int endExclusive) {
        throw ModelStuck.unsupported("Arrays.spliterator");
    }

    // ---- stream (java.util.stream model) ----

    public static <T> Stream<T> stream(T[] array) {
        return stream(array, 0, len(array, "array"));
    }

    public static <T> Stream<T> stream(T[] array, int startInclusive, int endExclusive) {
        return ModelStreams.ofArray(array, startInclusive, endExclusive);
    }

    public static IntStream stream(int[] array) {
        return stream(array, 0, len(array, "array"));
    }

    public static IntStream stream(int[] array, int startInclusive, int endExclusive) {
        return ModelStreams.ofIntArray(array, startInclusive, endExclusive);
    }

    public static LongStream stream(long[] array) {
        return stream(array, 0, len(array, "array"));
    }

    public static LongStream stream(long[] array, int startInclusive, int endExclusive) {
        return ModelStreams.ofLongArray(array, startInclusive, endExclusive);
    }

    public static DoubleStream stream(double[] array) {
        return stream(array, 0, len(array, "array"));
    }

    public static DoubleStream stream(double[] array, int startInclusive, int endExclusive) {
        return ModelStreams.ofDoubleArray(array, startInclusive, endExclusive);
    }

    /** The list view (java.util.Arrays$ArrayList). */
    private static class ArrayList<E> extends AbstractList<E> implements RandomAccess, java.io.Serializable {
        private final E[] a;

        ArrayList(E[] array) {
            if (array == null) throw new NullPointerException();
            a = array;
        }

        public int size() {
            return a.length;
        }

        public Object[] toArray() {
            Object[] r = new Object[a.length];
            System.arraycopy(a, 0, r, 0, a.length);
            return r;
        }

        @SuppressWarnings("unchecked")
        public <T> T[] toArray(T[] r) {
            int size = size();
            if (r == null) throw ImmutableCollections.lengthOfNull("a");
            if (r.length < size) {
                Object[] n = AbstractCollection.newArrayLike(r, size);
                System.arraycopy(this.a, 0, n, 0, size);
                return (T[]) n;
            }
            System.arraycopy(this.a, 0, r, 0, size);
            if (r.length > size) r[size] = null;
            return r;
        }

        public E get(int index) {
            return a[index];
        }

        public E set(int index, E element) {
            E old = a[index];
            a[index] = element;
            return old;
        }

        public int indexOf(Object o) {
            E[] arr = a;
            if (o == null) {
                for (int i = 0; i < arr.length; i++) {
                    if (arr[i] == null) return i;
                }
            } else {
                for (int i = 0; i < arr.length; i++) {
                    if (o.equals(arr[i])) return i;
                }
            }
            return -1;
        }

        public boolean contains(Object o) {
            return indexOf(o) >= 0;
        }

        public void forEach(Consumer<? super E> action) {
            if (action == null) throw new NullPointerException();
            for (E e : a) action.accept(e);
        }

        public void replaceAll(UnaryOperator<E> operator) {
            if (operator == null) throw new NullPointerException();
            E[] arr = this.a;
            for (int i = 0; i < arr.length; i++) arr[i] = operator.apply(arr[i]);
        }

        /** Arrays.sort(a, c): sorts the backing array in place (TimSort). */
        public void sort(Comparator<? super E> c) {
            sortRange(a, 0, a.length, c);
        }

        public Iterator<E> iterator() {
            return new ArrayItr<>(a);
        }
    }

    private static class ArrayItr<E> implements Iterator<E> {
        private int cursor;
        private final E[] a;

        ArrayItr(E[] a) {
            this.a = a;
        }

        public boolean hasNext() {
            return cursor < a.length;
        }

        public E next() {
            int i = cursor;
            if (i >= a.length) throw new NoSuchElementException();
            cursor = i + 1;
            return a[i];
        }
    }
}

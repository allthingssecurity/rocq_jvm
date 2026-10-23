package org.rocqjvm.jdkmodel;

import java.util.*;

/** Shared helpers of the java.util model tests: a small LCG, folding of observations into an
 *  int, exception codes (exact class), and key/value constructors. */
final class T {
    private T() {
    }

    int s;
    int acc = 17;

    T(int seed) {
        s = seed;
    }

    /** next pseudo-random value in [0, n) (n > 0). */
    int r(int n) {
        s = s * 1103515245 + 12345;
        int x = (s >>> 8) & 0x7fffff;
        return x % n;
    }

    boolean chance(int pct) {
        return r(100) < pct;
    }

    void f(int x) {
        acc = acc * 31 + x;
    }

    void f(boolean b) {
        f(b ? 1 : 2);
    }

    void fo(Object o) {
        f(code(o));
    }

    void fe(Throwable t) {
        f(1000 + exc(t));
    }

    /** Observable identity of a key/value: ids of K, Integer/Long values, String hash codes. */
    static int code(Object o) {
        if (o == null) return 7777;
        if (o instanceof K) return 100000 + ((K) o).id;
        if (o instanceof Integer) return (Integer) o;
        if (o instanceof Long) {
            long v = (Long) o;
            return (int) ((v * 0x9E3779B97F4A7C15L) >>> 32) + 3;
        }
        if (o instanceof String) return ((String) o).hashCode() + 11 * ((String) o).length();
        if (o instanceof Map.Entry) {
            Map.Entry<?, ?> e = (Map.Entry<?, ?>) o;
            return 31 * code(e.getKey()) + code(e.getValue()) + 5;
        }
        return 999;
    }

    /** Exact class of an exception, as a number. */
    static int exc(Throwable t) {
        Class<?> c = t.getClass();
        if (c == ConcurrentModificationException.class) return 1;
        if (c == NoSuchElementException.class) return 2;
        if (c == IllegalStateException.class) return 3;
        if (c == UnsupportedOperationException.class) return 4;
        if (c == IndexOutOfBoundsException.class) return 5;
        if (c == ArrayIndexOutOfBoundsException.class) return 6;
        if (c == IllegalArgumentException.class) return 7;
        if (c == NullPointerException.class) return 8;
        if (c == ClassCastException.class) return 9;
        if (c == ArrayStoreException.class) return 10;
        if (c == StringIndexOutOfBoundsException.class) return 11;
        return 99;
    }

    // ---- keys ----

    /** Hash functions for K keys: distinct hashes with many bin collisions, plus small
     *  equal-hash groups (at most 7 keys per hash value, so no tree bin ever has keys with
     *  equal hashes that do not compare: that case is the documented STUCK one). */
    static int hashFor(int mode, int id) {
        switch (mode) {
            case 0: return id;
            case 1: return id << 4;            // same low bits: long chains in small tables
            case 2: return id << 6;            // one bin until the table has > 64 slots
            case 3: return id << 16;           // only the spreading h ^ (h >>> 16) separates them
            case 4: return id * 0x9E3779B9;
            case 5: return -id;
            case 6: return id / 7;             // equal-hash groups of 7
            default: return (id << 10) | (id & 3);
        }
    }

    K key(int mode, int range) {
        int id = r(range);
        return new K(id, hashFor(mode, id));
    }

    /** Integer keys: small, multiples of 16/64, values that differ only above bit 16. */
    Integer intKey(int mode, int range) {
        int id = r(range);
        switch (mode) {
            case 0: return id;
            case 1: return id * 16;
            case 2: return id * 64;
            case 3: return id << 16;
            default: return -id;
        }
    }

    /** Long keys (a << 32 | b): hash code a ^ b, so many keys share a hash code; Long is
     *  Comparable, so tree bins order them by compareTo. */
    Long longKey(int range) {
        int r = 3 + range / 8;
        long a = r(r), b = r(r);
        return (a << 32) | b;
    }

    /** 2^6 = 64 distinct Strings of length 12 with one hash code (Aa/BB blocks): tree bins
     *  ordered by String.compareTo. */
    String strKeyLong(int range) {
        int n = r(range);
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < 6; i++) sb.append((n >> i & 1) == 0 ? "Aa" : "BB");
        return sb.toString();
    }

    /** Strings from a small alphabet; "Aa" and "BB" have equal hash codes, so concatenations
     *  of them collide (tree bins ordered by compareTo). */
    String strKey(int range) {
        int n = r(range);
        StringBuilder sb = new StringBuilder();
        int len = 1 + (n % 5);
        for (int i = 0; i < len; i++) {
            sb.append((n >> i & 1) == 0 ? "Aa" : "BB");
        }
        if (n % 3 == 0) sb.append((char) ('a' + (n % 7)));
        return sb.toString();
    }
}

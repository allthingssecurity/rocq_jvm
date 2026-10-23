package org.rocqjvm.corpus10;

import java.io.Serializable;
import java.lang.constant.Constable;
import java.lang.constant.ConstantDesc;

/** Corpus 10: the interfaces of the JDK classes the machine does not load (boxes, Number, String,
 *  StringBuilder, Enum): instanceof / checkcast / aastore into Serializable[] / Comparable[] / ... */
public class Boxes {
    enum E { A, B }
    @SafeVarargs static <T> T[] arr(T... xs) { return xs; }
    static Object pick(int x) {
        switch ((x & 0x7fffffff) % 9) {
            case 0: return x;
            case 1: return (long) x;
            case 2: return (short) x;
            case 3: return (byte) x;
            case 4: return (char) x;
            case 5: return (x & 16) != 0;
            case 6: return "s" + x;
            case 7: return new StringBuilder("b");
            default: return E.values()[x & 1];
        }
    }
    static int instances(int x) {
        Object o = pick(x);
        return (o instanceof Serializable ? 1 : 0) + (o instanceof Comparable ? 2 : 0) + (o instanceof Constable ? 4 : 0)
             + (o instanceof ConstantDesc ? 8 : 0) + (o instanceof CharSequence ? 16 : 0) + (o instanceof Number ? 32 : 0)
             + (o instanceof Appendable ? 64 : 0) + (o instanceof Enum ? 128 : 0) + (o instanceof Runnable ? 256 : 0);
    }
    static int stores(int x) {
        Object o = pick(x);
        int r = 0;
        Object[][] arrays = { new Serializable[1], new Comparable[1], new Constable[1], new ConstantDesc[1],
                              new CharSequence[1], new Number[1], new Integer[1], new String[1] };
        for (int i = 0; i < arrays.length; i++) {
            try { arrays[i][0] = o; r |= 1 << i; } catch (ArrayStoreException e) { r |= 1 << (i + 10); }
        }
        return r;
    }
    static int casts(int x) {
        Object o = pick(x);
        int r = 0;
        try { Serializable s = (Serializable) o; r |= 1; } catch (ClassCastException e) { r |= 2; }
        try { Comparable<?> c = (Comparable<?>) o; r |= 4; } catch (ClassCastException e) { r |= 8; }
        try { ConstantDesc d = (ConstantDesc) o; r |= 16; } catch (ClassCastException e) { r |= 32; }
        try { Number n = (Number) o; r |= 64; } catch (ClassCastException e) { r |= 128; }
        return r;
    }
    static int mixedVarargs(int x) {
        Object[] a = arr(x, "x" + x);      // the array type is the erasure of the lub of Integer and String
        Object[] b = arr((long) x, (short) x);
        int r = a.length + b.length * 10;
        try { a[0] = (x & 1) != 0 ? (Object) Boolean.TRUE : (Object) (char) x; r += 100; } catch (ArrayStoreException e) { r += 1000; }
        try { b[1] = (x & 2) != 0 ? (Object) "s" : (Object) x; r += 10000; } catch (ArrayStoreException e) { r += 100000; }
        return r;
    }
}

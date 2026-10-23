package org.apache.camel.util;

/**
 * Test driver for CaseInsensitiveMap (our code, not Camel's): runs a pseudo-random sequence of
 * put/remove/get on 4 keys, each in two case variants, against a reference map (an array indexed by
 * the key's class), and checks every result and the size. Returns the map if everything matched,
 * otherwise null. The slot capacity (length of the private keys array) is read from the heap by the
 * Rocq theorems, as main has no accessor for it.
 */
public class CimScenario {
    static final String[] KEYS = { "a", "A", "Bb", "bB", "Content-Type", "CONTENT-type", "x-é", "X-É" };

    public static CaseInsensitiveMap run(int seed, int nops) {
        CaseInsensitiveMap m = new CaseInsensitiveMap();
        Object[] ref = new Object[4];
        int count = 0;
        int r = seed;
        for (int i = 0; i < nops; i++) {
            r = r * 1103515245 + 12345;
            int op = (r >>> 16) % 3;
            int k = (r >>> 20) & 7;
            int c = k >> 1;
            String key = KEYS[k];
            Object v = Integer.valueOf(i);
            if (op == 0) {
                Object old = m.put(key, v);
                if (old != ref[c]) return null;
                if (ref[c] == null) count++;
                ref[c] = v;
            } else if (op == 1) {
                Object old = m.remove(key);
                if (old != ref[c]) return null;
                if (ref[c] != null) count--;
                ref[c] = null;
            } else {
                if (m.get(key) != ref[c]) return null;
                if (m.containsKey(key) != (ref[c] != null)) return null;
            }
            if (m.size() != count) return null;
        }
        return m;
    }

    /** put and remove the same key n times. */
    public static CaseInsensitiveMap churn(int n) {
        CaseInsensitiveMap m = new CaseInsensitiveMap();
        for (int i = 0; i < n; i++) {
            m.put("h", Integer.valueOf(i));
            m.remove("H");
        }
        return m;
    }
}

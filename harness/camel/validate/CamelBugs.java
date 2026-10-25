import java.lang.reflect.Field;
import java.time.Duration;
import java.util.*;
import org.apache.camel.util.CaseInsensitiveMap;
import org.apache.camel.util.FilterIterator;
import org.apache.camel.util.TimeUtils;

/** Plain-Java reproductions of the camel-util findings. Run with camel-util (and slf4j-api) on the classpath:
 *    javac -cp camel-util.jar:slf4j-api.jar CamelBugs.java && java -cp camel-util.jar:slf4j-api.jar:. CamelBugs
 *  Each line prints what Camel does and what the contract says. */
public class CamelBugs {
    public static void main(String[] a) throws Exception {
        // 1. FilterIterator.remove() after hasNext() removes the wrong element
        List<String> l = new ArrayList<>(List.of("a", "b", "c"));
        Iterator<String> it = new FilterIterator<>(l.iterator());
        it.next(); it.hasNext(); it.remove();
        System.out.println("FilterIterator  next();hasNext();remove() leaves " + l + "   expected [b, c]");
        List<String> l2 = new ArrayList<>(List.of("a", "b", "c"));
        Iterator<String> it2 = new FilterIterator<>(l2.iterator());
        it2.hasNext();
        String r;
        try { it2.remove(); r = "accepted, leaves " + l2; } catch (IllegalStateException e) { r = "IllegalStateException"; }
        System.out.println("FilterIterator  hasNext();remove() before next(): " + r + "   expected IllegalStateException");

        // 2. TimeUtils.isPositive on a negative duration with a fractional part
        for (long ns : new long[] {-1, -999_999_999, -1_000_000_001, 0, 1}) {
            Duration d = Duration.ofNanos(ns);
            System.out.println("TimeUtils.isPositive(ofNanos(" + ns + ")) = " + TimeUtils.isPositive(d) + "   expected " + d.isPositive());
        }

        // 3. CaseInsensitiveMap: supplementary-plane case pair (U+10400 / U+10428)
        String up = new String(Character.toChars(0x10400)), lo = new String(Character.toChars(0x10428));
        CaseInsensitiveMap m = new CaseInsensitiveMap();
        m.put(up, "v");
        System.out.println("CIM  equalsIgnoreCase=" + up.equalsIgnoreCase(lo) + " get(lower)=" + m.get(lo)
            + " containsKey(lower)=" + m.containsKey(lo) + "   expected v / true");
        m.put(lo, "w");
        System.out.println("CIM  size after put(upper), put(lower) = " + m.size() + "   expected 1");

        // 4. CaseInsensitiveMap: put(k); remove(K) churn grows the slot arrays (main before the removed-slots fix)
        for (int n : new int[] {50, 1000}) {
            CaseInsensitiveMap c = new CaseInsensitiveMap();
            for (int i = 0; i < n; i++) { c.put("h", "x"); c.remove("H"); }
            Field f = CaseInsensitiveMap.class.getDeclaredField("keys");
            f.setAccessible(true);
            System.out.println("CIM  " + n + " rounds of put(\"h\");remove(\"H\"): size=" + c.size()
                + " keys.length=" + ((Object[]) f.get(c)).length + "   expected bounded (fix: 13)");
        }
    }
}

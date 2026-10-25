import java.lang.reflect.Field;
import java.lang.reflect.Method;
import java.util.Map;

/** Independent HotSpot check of the recorded Camel class; no model classes. */
public class AsciiAudit {
    @SuppressWarnings("unchecked")
    public static void main(String[] args) throws Exception {
        Class<?> cls = Class.forName("org.apache.camel.util.CaseInsensitiveMap");
        Method hash = cls.getDeclaredMethod("caseInsensitiveHash", String.class);
        hash.setAccessible(true);
        int equivalent = 0;
        for (int a = 0; a < 128; a++) {
            for (int b = 0; b < 128; b++) {
                String x = Character.toString((char) a), y = Character.toString((char) b);
                if (x.equalsIgnoreCase(y)) {
                    equivalent++;
                    if (!hash.invoke(null, x).equals(hash.invoke(null, y))) {
                        throw new AssertionError("ASCII hash mismatch: " + a + "," + b);
                    }
                    Map<String, Object> map = (Map<String, Object>) cls.getConstructor().newInstance();
                    map.put(x, "value");
                    if (!"value".equals(map.get(y))) throw new AssertionError("ASCII lookup mismatch");
                    if (!"value".equals(map.remove(y)) || !map.isEmpty()) {
                        throw new AssertionError("ASCII removal mismatch");
                    }
                }
            }
        }
        System.out.println("ASCII pairs checked=16384 equivalent=" + equivalent + " failures=0");
        Map<String, Object> map = (Map<String, Object>) cls.getConstructor().newInstance();
        String upper = "\uD801\uDC00", lower = "\uD801\uDC28";
        map.put(upper, "value");
        Object lookup = map.get(lower);
        map.put(lower, "second");
        System.out.println("Deseret equalsIgnoreCase=" + upper.equalsIgnoreCase(lower)
                + " hashes=" + hash.invoke(null, upper) + "," + hash.invoke(null, lower)
                + " alternateLookup=" + lookup + " sizeAfterBoth=" + map.size());
        Field keys = cls.getDeclaredField("keys");
        keys.setAccessible(true);
        for (int rounds : new int[] {50, 1000}) {
            map = (Map<String, Object>) cls.getConstructor().newInstance();
            for (int i = 0; i < rounds; i++) {
                map.put("h", i);
                if (!Integer.valueOf(i).equals(map.remove("H"))) throw new AssertionError("churn mismatch");
            }
            System.out.println("churn rounds=" + rounds + " slots=" + ((Object[]) keys.get(map)).length);
        }
    }
}

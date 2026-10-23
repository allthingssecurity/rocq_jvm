import java.lang.reflect.*;
import java.io.*;
/** HotSpot side of the CaseInsensitiveMap differential test: same output format as machine_main for
 *  a returned object (class, then the length of each array-valued instance field). */
public class CimProbe {
  public static void main(String[] a) throws Exception {
    Class<?> sc = Class.forName("org.apache.camel.util.CimScenario");
    Method m = a[0].equals("churn") ? sc.getMethod("churn", int.class) : sc.getMethod("run", int.class, int.class);
    BufferedReader in = new BufferedReader(new FileReader(a[1]));
    for (String line; (line = in.readLine()) != null; ) {
      String[] t = line.trim().split(" +");
      Object r = t.length == 1 ? m.invoke(null, Integer.parseInt(t[0])) : m.invoke(null, Integer.parseInt(t[0]), Integer.parseInt(t[1]));
      if (r == null) { System.out.println("V null"); continue; }
      StringBuilder sb = new StringBuilder("O " + r.getClass().getName().replace('.', '/'));
      for (Field f : r.getClass().getDeclaredFields()) {
        if (Modifier.isStatic(f.getModifiers())) continue;
        f.setAccessible(true);
        Object v = f.get(r);
        if (v != null && v.getClass().isArray()) sb.append(" " + f.getName() + ".length=" + Array.getLength(v));
      }
      System.out.println(sb);
    }
  }
}

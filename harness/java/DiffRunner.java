import java.io.*;
import java.lang.reflect.*;
import java.net.*;
import java.nio.file.*;
import java.util.*;

/** HotSpot side of the differential test.
 *  java DiffRunner <classdir> <binary class name> <method> <descriptor> <inputs>
 *  Prints "V <n>" | "V void" | "E <internal class name of the thrown exception>" per input line. */
public class DiffRunner {
    static String desc(Class<?> c) {
        if (c == int.class) return "I"; if (c == long.class) return "J"; if (c == boolean.class) return "Z";
        if (c == byte.class) return "B"; if (c == char.class) return "C"; if (c == short.class) return "S";
        if (c == float.class) return "F"; if (c == double.class) return "D"; if (c == void.class) return "V";
        if (c.isArray()) return c.getName().replace('.', '/');
        return "L" + c.getName().replace('.', '/') + ";";
    }
    public static void main(String[] a) throws Exception {
        URLClassLoader cl = new URLClassLoader(new URL[]{Paths.get(a[0]).toUri().toURL()}, DiffRunner.class.getClassLoader());
        Class<?> k = Class.forName(a[1], false, cl);
        Method m = null;
        for (Method x : k.getDeclaredMethods()) {
            StringBuilder d = new StringBuilder("(");
            for (Class<?> p : x.getParameterTypes()) d.append(desc(p));
            d.append(")").append(desc(x.getReturnType()));
            if (x.getName().equals(a[2]) && d.toString().equals(a[3])) m = x;
        }
        if (m == null) throw new NoSuchMethodException(a[2] + a[3]);
        m.setAccessible(true);
        Class<?>[] pt = m.getParameterTypes();
        PrintWriter out = new PrintWriter(new BufferedWriter(new OutputStreamWriter(System.out)));
        try (BufferedReader r = Files.newBufferedReader(Paths.get(a[4]))) {
            String line;
            while ((line = r.readLine()) != null) {
                String[] t = line.trim().split(" +");
                Object[] args = new Object[pt.length];
                for (int i = 0; i < pt.length; i++) {
                    long v = Long.parseLong(t[i]);
                    if (pt[i] == long.class) args[i] = v;
                    else if (pt[i] == int.class) args[i] = (int) v;
                    else if (pt[i] == boolean.class) args[i] = v != 0;
                    else if (pt[i] == byte.class) args[i] = (byte) v;
                    else if (pt[i] == short.class) args[i] = (short) v;
                    else if (pt[i] == char.class) args[i] = (char) v;
                    else throw new IllegalArgumentException("type " + pt[i]);
                }
                String res;
                try {
                    Object o = m.invoke(null, args);
                    if (m.getReturnType() == void.class) res = "V void";
                    else if (o instanceof Boolean b) res = "V " + (b ? 1 : 0);
                    else if (o instanceof Character c) res = "V " + (int) c;
                    else res = "V " + ((Number) o).longValue();
                } catch (InvocationTargetException e) {
                    res = "E " + e.getCause().getClass().getName().replace('.', '/');
                }
                out.println(res);
            }
        }
        out.flush();
    }
}

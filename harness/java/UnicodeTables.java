import java.io.*;

/** Dumps the JDK's Character tables used by the model's Unicode environment (uenv):
 *  one line per code point whose data differs from the identity default:
 *  "cp upper lower digit10 flags" with flags bits 1=whitespace 2=letter 4=digit 8=upper 16=lower.
 *  Code points not listed have upper=lower=cp, digit=-1, flags=0. */
public class UnicodeTables {
    public static void main(String[] a) throws IOException {
        try (PrintWriter w = new PrintWriter(new BufferedWriter(new FileWriter(a[0])))) {
            w.println("# java.version=" + System.getProperty("java.version") + " unicode tables, Character.*(int)");
            for (int cp = 0; cp <= Character.MAX_CODE_POINT; cp++) {
                int up = Character.toUpperCase(cp), lo = Character.toLowerCase(cp), d = Character.digit(cp, 10);
                int f = (Character.isWhitespace(cp) ? 1 : 0) | (Character.isLetter(cp) ? 2 : 0) | (Character.isDigit(cp) ? 4 : 0)
                      | (Character.isUpperCase(cp) ? 8 : 0) | (Character.isLowerCase(cp) ? 16 : 0);
                if (up != cp || lo != cp || d != -1 || f != 0) w.println(cp + " " + up + " " + lo + " " + d + " " + f);
            }
        }
    }
}

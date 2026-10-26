import java.io.*;

/** Dumps the JDK's Character tables used by the model's Unicode environment (uenv):
 *  one line per code point whose data differs from the identity default:
 *  "cp upper lower digit10 flags type props numeric" with flags bits 1=whitespace 2=letter 4=digit
 *  8=upper 16=lower, type = Character.getType, props bits 1=isJavaIdentifierStart
 *  2=isJavaIdentifierPart 4=isUnicodeIdentifierStart 8=isUnicodeIdentifierPart
 *  16=isIdentifierIgnorable 32=isAlphabetic 64=isIdeographic 128=isSpaceChar 256=isTitleCase
 *  512=isDefined 1024=isMirrored 2048=toUpperCaseEx differs from toUpperCase (read by reflection:
 *  run with --add-opens java.base/java.lang=ALL-UNNAMED), numeric = Character.getNumericValue, upperx = the UTF-16 units of
 *  String.toUpperCase(Locale.ROOT) of the code point when they differ from Character.toUpperCase
 *  (special casing, e.g. U+00DF -> "SS"), packed as u1 + u2*2^16 + u3*2^32 + n*2^48, else -1.
 *  Code points not listed have upper=lower=cp, digit=-1, flags=0, type=0, props=0, numeric=-1. */
public class UnicodeTables {
    public static void main(String[] a) throws Exception {
        java.lang.reflect.Method ex = Character.class.getDeclaredMethod("toUpperCaseEx", int.class);
        ex.setAccessible(true);
        try (PrintWriter w = new PrintWriter(new BufferedWriter(new FileWriter(a[0])))) {
            w.println("# java.version=" + System.getProperty("java.version") + " unicode tables, Character.*(int)");
            for (int cp = 0; cp <= Character.MAX_CODE_POINT; cp++) {
                int up = Character.toUpperCase(cp), lo = Character.toLowerCase(cp), d = Character.digit(cp, 10);
                int f = (Character.isWhitespace(cp) ? 1 : 0) | (Character.isLetter(cp) ? 2 : 0) | (Character.isDigit(cp) ? 4 : 0)
                      | (Character.isUpperCase(cp) ? 8 : 0) | (Character.isLowerCase(cp) ? 16 : 0);
                int ty = Character.getType(cp);
                int pr = (Character.isJavaIdentifierStart(cp) ? 1 : 0) | (Character.isJavaIdentifierPart(cp) ? 2 : 0)
                       | (Character.isUnicodeIdentifierStart(cp) ? 4 : 0) | (Character.isUnicodeIdentifierPart(cp) ? 8 : 0)
                       | (Character.isIdentifierIgnorable(cp) ? 16 : 0) | (Character.isAlphabetic(cp) ? 32 : 0)
                       | (Character.isIdeographic(cp) ? 64 : 0) | (Character.isSpaceChar(cp) ? 128 : 0)
                       | (Character.isTitleCase(cp) ? 256 : 0) | (Character.isDefined(cp) ? 512 : 0)
                       | (Character.isMirrored(cp) ? 1024 : 0)
                       | (((Integer) ex.invoke(null, cp)) != up ? 2048 : 0);
                int nv = Character.getNumericValue(cp);
                long ux = -1;
                if (!Character.isSurrogate((char) cp) || cp > 0xffff) {
                    String su = new String(Character.toChars(cp)).toUpperCase(java.util.Locale.ROOT);
                    if (!su.equals(new String(Character.toChars(up)))) {
                        ux = (long) su.length() << 48;
                        for (int k = 0; k < su.length(); k++) ux += (long) su.charAt(k) << (16 * k);
                    }
                }
                if (up != cp || lo != cp || d != -1 || f != 0 || ty != 0 || pr != 0 || nv != -1 || ux != -1)
                    w.println(cp + " " + up + " " + lo + " " + d + " " + f + " " + ty + " " + pr + " " + nv + " " + ux);
            }
        }
    }
}

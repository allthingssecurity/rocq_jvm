package org.rocqjvm.jdkmodel;

import java.util.Arrays;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/** Differential tests of java.util.regex: random patterns (groups, alternation, classes, quantifiers in
 *  their three forms, anchors, back references, lookahead, inline flags) over random inputs. */
public final class RegexOps {
    private RegexOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static int groups;

    static String atom(int depth) {
        switch (r(depth > 2 ? 9 : 16)) {
            case 0: case 1: return "a";
            case 2: return "b";
            case 3: return ".";
            case 4: return "[ab]";
            case 5: return "[^a\\n]";
            case 6: return r(2) == 0 ? "\\d" : "\\w";
            case 7: return r(2) == 0 ? "\\s" : "[a-c1]";
            case 8: return "c";
            case 9: case 10: groups++; return "(" + re(depth + 1) + ")";
            case 11: return "(?:" + re(depth + 1) + ")";
            case 12: return groups > 0 ? "\\" + (1 + r(groups)) : "a";
            case 13: return (r(2) == 0 ? "(?=" : "(?!") + re(depth + 1) + ")";
            case 14: return r(3) == 0 ? "^" : r(2) == 0 ? "$" : "\\b";
            default: groups++; return "(?<g" + groups + ">" + re(depth + 1) + ")";
        }
    }

    static String quant() {
        String q;
        switch (r(10)) {
            case 0: q = "*"; break;
            case 1: q = "+"; break;
            case 2: q = "?"; break;
            case 3: q = "{1,2}"; break;
            case 4: q = "{2}"; break;
            default: return "";
        }
        int k = r(5);
        return k == 0 ? q + "?" : k == 1 ? q + "+" : q;
    }

    static String re(int depth) {
        StringBuilder b = new StringBuilder();
        int n = 1 + r(3);
        for (int i = 0; i < n; i++) b.append(atom(depth)).append(quant());
        if (depth < 2 && r(5) == 0) b.append('|').append(re(depth + 1));
        return b.toString();
    }

    static String input() {
        String al = "aab1 _bc\nA";
        StringBuilder b = new StringBuilder();
        int n = r(9);
        for (int i = 0; i < n; i++) b.append(al.charAt(r(al.length())));
        return b.toString();
    }

    public static String fuzz(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int round = 0; round < 4; round++) {
            groups = 0;
            String re = (r(6) == 0 ? "(?i)" : "") + re(0);
            String in = input();
            out.append(re.replace("\n", "\\n")).append(" @ ").append(in.replace("\n", "\\n")).append(" => ");
            try {
                Pattern p = Pattern.compile(re, r(4) == 0 ? Pattern.MULTILINE : 0);
                Matcher m = p.matcher(in);
                out.append(m.matches()).append(' ').append(m.lookingAt()).append(' ');
                m.reset();
                while (m.find()) {
                    out.append('[').append(m.start()).append(',').append(m.end());
                    for (int g = 1; g <= m.groupCount(); g++) out.append(',').append(m.group(g));
                    out.append(']');
                }
                out.append(' ').append(p.matcher(in).replaceAll("<$0>"));
                out.append(' ').append(Arrays.toString(p.split(in))).append(Arrays.toString(p.split(in, -1)))
                   .append(Arrays.toString(p.split(in, 2)));
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName());
            }
            out.append(" ;; ");
        }
        return out.toString();
    }

    /** Typical uses: validation, extraction with named groups, replacement with references, quoting. */
    public static String common(int n) {
        String in = "id=" + n + ", name=user" + (n % 7) + "; ip=10.0." + (n & 255) + ".1";
        StringBuilder out = new StringBuilder();
        Matcher m = Pattern.compile("(?<key>\\w+)=(?<val>[^,;]+)").matcher(in);
        while (m.find()) out.append(m.group("key")).append(':').append(m.group("val")).append('|');
        out.append(Pattern.matches("\\d{1,3}(\\.\\d{1,3}){3}", "10.0." + (n & 255) + ".1"));
        out.append(Pattern.compile("(\\w+)@(\\w+)\\.com").matcher("mail a@b.com and cc@dd.com").replaceAll("$2 at $2:$1"));
        out.append(Pattern.compile("[,;]\\s*").split(in).length);
        out.append(Pattern.compile(Pattern.quote("a.b")).matcher("a.b axb").replaceAll("X"));
        out.append(Matcher.quoteReplacement("$1\\"));
        out.append(Pattern.compile("^\\s*$", Pattern.MULTILINE).matcher("a\n \nb").find());
        out.append(Pattern.compile("CAMEL", Pattern.CASE_INSENSITIVE).matcher("camel-Camel").replaceFirst("x"));
        try { Pattern.compile("(a)").matcher("a").replaceAll("$2"); } catch (IndexOutOfBoundsException e) { out.append(" ioobe:").append(e.getMessage()); }
        try { Pattern.compile("a").matcher("b").group(); } catch (IllegalStateException e) { out.append(" ise:").append(e.getMessage()); }
        return out.toString();
    }
}

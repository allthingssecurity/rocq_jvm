package org.rocqjvm.jdkmodel;

/** Differential tests of the String methods defined by regular expressions: matches, replaceAll,
 *  replaceFirst, split (with and without a limit, including the one-character fast path), over
 *  random patterns from a pool and random inputs; the result, or the exception class. */
public final class StrRegex {
    private StrRegex() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static final String[] PATS = {
        ",", ":", "\\.", "\\s+", "\\s*,\\s*", "a+", "(a)(b)?", "[ab]", "x*", "", "\\d+", "(?i)A",
        "b|", "^a", "$", "\\b", "(\\w)\\1", "[^,]+", "a(?=b)", ".", "\\|", "(?<n>a)b"
    };
    static final String[] REPS = { "", "-", "$1", "<$0>", "\\$", "x$2y", "${n}", "[$0$0]" };

    static String input() {
        String al = "aab, :.1 x|AB";
        StringBuilder b = new StringBuilder();
        int n = r(12);
        for (int i = 0; i < n; i++) b.append(al.charAt(r(al.length())));
        return b.toString();
    }

    static void show(StringBuilder out, String[] a) {
        out.append(a.length).append('{');
        for (String x : a) out.append(x).append('/');
        out.append('}');
    }

    public static String ops(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        int rounds = 4 + r(6);
        for (int k = 0; k < rounds; k++) {
            String in = input();
            String p = PATS[r(PATS.length)];
            try {
                switch (r(6)) {
                    case 0: out.append(in.matches(p)); break;
                    case 1: out.append(in.replaceAll(p, REPS[r(REPS.length)])); break;
                    case 2: out.append(in.replaceFirst(p, REPS[r(REPS.length)])); break;
                    case 3: show(out, in.split(p)); break;
                    default: show(out, in.split(p, r(5) - 1)); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(e.getClass().getSimpleName());
            }
            out.append(';');
        }
        return out.toString();
    }

    /** Typical uses: CSV and key=value parsing, whitespace normalisation, validation. */
    public static String common(int n) {
        String line = " k" + (n % 7) + " = v" + n + " ,  b=" + (n % 3) + ",,c= ";
        StringBuilder out = new StringBuilder();
        for (String kv : line.trim().split("\\s*,\\s*")) {
            String[] p = kv.split("\\s*=\\s*", 2);
            out.append(p.length).append(':').append(p[0]).append(p.length > 1 ? "->" + p[1] : "").append('|');
        }
        out.append("a  b\t c".replaceAll("\\s+", " "));
        out.append(String.valueOf(n).matches("-?\\d+")).append(("x" + n).matches("\\d+"));
        out.append("2026-10-25".replaceFirst("(\\d+)-(\\d+)-(\\d+)", "$3/$2/$1"));
        out.append("a,b,,c,,".split(",").length).append("a,b,,c,,".split(",", -1).length);
        return out.toString();
    }
}

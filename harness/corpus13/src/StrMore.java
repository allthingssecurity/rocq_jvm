// corpus13: more String methods (repeat, isBlank, strip*, ASCII case conversion, replace of
// CharSequences, split on one character, join, compareToIgnoreCase), against HotSpot.
public class StrMore {
    static String pick(int n) {
        String[] xs = { "", " ", "a,b,,c,,", ",x,", "  Hello World \t", "abcabc", "MiXeD-Case_09", "été", "a||b|", "x.y.z", "one" };
        return xs[Math.floorMod(n, xs.length)];
    }
    static String show(String[] a) { StringBuilder b = new StringBuilder("["); for (String x : a) b.append('<').append(x).append('>'); return b.append(']').toString(); }

    public static String repeats(int n) {
        String s = pick(n);
        try { return s.repeat(Math.floorMod(n, 4)) + "|" + (s.repeat(1) == s) + "|" + s.repeat(0).isEmpty() + "|" + s.repeat(n % 3 - 1); }
        catch (IllegalArgumentException e) { return "IAE " + e.getMessage(); }
    }
    public static String blanks(int n) {
        String s = pick(n);
        return s.isBlank() + "|" + s.strip() + "|" + s.stripLeading() + "|" + s.stripTrailing() + "|" + (s.strip() == s);
    }
    public static String cases(int n) {
        String s = pick(n);
        if (s.chars().anyMatch(c -> c > 127)) return "skip";
        return s.toUpperCase() + "|" + s.toLowerCase() + "|" + (s.toLowerCase() == s);
    }
    public static String replaces(int n) {
        String s = pick(n);
        String[] ts = { "a", "abc", "", ",", "||", "zz" };
        String t = ts[Math.floorMod(n / 7, ts.length)];
        return s.replace(t, "-") + "|" + s.replace(t, "") + "|" + (s.replace("zz", "q") == s) + "|" + s.replace((CharSequence) "b", "B");
    }
    public static String splits(int n) {
        String s = pick(n);
        String[] rs = { ",", "\\|", "\\.", "|", ".", "o" };
        String r = rs[Math.floorMod(n / 3, rs.length)];
        if (r.equals("|") || r.equals(".")) r = ",";
        return show(s.split(r)) + show(s.split(r, 2)) + show(s.split(r, -1)) + (s.split("q")[0] == s);
    }
    public static String joins(int n) {
        String s = pick(n);
        return String.join("+", s, "x", null) + "|" + String.join("", new String[0]) + "|" + String.join(s, "a", "b");
    }
    public static int cmpIC(int n) {
        String a = pick(n), b = pick(n / 5);
        return Integer.signum(a.compareToIgnoreCase(b)) * 1000 + a.compareToIgnoreCase(a.toUpperCase().equals(a) ? a : a);
    }
}

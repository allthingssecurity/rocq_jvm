/*
 * rocq-jvm model of java.util.regex.Pattern (clean-room, Apache-2.0), from the class Javadoc:
 * a backtracking matcher over UTF-16 strings without surrogate pairs.
 *
 * Supported constructs: literals and escapes (t n r f a e 0nn xhh u+4 hex digits cX after a backslash, and quoting
 * of metacharacters), \Q...\E, the dot, character classes with ranges, negation, nested classes,
 * union and intersection (&&), the predefined classes \d \D \s \S \w \W \h \H \v \V and POSIX
 * \p{Lower} \p{Upper} \p{Alpha} \p{Digit} \p{Alnum} \p{Punct} \p{Space} \p{XDigit} \p{ASCII}
 * (US-ASCII), the boundary matchers ^ $ \b \B \A \z \Z \G, capturing groups (numbered and named),
 * non-capturing groups, atomic groups, lookahead (positive and negative), back references \n and
 * \k<name>, alternation, and the quantifiers ? * + {n} {n,} {n,m} in their greedy, reluctant and
 * possessive forms; the flags CASE_INSENSITIVE (US-ASCII), MULTILINE, DOTALL, LITERAL, COMMENTS
 * and UNIX_LINES, also inline as (?imsxd-imsxd) and (?imsxd-imsxd:X).
 * Not modelled (STUCK): lookbehind, Unicode properties and blocks beyond the POSIX ones, CANON_EQ,
 * UNICODE_CASE, UNICODE_CHARACTER_CLASS, \R \X \N{..}, surrogate pairs in the pattern or the input,
 * and malformed patterns (the JDK's PatternSyntaxException messages are not modelled).
 */
package java.util.regex;

import java.util.ArrayList;

public final class Pattern implements java.io.Serializable {
    public static final int UNIX_LINES = 0x01;
    public static final int CASE_INSENSITIVE = 0x02;
    public static final int COMMENTS = 0x04;
    public static final int MULTILINE = 0x08;
    public static final int LITERAL = 0x10;
    public static final int DOTALL = 0x20;
    public static final int UNICODE_CASE = 0x40;
    public static final int CANON_EQ = 0x80;
    public static final int UNICODE_CHARACTER_CLASS = 0x100;

    private final String pattern;
    private final int flags;
    final Node root;
    int groupCount;
    final ArrayList<String> groupNames = new ArrayList<>();
    final ArrayList<Integer> groupNumbers = new ArrayList<>();

    private Pattern(String p, int f) {
        if ((f & ~(UNIX_LINES | CASE_INSENSITIVE | COMMENTS | MULTILINE | LITERAL | DOTALL | UNICODE_CASE | CANON_EQ
                   | UNICODE_CHARACTER_CLASS)) != 0)
            throw new IllegalArgumentException("Unknown flag 0x" + Integer.toHexString(f));
        if ((f & (CANON_EQ | UNICODE_CASE | UNICODE_CHARACTER_CLASS)) != 0) throw stuck("CANON_EQ / UNICODE_CASE / UNICODE_CHARACTER_CLASS");
        this.pattern = p;
        this.flags = f;
        for (int i = 0; i < p.length(); i++) {
            if (isSurr(p.charAt(i))) throw stuck("surrogate pairs in a pattern");
        }
        if ((f & LITERAL) != 0) {
            Seq s = new Seq();
            for (int i = 0; i < p.length(); i++) s.add(new Ch(p.charAt(i), (f & CASE_INSENSITIVE) != 0));
            root = s;
        } else {
            Parser ps = new Parser(this, p, f);
            root = ps.parseAll();
        }
    }

    static boolean isSurr(char c) {
        return c >= '\uD800' && c <= '\uDFFF';
    }

    static RuntimeException stuck(String what) {
        return ModelStuckRx.unsupported("regex: " + what);
    }

    public static Pattern compile(String regex) {
        return new Pattern(regex, 0);
    }

    public static Pattern compile(String regex, int flags) {
        return new Pattern(regex, flags);
    }

    public String pattern() {
        return pattern;
    }

    public String toString() {
        return pattern;
    }

    public int flags() {
        return flags;
    }

    public Matcher matcher(CharSequence input) {
        return new Matcher(this, input);
    }

    public static boolean matches(String regex, CharSequence input) {
        return compile(regex).matcher(input).matches();
    }

    public String[] split(CharSequence input) {
        return split(input, 0);
    }

    public String[] split(CharSequence input, int limit) {
        int index = 0;
        boolean matchLimited = limit > 0;
        ArrayList<String> matchList = new ArrayList<>();
        Matcher m = matcher(input);
        String in = input.toString();
        while (m.find()) {
            if (!matchLimited || matchList.size() < limit - 1) {
                if (index == 0 && index == m.start() && m.start() == m.end()) continue;
                matchList.add(in.substring(index, m.start()));
                index = m.end();
            } else if (matchList.size() == limit - 1) {
                matchList.add(in.substring(index));
                index = m.end();
            }
        }
        if (index == 0) return new String[] { in };
        if (!matchLimited || matchList.size() < limit) matchList.add(in.substring(index));
        int resultSize = matchList.size();
        if (limit == 0) {
            while (resultSize > 0 && matchList.get(resultSize - 1).isEmpty()) resultSize--;
        }
        String[] result = new String[resultSize];
        for (int i = 0; i < resultSize; i++) result[i] = matchList.get(i);
        return result;
    }

    public static String quote(String s) {
        int slashEIndex = s.indexOf("\\E");
        if (slashEIndex == -1) return "\\Q" + s + "\\E";
        StringBuilder sb = new StringBuilder(s.length() * 2);
        sb.append("\\Q");
        int current = 0;
        while ((slashEIndex = s.indexOf("\\E", current)) != -1) {
            sb.append(s.substring(current, slashEIndex));
            current = slashEIndex + 2;
            sb.append("\\E\\\\E\\Q");
        }
        sb.append(s.substring(current, s.length()));
        return sb.append("\\E").toString();
    }

    int groupIndex(String name) {
        int i = groupNames.indexOf(name);
        return i < 0 ? -1 : groupNumbers.get(i);
    }

    // ---- the pattern tree ----

    /** A continuation: does the rest of the pattern match from position i? */
    interface Cont {
        boolean at(int i);
    }

    abstract static class Node {
        abstract boolean m(Matcher x, int i, Cont k);
    }

    static boolean isLineTerm(char c, boolean unix) {
        return unix ? c == '\n' : (c == '\n' || c == '\r' || c == '\u0085' || c == ' ' || c == ' ');
    }

    static char lowerAscii(char c) {
        return (c >= 'A' && c <= 'Z') ? (char) (c + 32) : c;
    }

    static final class Ch extends Node {
        final char c;
        final boolean ci;
        Ch(char c, boolean ci) { this.c = c; this.ci = ci; }
        boolean m(Matcher x, int i, Cont k) {
            if (i >= x.to) { x.hitEnd = true; return false; }
            char d = x.text.charAt(i);
            boolean ok = ci ? lowerAscii(d) == lowerAscii(c) : d == c;
            return ok && k.at(i + 1);
        }
    }

    /** A set of characters (a class, the dot, a predefined class). */
    abstract static class CharSet {
        abstract boolean has(char c);
    }

    static final class SetNode extends Node {
        final CharSet set;
        SetNode(CharSet set) { this.set = set; }
        boolean m(Matcher x, int i, Cont k) {
            if (i >= x.to) { x.hitEnd = true; return false; }
            return set.has(x.text.charAt(i)) && k.at(i + 1);
        }
    }

    static final class Range extends CharSet {
        final char lo, hi;
        final boolean ci;
        Range(char lo, char hi, boolean ci) { this.lo = lo; this.hi = hi; this.ci = ci; }
        boolean has(char c) {
            if (c >= lo && c <= hi) return true;
            if (ci) {
                char l = lowerAscii(c), u = (c >= 'a' && c <= 'z') ? (char) (c - 32) : c;
                return (l >= lo && l <= hi) || (u >= lo && u <= hi);
            }
            return false;
        }
    }

    static final class Union extends CharSet {
        final ArrayList<CharSet> parts = new ArrayList<>();
        boolean has(char c) {
            for (CharSet p : parts) if (p.has(c)) return true;
            return false;
        }
    }

    static final class Inter extends CharSet {
        final CharSet a, b;
        Inter(CharSet a, CharSet b) { this.a = a; this.b = b; }
        boolean has(char c) { return a.has(c) && b.has(c); }
    }

    static final class Not extends CharSet {
        final CharSet a;
        Not(CharSet a) { this.a = a; }
        boolean has(char c) { return !a.has(c); }
    }

    static final class Pred extends CharSet {
        final int kind;   // see Parser.predef
        Pred(int kind) { this.kind = kind; }
        boolean has(char c) {
            switch (kind) {
                case 'd': return c >= '0' && c <= '9';
                case 's': return c == ' ' || c == '\t' || c == '\n' || c == 0x0B || c == '\f' || c == '\r';
                case 'w': return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c == '_';
                case 'h': return c == ' ' || c == '\t' || c == 0xA0 || c == 0x1680 || c == 0x180e || (c >= 0x2000 && c <= 0x200a)
                              || c == 0x202f || c == 0x205f || c == 0x3000;
                case 'v': return c == '\n' || c == 0x0B || c == '\f' || c == '\r' || c == 0x85 || c == 0x2028 || c == 0x2029;
                case 'L': return c >= 'a' && c <= 'z';                          // Lower
                case 'U': return c >= 'A' && c <= 'Z';                          // Upper
                case 'A': return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');   // Alpha
                case 'N': return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9');   // Alnum
                case 'P': return (c >= 0x21 && c <= 0x2f) || (c >= 0x3a && c <= 0x40) || (c >= 0x5b && c <= 0x60) || (c >= 0x7b && c <= 0x7e);
                case 'X': return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
                case 'C': return c < 0x80;                                     // ASCII
                case 'G': return c >= 0x21 && c <= 0x7e;                       // Graph
                case 'R': return c >= 0x20 && c <= 0x7e;                       // Print
                case 'B': return c == ' ' || c == '\t';                        // Blank
                case 'K': return c < 0x20 || c == 0x7f;                        // Cntrl
                default: return false;
            }
        }
    }

    static final class Dot extends CharSet {
        final boolean all, unix;
        Dot(boolean all, boolean unix) { this.all = all; this.unix = unix; }
        boolean has(char c) { return all || !isLineTerm(c, unix); }
    }

    static final class Seq extends Node {
        final ArrayList<Node> items = new ArrayList<>();
        void add(Node n) { items.add(n); }
        boolean m(Matcher x, int i, Cont k) { return from(0, x, i, k); }
        private boolean from(int j, Matcher x, int i, Cont k) {
            if (j == items.size()) return k.at(i);
            return items.get(j).m(x, i, p -> from(j + 1, x, p, k));
        }
    }

    static final class Alt extends Node {
        final ArrayList<Node> alts = new ArrayList<>();
        boolean m(Matcher x, int i, Cont k) {
            for (Node a : alts) {
                if (a.m(x, i, k)) return true;
            }
            return false;
        }
    }

    static final class Group extends Node {
        final int n;
        final Node body;
        /** Inside a quantifier or an atomic group: when such a capture is undone by backtracking, the
         *  JDK may keep it (its Curly node matches each iteration on its own), so the value is then
         *  not claimed (Matcher.unc). */
        boolean leaky;
        Group(int n, Node body) { this.n = n; this.body = body; }
        boolean m(Matcher x, int i, Cont k) {
            int os = x.gs[n], oe = x.ge[n];
            boolean ou = x.unc[n];
            boolean r = body.m(x, i, p -> {
                int ss = x.gs[n], se = x.ge[n];
                boolean su = x.unc[n];
                x.gs[n] = i;
                x.ge[n] = p;
                x.unc[n] = false;
                if (k.at(p)) return true;
                x.gs[n] = ss;
                x.ge[n] = se;
                x.unc[n] = su || leaky;
                return false;
            });
            if (!r) {
                x.gs[n] = os;
                x.ge[n] = oe;
                x.unc[n] = x.unc[n] || ou;
            }
            return r;
        }
    }

    /** Mark the groups inside a quantified or atomic node as leaky. */
    static void markLeaky(Node n) {
        if (n instanceof Group) { ((Group) n).leaky = true; markLeaky(((Group) n).body); }
        else if (n instanceof Seq) { for (Node c : ((Seq) n).items) markLeaky(c); }
        else if (n instanceof Alt) { for (Node c : ((Alt) n).alts) markLeaky(c); }
        else if (n instanceof Repeat) markLeaky(((Repeat) n).body);
        else if (n instanceof Atomic) markLeaky(((Atomic) n).body);
        else if (n instanceof Look) markLeaky(((Look) n).body);
    }

    /** (?>X) and possessive quantifiers: X matches once, its end is not backtracked into. */
    static final class Atomic extends Node {
        final Node body;
        Atomic(Node body) { this.body = body; }
        boolean m(Matcher x, int i, Cont k) {
            int[] end = { -1 };
            int[] gs = x.gs.clone(), ge = x.ge.clone();
            if (!body.m(x, i, p -> { end[0] = p; return true; })) return false;
            if (k.at(end[0])) return true;
            for (int g = 0; g < gs.length; g++) {
                if (x.gs[g] != gs[g] || x.ge[g] != ge[g]) x.unc[g] = true;   // the JDK may keep it
            }
            System.arraycopy(gs, 0, x.gs, 0, gs.length);
            System.arraycopy(ge, 0, x.ge, 0, ge.length);
            return false;
        }
    }

    /** Lookahead. As in the JDK, captures made by the condition are kept, whatever the outcome. */
    static final class Look extends Node {
        final Node body;
        final boolean neg;
        Look(Node body, boolean neg) { this.body = body; this.neg = neg; }
        boolean m(Matcher x, int i, Cont k) {
            boolean r = body.m(x, i, p -> true);   // within the region (opaque bounds)
            return (neg ? !r : r) && k.at(i);
        }
    }

    static final class Repeat extends Node {
        final Node body;
        final int min, max;   // max -1: unbounded
        final int kind;       // 0 greedy, 1 reluctant
        Repeat(Node body, int min, int max, int kind) { this.body = body; this.min = min; this.max = max; this.kind = kind; }
        boolean m(Matcher x, int i, Cont k) { return iter(x, i, 0, -1, k); }
        private boolean iter(Matcher x, int i, int count, int last, Cont k) {
            if (count < min) {
                return body.m(x, i, p -> iter(x, p, count + 1, i, k));
            }
            boolean more = (max < 0 || count < max) && i != last;   // an empty iteration ends the loop
            if (kind == 0) {
                if (more && body.m(x, i, p -> p != i && iter(x, p, count + 1, i, k))) return true;
                return k.at(i);
            } else {
                if (k.at(i)) return true;
                return more && body.m(x, i, p -> p != i && iter(x, p, count + 1, i, k));
            }
        }
    }

    static final class BackRef extends Node {
        final int n;
        final boolean ci;
        BackRef(int n, boolean ci) { this.n = n; this.ci = ci; }
        boolean m(Matcher x, int i, Cont k) {
            if (x.unc[n]) throw stuck("a back reference to a capture the JDK may have kept");
            int s = x.gs[n], e = x.ge[n];
            if (s < 0) return false;
            int len = e - s;
            if (i + len > x.to) { x.hitEnd = true; return false; }
            for (int j = 0; j < len; j++) {
                char a = x.text.charAt(s + j), b = x.text.charAt(i + j);
                if (ci ? lowerAscii(a) != lowerAscii(b) : a != b) return false;
            }
            return k.at(i + len);
        }
    }

    static final class Assert extends Node {
        final int kind;
        final boolean multi, unix;
        Assert(int kind, boolean multi, boolean unix) { this.kind = kind; this.multi = multi; this.unix = unix; }
        boolean m(Matcher x, int i, Cont k) { return test(x, i) && k.at(i); }
        private boolean isWord(Matcher x, int j) {
            if (j < 0 || j >= x.text.length()) return false;
            char c = x.text.charAt(j);
            return Character.isLetterOrDigit(c) || c == '_';
        }
        private boolean test(Matcher x, int i) {
            int from = x.anchoringBounds ? x.from : 0;
            int to = x.anchoringBounds ? x.to : x.text.length();
            switch (kind) {
                case '^':
                    if (!multi) return i == from;
                    if (i == from) return true;
                    if (i >= to) return false;
                    char p = x.text.charAt(i - 1);
                    if (unix) return p == '\n';
                    if (p == '\r' && x.text.charAt(i) == '\n') return false;
                    return isLineTerm(p, false);
                case '$':
                    if (multi) {
                        if (i >= to) { x.hitEnd = true; return true; }
                        char c = x.text.charAt(i);
                        if (unix) return c == '\n';
                        if (c == '\n' && i > 0 && x.text.charAt(i - 1) == '\r') return false;
                        return isLineTerm(c, false);
                    }
                    // fall through to \Z
                case 'Z':
                    if (i >= to) { x.hitEnd = true; return true; }
                    x.hitEnd = true;
                    if (unix) return i == to - 1 && x.text.charAt(i) == '\n';
                    if (i == to - 1) return isLineTerm(x.text.charAt(i), false);
                    if (i == to - 2) return x.text.charAt(i) == '\r' && x.text.charAt(i + 1) == '\n';
                    return false;
                case 'A': return i == from;
                case 'z': if (i >= to) x.hitEnd = true; return i == to;
                case 'G': return i == x.lastAppendOrMatchEnd();
                case 'b': return isWord(x, i - 1) != isWord(x, i);
                case 'B': return isWord(x, i - 1) == isWord(x, i);
                default: return false;
            }
        }
    }

    // ---- the parser ----

    static final class Parser {
        final Pattern pat;
        final String s;
        int i;
        int flags;

        Parser(Pattern pat, String s, int flags) {
            this.pat = pat;
            this.s = s;
            this.flags = flags;
        }

        boolean ci() { return (flags & CASE_INSENSITIVE) != 0; }

        RuntimeException bad() { return stuck("malformed pattern (PatternSyntaxException not modelled): " + s); }

        Node parseAll() {
            Node n = alt();
            if (i < s.length()) throw bad();   // an unmatched ')'
            return n;
        }

        private void skipComments() {
            if ((flags & COMMENTS) == 0) return;
            while (i < s.length()) {
                char c = s.charAt(i);
                if (c == ' ' || c == '\t' || c == '\n' || c == 0x0B || c == '\f' || c == '\r') i++;
                else if (c == '#') { while (i < s.length() && !isLineTerm(s.charAt(i), false)) i++; }
                else break;
            }
        }

        Node alt() {
            Alt a = new Alt();
            a.alts.add(seq());
            while (i < s.length() && s.charAt(i) == '|') {
                i++;
                a.alts.add(seq());
            }
            return a.alts.size() == 1 ? a.alts.get(0) : a;
        }

        Node seq() {
            Seq q = new Seq();
            for (;;) {
                skipComments();
                if (i >= s.length()) break;
                char c = s.charAt(i);
                if (c == '|' || c == ')') break;
                Node atom = atom();
                if (atom == null) continue;
                q.add(quant(atom));
            }
            return q;
        }

        private int num() {
            int st = i;
            while (i < s.length() && s.charAt(i) >= '0' && s.charAt(i) <= '9') i++;
            if (st == i) throw bad();
            return Integer.parseInt(s.substring(st, i));
        }

        Node quant(Node atom) {
            skipComments();
            if (i >= s.length()) return atom;
            char c = s.charAt(i);
            int min, max;
            if (c == '?') { min = 0; max = 1; i++; }
            else if (c == '*') { min = 0; max = -1; i++; }
            else if (c == '+') { min = 1; max = -1; i++; }
            else if (c == '{') {
                i++;
                min = num();
                max = min;
                if (i < s.length() && s.charAt(i) == ',') {
                    i++;
                    max = (i < s.length() && s.charAt(i) == '}') ? -1 : num();
                }
                if (i >= s.length() || s.charAt(i) != '}') throw bad();
                i++;
                if (max >= 0 && max < min) throw bad();
            } else {
                return atom;
            }
            markLeaky(atom);
            if (i < s.length() && s.charAt(i) == '?') { i++; return new Repeat(atom, min, max, 1); }
            if (i < s.length() && s.charAt(i) == '+') { i++; return new Atomic(new Repeat(atom, min, max, 0)); }
            return new Repeat(atom, min, max, 0);
        }

        /** An atom, or null for something that matches nothing by itself (inline flags). */
        Node atom() {
            char c = s.charAt(i++);
            boolean multi = (flags & MULTILINE) != 0, unix = (flags & UNIX_LINES) != 0;
            switch (c) {
                case '.': return new SetNode(new Dot((flags & DOTALL) != 0, unix));
                case '^': return new Assert('^', multi, unix);
                case '$': return new Assert('$', multi, unix);
                case '[': return new SetNode(cls());
                case '(': return group();
                case '\\': return escape();
                case '*': case '+': case '?': case '{': throw bad();
                default: return new Ch(c, ci());
            }
        }

        Node group() {
            if (i < s.length() && s.charAt(i) == '?') {
                i++;
                if (i >= s.length()) throw bad();
                char c = s.charAt(i++);
                if (c == ':') return close(alt());
                if (c == '>') { Node b = close(alt()); markLeaky(b); return new Atomic(b); }
                if (c == '=') return new Look(close(alt()), false);
                if (c == '!') return new Look(close(alt()), true);
                if (c == '<') {
                    if (i < s.length() && (s.charAt(i) == '=' || s.charAt(i) == '!')) throw stuck("lookbehind");
                    int st = i;
                    while (i < s.length() && s.charAt(i) != '>') i++;
                    if (i >= s.length() || st == i) throw bad();
                    String name = s.substring(st, i);
                    i++;
                    if (pat.groupNames.contains(name)) throw bad();
                    int n = ++pat.groupCount;
                    pat.groupNames.add(name);
                    pat.groupNumbers.add(n);
                    return new Group(n, close(alt()));
                }
                // inline flags (?idmsux-idmsux) or (?idmsux-idmsux:X)
                i--;
                int saved = flags;
                boolean neg = false;
                for (;;) {
                    if (i >= s.length()) throw bad();
                    char f = s.charAt(i++);
                    int bit;
                    switch (f) {
                        case 'i': bit = CASE_INSENSITIVE; break;
                        case 'd': bit = UNIX_LINES; break;
                        case 'm': bit = MULTILINE; break;
                        case 's': bit = DOTALL; break;
                        case 'x': bit = COMMENTS; break;
                        case 'u': case 'U': throw stuck("UNICODE_CASE / UNICODE_CHARACTER_CLASS");
                        case '-': neg = true; continue;
                        case ')': return null;   // applies to the rest of the enclosing group
                        case ':': {
                            Node body = close(alt());
                            flags = saved;
                            return body;
                        }
                        default: throw bad();
                    }
                    if (neg) flags &= ~bit;
                    else flags |= bit;
                }
            }
            int n = ++pat.groupCount;
            int saved = flags;
            Node body = close(alt());
            flags = saved;
            return new Group(n, body);
        }

        Node close(Node body) {
            if (i >= s.length() || s.charAt(i) != ')') throw bad();
            i++;
            return body;
        }

        private int hex(int from, int to) {
            int v = 0;
            for (int j = from; j < to; j++) {
                char h = s.charAt(j);
                int d = (h >= '0' && h <= '9') ? h - '0' : (h >= 'a' && h <= 'f') ? h - 'a' + 10 : (h >= 'A' && h <= 'F') ? h - 'A' + 10 : -1;
                if (d < 0) throw bad();
                v = v * 16 + d;
            }
            return v;
        }

        /** A single escaped character, or -1 if the escape is not a single character. */
        private int escChar(char c) {
            switch (c) {
                case 't': return '\t';
                case 'n': return '\n';
                case 'r': return '\r';
                case 'f': return '\f';
                case 'a': return 7;
                case 'e': return 27;
                case '0': {
                    int v = 0, k = 0;
                    while (k < 3 && i < s.length() && s.charAt(i) >= '0' && s.charAt(i) <= '7' && (k < 2 || v < 040)) {
                        v = v * 8 + (s.charAt(i++) - '0');
                        k++;
                    }
                    if (k == 0) throw bad();
                    return v;
                }
                case 'x': {
                    if (i < s.length() && s.charAt(i) == '{') throw stuck("\\x{...}");
                    if (i + 2 > s.length()) throw bad();
                    int v = hex(i, i + 2);
                    i += 2;
                    return v;
                }
                case 'u': {
                    if (i + 4 > s.length()) throw bad();
                    int v = hex(i, i + 4);
                    i += 4;
                    if (isSurr((char) v)) throw stuck("surrogate escapes");
                    return v;
                }
                case 'c': {
                    if (i >= s.length()) throw bad();
                    return s.charAt(i++) ^ 64;
                }
                default:
                    if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')) return -1;
                    return c;
            }
        }

        private CharSet predef(char c) {
            switch (c) {
                case 'd': return new Pred('d');
                case 'D': return new Not(new Pred('d'));
                case 's': return new Pred('s');
                case 'S': return new Not(new Pred('s'));
                case 'w': return new Pred('w');
                case 'W': return new Not(new Pred('w'));
                case 'h': return new Pred('h');
                case 'H': return new Not(new Pred('h'));
                case 'v': return new Pred('v');
                case 'V': return new Not(new Pred('v'));
                case 'p': case 'P': {
                    CharSet p = posix();
                    return c == 'P' ? new Not(p) : p;
                }
                default: return null;
            }
        }

        private CharSet posix() {
            if (i >= s.length()) throw bad();
            String name;
            if (s.charAt(i) == '{') {
                int e = s.indexOf('}', i);
                if (e < 0) throw bad();
                name = s.substring(i + 1, e);
                i = e + 1;
            } else {
                name = String.valueOf(s.charAt(i++));
            }
            switch (name) {
                case "Lower": return ci() ? new Pred('A') : new Pred('L');
                case "Upper": return ci() ? new Pred('A') : new Pred('U');
                case "Alpha": return new Pred('A');
                case "Digit": return new Pred('d');
                case "Alnum": return new Pred('N');
                case "Punct": return new Pred('P');
                case "Space": return new Pred('s');
                case "XDigit": return new Pred('X');
                case "ASCII": return new Pred('C');
                case "Graph": return new Pred('G');
                case "Print": return new Pred('R');
                case "Blank": return new Pred('B');
                case "Cntrl": return new Pred('K');
                default: throw stuck("Unicode property \\p{" + name + "}");
            }
        }

        Node escape() {
            if (i >= s.length()) throw bad();
            char c = s.charAt(i++);
            boolean multi = (flags & MULTILINE) != 0, unix = (flags & UNIX_LINES) != 0;
            switch (c) {
                case 'b': return new Assert('b', multi, unix);
                case 'B': return new Assert('B', multi, unix);
                case 'A': return new Assert('A', multi, unix);
                case 'z': return new Assert('z', multi, unix);
                case 'Z': return new Assert('Z', multi, unix);
                case 'G': return new Assert('G', multi, unix);
                case 'Q': {
                    int e = s.indexOf("\\E", i);
                    String lit = (e < 0) ? s.substring(i) : s.substring(i, e);
                    i = (e < 0) ? s.length() : e + 2;
                    Seq q = new Seq();
                    for (int j = 0; j < lit.length(); j++) q.add(new Ch(lit.charAt(j), ci()));
                    return q;
                }
                case 'k': {
                    if (i >= s.length() || s.charAt(i) != '<') throw bad();
                    int e = s.indexOf('>', i);
                    if (e < 0) throw bad();
                    int n = pat.groupIndex(s.substring(i + 1, e));
                    if (n < 0) throw bad();
                    i = e + 1;
                    return new BackRef(n, ci());
                }
                case 'R': case 'X': case 'N': throw stuck("\\" + c);
                default:
            }
            if (c >= '1' && c <= '9') {
                // the longest number that names an existing group (at least one digit)
                int n = c - '0';
                while (i < s.length() && s.charAt(i) >= '0' && s.charAt(i) <= '9' && n * 10 + (s.charAt(i) - '0') <= pat.groupCount) {
                    n = n * 10 + (s.charAt(i++) - '0');
                }
                if (n > pat.groupCount) throw stuck("a back reference to a group that is defined later");
                return new BackRef(n, ci());
            }
            CharSet p = predef(c);
            if (p != null) return new SetNode(p);
            int ch = escChar(c);
            if (ch < 0) throw bad();
            return new Ch((char) ch, ci());
        }

        /** A character class after '['. */
        CharSet cls() {
            boolean neg = false;
            if (i < s.length() && s.charAt(i) == '^') { neg = true; i++; }
            CharSet acc = null;
            Union u = new Union();
            boolean first = true;
            for (;;) {
                if (i >= s.length()) throw bad();
                char c = s.charAt(i);
                if (c == ']' && !first) { i++; break; }
                first = false;
                if (c == '[') {
                    i++;
                    u.parts.add(cls());
                    continue;
                }
                if (c == '&' && i + 1 < s.length() && s.charAt(i + 1) == '&') {
                    i += 2;
                    CharSet left = (acc == null) ? u : new Inter(acc, u);
                    acc = left;
                    u = new Union();
                    continue;
                }
                CharSet single = null;
                int lo;
                i++;
                if (c == '\\') {
                    if (i >= s.length()) throw bad();
                    char e = s.charAt(i++);
                    CharSet p = predef(e);
                    if (p != null) { u.parts.add(p); continue; }
                    if (e == 'Q') {
                        int end = s.indexOf("\\E", i);
                        String lit = (end < 0) ? s.substring(i) : s.substring(i, end);
                        i = (end < 0) ? s.length() : end + 2;
                        for (int j = 0; j < lit.length(); j++) u.parts.add(new Range(lit.charAt(j), lit.charAt(j), ci()));
                        continue;
                    }
                    lo = escChar(e);
                    if (lo < 0) throw bad();
                } else {
                    lo = c;
                }
                int hi = lo;
                if (i + 1 < s.length() && s.charAt(i) == '-' && s.charAt(i + 1) != ']') {
                    i++;
                    char d = s.charAt(i++);
                    if (d == '[') throw bad();
                    if (d == '\\') {
                        if (i >= s.length()) throw bad();
                        hi = escChar(s.charAt(i++));
                        if (hi < 0) throw bad();
                    } else {
                        hi = d;
                    }
                    if (hi < lo) throw bad();
                }
                u.parts.add(new Range((char) lo, (char) hi, ci()));
            }
            CharSet r = (acc == null) ? u : new Inter(acc, u);
            return neg ? new Not(r) : r;
        }
    }
}

final class ModelStuckRx {
    private ModelStuckRx() {
    }

    static native RuntimeException unsupported(String what);
}

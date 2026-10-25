/*
 * rocq-jvm model of java.util.regex.Matcher (clean-room, Apache-2.0), from the class Javadoc: matches,
 * lookingAt, find (successive matches; an empty match moves the next search one character on), groups by
 * number and by name, start/end, regions (opaque, anchoring bounds), reset, replaceAll /
 * replaceFirst / appendReplacement / appendTail with $n, ${name} and \ escapes, quoteReplacement, hitEnd.
 * Not modelled (STUCK): results(), toMatchResult(), StringBuffer forms, transparent and non-anchoring
 * bounds, requireEnd.
 */
package java.util.regex;

public final class Matcher {
    private Pattern pat;
    String text;
    int from, to;
    int[] gs, ge;          // group starts and ends (-1: did not match); group 0 is the match
    boolean[] unc;         // the JDK's value of this group may differ (see Pattern.Group.leaky)
    private int first = -1, last = 0;
    private int lastAppendPosition = 0;
    boolean hitEnd;
    final boolean transparentBounds = false;
    final boolean anchoringBounds = true;

    Matcher(Pattern pat, CharSequence input) {
        this.pat = pat;
        this.text = input.toString();
        for (int i = 0; i < text.length(); i++) {
            if (Pattern.isSurr(text.charAt(i))) throw Pattern.stuck("surrogate pairs in the input");
        }
        this.from = 0;
        this.to = text.length();
        alloc();
    }

    private void alloc() {
        gs = new int[pat.groupCount + 1];
        ge = new int[pat.groupCount + 1];
        unc = new boolean[pat.groupCount + 1];
        clearGroups();
    }

    private void clearGroups() {
        for (int k = 0; k < gs.length; k++) { gs[k] = -1; ge[k] = -1; unc[k] = false; }
    }

    int lastAppendOrMatchEnd() {
        return last;
    }

    public Pattern pattern() {
        return pat;
    }

    public Matcher usePattern(Pattern newPattern) {
        if (newPattern == null) throw new IllegalArgumentException("Pattern cannot be null");
        pat = newPattern;
        alloc();
        return this;
    }

    public Matcher reset() {
        first = -1;
        last = 0;
        from = 0;
        to = text.length();
        lastAppendPosition = 0;
        clearGroups();
        return this;
    }

    public Matcher reset(CharSequence input) {
        text = input.toString();
        for (int i = 0; i < text.length(); i++) {
            if (Pattern.isSurr(text.charAt(i))) throw Pattern.stuck("surrogate pairs in the input");
        }
        return reset();
    }

    public Matcher region(int start, int end) {
        if (start < 0 || start > text.length()) throw new IndexOutOfBoundsException("start");
        if (end < 0 || end > text.length()) throw new IndexOutOfBoundsException("end");
        if (start > end) throw new IndexOutOfBoundsException("start > end");
        reset();
        from = start;
        to = end;
        return this;
    }

    public int regionStart() {
        return from;
    }

    public int regionEnd() {
        return to;
    }

    public boolean hitEnd() {
        return hitEnd;
    }

    /** Try at position i; [whole]: the match must end at the region's end. */
    private boolean attempt(int i, boolean whole) {
        // groups are not cleared between start positions: as in the JDK, a capture made inside a
        // lookahead of a failed attempt stays visible until it is overwritten
        int[] end = { -1 };
        boolean ok = pat.root.m(this, i, p -> {
            if (whole && p != to) return false;
            end[0] = p;
            return true;
        });
        if (ok) {
            first = i;
            last = end[0];
            gs[0] = i;
            ge[0] = end[0];
        } else {
            first = -1;
        }
        return ok;
    }

    public boolean matches() {
        hitEnd = false;
        clearGroups();
        return attempt(from, true);
    }

    public boolean lookingAt() {
        hitEnd = false;
        clearGroups();
        return attempt(from, false);
    }

    public boolean find() {
        int next = last;
        if (next == first) next++;
        if (next < from) next = from;
        if (next > to) {
            clearGroups();
            first = -1;
            return false;
        }
        return search(next);
    }

    public boolean find(int start) {
        int limit = text.length();
        if (start < 0 || start > limit) throw new IndexOutOfBoundsException("Illegal start index");
        reset();
        return search(start);
    }

    private boolean search(int start) {
        hitEnd = false;
        clearGroups();
        for (int i = start; i <= to; i++) {
            if (attempt(i, false)) return true;
        }
        first = -1;
        return false;
    }

    private void ensureMatch() {
        if (first < 0) throw new IllegalStateException("No match found");
    }

    private void certain(int g) {
        if (unc[g]) throw Pattern.stuck("the JDK may keep a capture of a failed quantified attempt (group " + g + ")");
    }

    public int groupCount() {
        return pat.groupCount;
    }

    public String group() {
        return group(0);
    }

    public String group(int group) {
        ensureMatch();
        if (group < 0 || group > groupCount()) throw new IndexOutOfBoundsException("No group " + group);
        certain(group);
        if (gs[group] == -1 || ge[group] == -1) return null;
        return text.substring(gs[group], ge[group]);
    }

    private int named(String name) {
        if (name == null) throw new NullPointerException("Group name");
        int n = pat.groupIndex(name);
        if (n < 0) throw new IllegalArgumentException("No group with name <" + name + ">");
        return n;
    }

    public String group(String name) {
        int n = named(name);
        ensureMatch();
        certain(n);
        if (gs[n] == -1 || ge[n] == -1) return null;
        return text.substring(gs[n], ge[n]);
    }

    public int start() {
        ensureMatch();
        return first;
    }

    public int start(int group) {
        ensureMatch();
        if (group < 0 || group > groupCount()) throw new IndexOutOfBoundsException("No group " + group);
        certain(group);
        return gs[group];
    }

    public int start(String name) {
        int n = named(name);
        ensureMatch();
        certain(n);
        return gs[n];
    }

    public int end() {
        ensureMatch();
        return last;
    }

    public int end(int group) {
        ensureMatch();
        if (group < 0 || group > groupCount()) throw new IndexOutOfBoundsException("No group " + group);
        certain(group);
        return ge[group];
    }

    public int end(String name) {
        int n = named(name);
        ensureMatch();
        certain(n);
        return ge[n];
    }

    public static String quoteReplacement(String s) {
        if ((s.indexOf('\\') == -1) && (s.indexOf('$') == -1)) return s;
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (c == '\\' || c == '$') sb.append('\\');
            sb.append(c);
        }
        return sb.toString();
    }

    private void expand(String replacement, StringBuilder result) {
        int cursor = 0;
        while (cursor < replacement.length()) {
            char nextChar = replacement.charAt(cursor);
            if (nextChar == '\\') {
                cursor++;
                if (cursor == replacement.length()) throw new IllegalArgumentException("character to be escaped is missing");
                result.append(replacement.charAt(cursor));
                cursor++;
            } else if (nextChar == '$') {
                cursor++;
                if (cursor == replacement.length()) throw new IllegalArgumentException("Illegal group reference: group index is missing");
                nextChar = replacement.charAt(cursor);
                int refNum;
                if (nextChar == '{') {
                    cursor++;
                    StringBuilder gsb = new StringBuilder();
                    while (cursor < replacement.length()) {
                        nextChar = replacement.charAt(cursor);
                        if ((nextChar >= 'a' && nextChar <= 'z') || (nextChar >= 'A' && nextChar <= 'Z') || (nextChar >= '0' && nextChar <= '9')) {
                            gsb.append(nextChar);
                            cursor++;
                        } else {
                            break;
                        }
                    }
                    if (gsb.length() == 0) throw new IllegalArgumentException("named capturing group has 0 length name");
                    if (nextChar != '}') throw new IllegalArgumentException("named capturing group is missing trailing '}'");
                    String gname = gsb.toString();
                    if (gname.charAt(0) >= '0' && gname.charAt(0) <= '9')
                        throw new IllegalArgumentException("capturing group name {" + gname + "} starts with digit character");
                    if (pat.groupIndex(gname) < 0) throw new IllegalArgumentException("No group with name {" + gname + "}");
                    refNum = pat.groupIndex(gname);
                    cursor++;
                } else {
                    refNum = nextChar - '0';
                    if ((refNum < 0) || (refNum > 9)) throw new IllegalArgumentException("Illegal group reference");
                    cursor++;
                    boolean done = false;
                    while (!done) {
                        if (cursor >= replacement.length()) break;
                        int nextDigit = replacement.charAt(cursor) - '0';
                        if ((nextDigit < 0) || (nextDigit > 9)) break;
                        int newRefNum = (refNum * 10) + nextDigit;
                        if (groupCount() < newRefNum) {
                            done = true;
                        } else {
                            refNum = newRefNum;
                            cursor++;
                        }
                    }
                }
                if (start(refNum) != -1 && end(refNum) != -1) result.append(text.substring(start(refNum), end(refNum)));
            } else {
                result.append(nextChar);
                cursor++;
            }
        }
    }

    public Matcher appendReplacement(StringBuilder sb, String replacement) {
        if (first < 0) throw new IllegalStateException("No match available");
        StringBuilder result = new StringBuilder();
        expand(replacement, result);
        sb.append(text.substring(lastAppendPosition, first));
        sb.append(result.toString());
        lastAppendPosition = last;
        return this;
    }

    public StringBuilder appendTail(StringBuilder sb) {
        sb.append(text.substring(lastAppendPosition, text.length()));
        return sb;
    }

    public String replaceAll(String replacement) {
        reset();
        boolean result = find();
        if (result) {
            StringBuilder sb = new StringBuilder();
            do {
                appendReplacement(sb, replacement);
                result = find();
            } while (result);
            appendTail(sb);
            return sb.toString();
        }
        return text;
    }

    public String replaceFirst(String replacement) {
        if (replacement == null) throw new NullPointerException("replacement");
        reset();
        if (!find()) return text;
        StringBuilder sb = new StringBuilder();
        appendReplacement(sb, replacement);
        appendTail(sb);
        return sb.toString();
    }

    public String toString() {
        return "java.util.regex.Matcher[pattern=" + pat.pattern() + " region=" + from + "," + to + " lastmatch="
            + ((first >= 0 && group() != null) ? group() : "") + "]";
    }
}

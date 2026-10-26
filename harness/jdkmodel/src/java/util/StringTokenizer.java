/*
 * rocq-jvm model of java.util.StringTokenizer (clean-room, Apache-2.0), JDK 21 behaviour:
 * delimiters are chars, or code points once a delimiter set with a surrogate has been used (the
 * JDK never switches back), returnDelims returns each delimiter as a one-code-point token,
 * hasMoreTokens remembers the skipped position for the next nextToken (unless the delimiters
 * change), countTokens counts from the current position without moving it, a null delimiter
 * set fails with NullPointerException when tokens are looked for.
 */
package java.util;

public class StringTokenizer implements Enumeration<Object> {
    private int currentPosition;
    private int newPosition;
    private int maxPosition;
    private String str;
    private String delimiters;
    private boolean retDelims;
    private boolean delimsChanged;
    private int maxDelimCodePoint;
    private boolean hasSurrogates = false;
    private int[] delimiterCodePoints;

    private static boolean isHigh(char c) {
        return c >= '\uD800' && c <= '\uDBFF';
    }

    private static boolean isLow(char c) {
        return c >= '\uDC00' && c <= '\uDFFF';
    }

    /** String.codePointAt. */
    private static int codePointAt(String s, int i) {
        char c = s.charAt(i);
        if (isHigh(c) && i + 1 < s.length()) {
            char d = s.charAt(i + 1);
            if (isLow(d)) return ((c - 0xD800) << 10) + (d - 0xDC00) + 0x10000;
        }
        return c;
    }

    private static int charCount(int cp) {
        return cp >= 0x10000 ? 2 : 1;
    }

    private void setMaxDelimCodePoint() {
        if (delimiters == null) {
            maxDelimCodePoint = 0;
            return;
        }
        int m = 0;
        int c;
        int count = 0;
        for (int i = 0; i < delimiters.length(); i += charCount(c)) {
            c = delimiters.charAt(i);
            if (c >= 0xD800 && c <= 0xDFFF) {
                c = codePointAt(delimiters, i);
                hasSurrogates = true;
            }
            if (m < c) m = c;
            count++;
        }
        maxDelimCodePoint = m;
        if (hasSurrogates) {
            delimiterCodePoints = new int[count];
            for (int i = 0, j = 0; i < count; i++) {
                c = codePointAt(delimiters, j);
                delimiterCodePoints[i] = c;
                j += charCount(c);
            }
        }
    }

    public StringTokenizer(String str, String delim, boolean returnDelims) {
        currentPosition = 0;
        newPosition = -1;
        delimsChanged = false;
        this.str = str;
        if (str == null) throw new NullPointerException("Cannot invoke \"String.length()\" because \"str\" is null");
        maxPosition = str.length();
        delimiters = delim;
        retDelims = returnDelims;
        setMaxDelimCodePoint();
    }

    public StringTokenizer(String str, String delim) {
        this(str, delim, false);
    }

    public StringTokenizer(String str) {
        this(str, " \t\n\r\f", false);
    }

    private boolean isDelim(int c) {
        if (c > maxDelimCodePoint) return false;
        if (!hasSurrogates) return delimiters.indexOf(c) >= 0;
        for (int d : delimiterCodePoints) {
            if (d == c) return true;
        }
        return false;
    }

    private int skipDelimiters(int startPos) {
        if (delimiters == null) throw new NullPointerException();
        int position = startPos;
        while (!retDelims && position < maxPosition) {
            if (!hasSurrogates) {
                char c = str.charAt(position);
                if (!isDelim(c)) break;
                position++;
            } else {
                int c = codePointAt(str, position);
                if (!isDelim(c)) break;
                position += charCount(c);
            }
        }
        return position;
    }

    private int scanToken(int startPos) {
        int position = startPos;
        while (position < maxPosition) {
            if (!hasSurrogates) {
                char c = str.charAt(position);
                if (isDelim(c)) break;
                position++;
            } else {
                int c = codePointAt(str, position);
                if (isDelim(c)) break;
                position += charCount(c);
            }
        }
        if (retDelims && startPos == position) {
            if (!hasSurrogates) {
                char c = str.charAt(position);
                if (isDelim(c)) position++;
            } else {
                int c = codePointAt(str, position);
                if (isDelim(c)) position += charCount(c);
            }
        }
        return position;
    }

    public boolean hasMoreTokens() {
        newPosition = skipDelimiters(currentPosition);
        return newPosition < maxPosition;
    }

    public String nextToken() {
        currentPosition = (newPosition >= 0 && !delimsChanged) ? newPosition : skipDelimiters(currentPosition);
        delimsChanged = false;
        newPosition = -1;
        if (currentPosition >= maxPosition) throw new NoSuchElementException();
        int start = currentPosition;
        currentPosition = scanToken(currentPosition);
        return str.substring(start, currentPosition);
    }

    public String nextToken(String delim) {
        delimiters = delim;
        delimsChanged = true;
        setMaxDelimCodePoint();
        return nextToken();
    }

    public boolean hasMoreElements() {
        return hasMoreTokens();
    }

    public Object nextElement() {
        return nextToken();
    }

    public int countTokens() {
        int count = 0;
        int currpos = currentPosition;
        while (currpos < maxPosition) {
            currpos = skipDelimiters(currpos);
            if (currpos >= maxPosition) break;
            currpos = scanToken(currpos);
            count++;
        }
        return count;
    }
}

/*
 * rocq-jvm model of java.util.StringJoiner (clean-room, Apache-2.0), from the Javadoc: elements
 * are converted with String.valueOf when added; toString is prefix + elements separated by the
 * delimiter + suffix, or the empty value when one was set and nothing was added; merge adds the
 * other joiner's elements (joined with the other's delimiter) as one element; length is the
 * length of toString. Null constructor/setEmptyValue arguments throw NullPointerException with the
 * documented messages (checked in the order prefix, delimiter, suffix).
 * A total length beyond int range (OutOfMemoryError in the JDK) is STUCK.
 */
package java.util;

public final class StringJoiner {
    private final String prefix;
    private final String delimiter;
    private final String suffix;
    private String[] elts;
    private int size;
    private int len;
    private String emptyValue;

    public StringJoiner(CharSequence delimiter) {
        this(delimiter, "", "");
    }

    public StringJoiner(CharSequence delimiter, CharSequence prefix, CharSequence suffix) {
        if (prefix == null) throw new NullPointerException("The prefix must not be null");
        if (delimiter == null) throw new NullPointerException("The delimiter must not be null");
        if (suffix == null) throw new NullPointerException("The suffix must not be null");
        this.prefix = prefix.toString();
        this.delimiter = delimiter.toString();
        this.suffix = suffix.toString();
        checkLength(0, 0);
    }

    public StringJoiner setEmptyValue(CharSequence emptyValue) {
        if (emptyValue == null) throw new NullPointerException("The empty value must not be null");
        this.emptyValue = emptyValue.toString();
        return this;
    }

    private static String join(String pre, String suf, String delim, String[] es, int n) {
        StringBuilder b = new StringBuilder(pre);
        for (int i = 0; i < n; i++) {
            if (i > 0) b.append(delim);
            b.append(es[i]);
        }
        return b.append(suf).toString();
    }

    @Override
    public String toString() {
        if (size == 0 && emptyValue != null) return emptyValue;
        return join(prefix, suffix, delimiter, elts, size);
    }

    public StringJoiner add(CharSequence newElement) {
        String elt = String.valueOf(newElement);
        if (elts == null) {
            elts = new String[8];
        } else {
            if (size == elts.length) {
                String[] n = new String[2 * size];
                for (int i = 0; i < size; i++) n[i] = elts[i];
                elts = n;
            }
            len = checkLength(len, delimiter.length());
        }
        len = checkLength(len, elt.length());
        elts[size++] = elt;
        return this;
    }

    private int checkLength(int oldLen, int inc) {
        long newLen = (long) oldLen + (long) inc;
        long tmpLen = newLen + (long) prefix.length() + (long) suffix.length();
        if (tmpLen != (int) tmpLen) throw ModelStuck.unsupported("StringJoiner: length beyond int range");
        return (int) newLen;
    }

    public StringJoiner merge(StringJoiner other) {
        if (other == null) throw new NullPointerException();
        if (other.size == 0) return this;
        other.compact();
        return add(other.elts[0]);
    }

    private void compact() {
        int sz = size;
        if (sz > 1) {
            elts[0] = join("", "", delimiter, elts, sz);
            for (int i = 1; i < sz; i++) elts[i] = null;
            size = 1;
        }
    }

    public int length() {
        return (size == 0 && emptyValue != null) ? emptyValue.length() : len + prefix.length() + suffix.length();
    }
}

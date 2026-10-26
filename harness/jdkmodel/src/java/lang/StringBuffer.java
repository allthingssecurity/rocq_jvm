/*
 * rocq-jvm model of java.lang.StringBuffer (clean-room, Apache-2.0), from the Javadoc: the
 * synchronized twin of StringBuilder. Every operation is the StringBuilder operation of the model
 * (theories/Jdk/Jdk.v sb_model) on a private StringBuilder, under this object's monitor, so the
 * results and exception messages are StringBuilder's (the JDK shares AbstractStringBuilder).
 * A StringBuffer or StringBuilder argument is read through its contents, as the JDK does.
 * Differences that are STUCK: capacity(), chars()/codePoints() streams, repeat. The superclass is
 * java.lang.Object here (the JDK's is the package-private AbstractStringBuilder); Class.getSuperclass
 * of StringBuffer is STUCK in the model.
 */
package java.lang;

public final class StringBuffer implements java.io.Serializable, Comparable<StringBuffer>, CharSequence, Appendable {
    private static final long serialVersionUID = 3388685877147921107L;

    private final StringBuilder sb;

    public StringBuffer() {
        sb = new StringBuilder();
    }

    public StringBuffer(int capacity) {
        sb = new StringBuilder(capacity);
    }

    public StringBuffer(String str) {
        sb = new StringBuilder(str);
    }

    public StringBuffer(CharSequence seq) {
        if (seq == null) throw new NullPointerException("Cannot invoke \"java.lang.CharSequence.length()\" because \"seq\" is null");
        sb = new StringBuilder(contents(seq));
    }

    /** The text of a String, StringBuilder or StringBuffer; other CharSequences are read by the JDK
     *  through length()/charAt() calls, which the model does not reproduce. */
    private static String contents(CharSequence s) {
        if (s instanceof String || s instanceof StringBuilder || s instanceof StringBuffer) return s.toString();
        throw ModelStuckLang.unsupported("StringBuffer: a CharSequence other than String/StringBuilder/StringBuffer");
    }

    public synchronized int compareTo(StringBuffer another) {
        if (another == null) throw new NullPointerException("Cannot read field \"value\" because \"another\" is null");
        return sb.toString().compareTo(another.toString());
    }

    public synchronized int length() {
        return sb.length();
    }

    public synchronized int capacity() {
        throw ModelStuckLang.unsupported("StringBuffer.capacity");
    }

    public synchronized void ensureCapacity(int minimumCapacity) {
        sb.ensureCapacity(minimumCapacity);
    }

    public synchronized void trimToSize() {
        sb.trimToSize();
    }

    public synchronized void setLength(int newLength) {
        sb.setLength(newLength);
    }

    public synchronized char charAt(int index) {
        return sb.charAt(index);
    }

    public synchronized int codePointAt(int index) {
        return sb.codePointAt(index);
    }

    public synchronized int codePointBefore(int index) {
        return sb.codePointBefore(index);
    }

    public synchronized int codePointCount(int beginIndex, int endIndex) {
        return sb.codePointCount(beginIndex, endIndex);
    }

    public synchronized int offsetByCodePoints(int index, int codePointOffset) {
        return sb.offsetByCodePoints(index, codePointOffset);
    }

    public synchronized void getChars(int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        sb.getChars(srcBegin, srcEnd, dst, dstBegin);
    }

    public synchronized void setCharAt(int index, char ch) {
        sb.setCharAt(index, ch);
    }

    public synchronized StringBuffer append(Object obj) {
        sb.append(String.valueOf(obj));
        return this;
    }

    public synchronized StringBuffer append(String str) {
        sb.append(str);
        return this;
    }

    public synchronized StringBuffer append(StringBuffer s) {
        sb.append(s == null ? "null" : s.toString());
        return this;
    }

    public synchronized StringBuffer append(CharSequence s) {
        sb.append(s == null ? "null" : contents(s));
        return this;
    }

    public synchronized StringBuffer append(CharSequence s, int start, int end) {
        if (s == null) s = "null";
        if (start < 0 || start > end || end > s.length())
            throw new IndexOutOfBoundsException("Range [" + start + ", " + end + ") out of bounds for length " + s.length());
        sb.append(contents(s), start, end);
        return this;
    }

    public synchronized StringBuffer append(char[] str) {
        sb.append(str);
        return this;
    }

    public synchronized StringBuffer append(char[] str, int offset, int len) {
        sb.append(str, offset, len);
        return this;
    }

    public synchronized StringBuffer append(boolean b) {
        sb.append(b);
        return this;
    }

    public synchronized StringBuffer append(char c) {
        sb.append(c);
        return this;
    }

    public synchronized StringBuffer append(int i) {
        sb.append(i);
        return this;
    }

    public synchronized StringBuffer appendCodePoint(int codePoint) {
        sb.appendCodePoint(codePoint);
        return this;
    }

    public synchronized StringBuffer append(long lng) {
        sb.append(lng);
        return this;
    }

    public synchronized StringBuffer append(float f) {
        sb.append(f);
        return this;
    }

    public synchronized StringBuffer append(double d) {
        sb.append(d);
        return this;
    }

    public synchronized StringBuffer delete(int start, int end) {
        sb.delete(start, end);
        return this;
    }

    public synchronized StringBuffer deleteCharAt(int index) {
        sb.deleteCharAt(index);
        return this;
    }

    public synchronized StringBuffer replace(int start, int end, String str) {
        sb.replace(start, end, str);
        return this;
    }

    public synchronized String substring(int start) {
        return sb.substring(start);
    }

    public synchronized CharSequence subSequence(int start, int end) {
        return sb.substring(start, end);
    }

    public synchronized String substring(int start, int end) {
        return sb.substring(start, end);
    }

    public synchronized StringBuffer insert(int index, char[] str, int offset, int len) {
        sb.insert(index, str, offset, len);
        return this;
    }

    public synchronized StringBuffer insert(int offset, Object obj) {
        sb.insert(offset, String.valueOf(obj));
        return this;
    }

    public synchronized StringBuffer insert(int offset, String str) {
        sb.insert(offset, str);
        return this;
    }

    public synchronized StringBuffer insert(int offset, char[] str) {
        sb.insert(offset, str);
        return this;
    }

    public StringBuffer insert(int dstOffset, CharSequence s) {
        synchronized (this) {
            sb.insert(dstOffset, s == null ? "null" : contents(s));
        }
        return this;
    }

    public synchronized StringBuffer insert(int dstOffset, CharSequence s, int start, int end) {
        sb.insert(dstOffset, s == null ? "null" : contents(s), start, end);
        return this;
    }

    public StringBuffer insert(int offset, boolean b) {
        synchronized (this) {
            sb.insert(offset, b);
        }
        return this;
    }

    public synchronized StringBuffer insert(int offset, char c) {
        sb.insert(offset, c);
        return this;
    }

    public StringBuffer insert(int offset, int i) {
        synchronized (this) {
            sb.insert(offset, i);
        }
        return this;
    }

    public StringBuffer insert(int offset, long l) {
        synchronized (this) {
            sb.insert(offset, l);
        }
        return this;
    }

    public StringBuffer insert(int offset, float f) {
        synchronized (this) {
            sb.insert(offset, f);
        }
        return this;
    }

    public StringBuffer insert(int offset, double d) {
        synchronized (this) {
            sb.insert(offset, d);
        }
        return this;
    }

    public int indexOf(String str) {
        return indexOf(str, 0);
    }

    public synchronized int indexOf(String str, int fromIndex) {
        return sb.indexOf(str, fromIndex);
    }

    public int lastIndexOf(String str) {
        return lastIndexOf(str, length());
    }

    public synchronized int lastIndexOf(String str, int fromIndex) {
        return sb.lastIndexOf(str, fromIndex);
    }

    public synchronized StringBuffer reverse() {
        sb.reverse();
        return this;
    }

    public synchronized StringBuffer repeat(int codePoint, int count) {
        throw ModelStuckLang.unsupported("StringBuffer.repeat");
    }

    public synchronized StringBuffer repeat(CharSequence cs, int count) {
        throw ModelStuckLang.unsupported("StringBuffer.repeat");
    }

    public synchronized String toString() {
        return sb.toString();
    }

    public java.util.stream.IntStream chars() {
        throw ModelStuckLang.unsupported("StringBuffer.chars");
    }

    public java.util.stream.IntStream codePoints() {
        throw ModelStuckLang.unsupported("StringBuffer.codePoints");
    }
}

/*
 * rocq-jvm model of java.util.Properties (clean-room, Apache-2.0): the map part.
 *
 * As in the JDK (9+), a Properties object does not use the table of its Hashtable superclass:
 * the mappings live in an internal ConcurrentHashMap (so iteration order, toString, equals and
 * hashCode are those of the ConcurrentHashMap model), the views are synchronized on the
 * Properties object, getProperty falls back to the defaults, propertyNames() collects the names
 * (defaults first) into a Hashtable and returns its keys(), stringPropertyNames() collects the
 * String-valued names into a HashMap and returns its unmodifiable key set.
 * load(Reader) / load(InputStream) parse as the JDK's LineReader and loadConvert (ISO-8859-1 bytes, read in
 * chunks of 8192), with its \\uxxxx error.
 * Not modelled (STUCK): store/save (they write the current date), loadFromXML, storeToXML, list,
 * serialization.
 */
package java.util;

import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

public class Properties extends Hashtable<Object, Object> {
    protected volatile Properties defaults;

    private transient volatile ConcurrentHashMap<Object, Object> map;

    public Properties() {
        this(null, 8);
    }

    public Properties(int initialCapacity) {
        this(null, initialCapacity);
    }

    public Properties(Properties defaults) {
        this(defaults, 8);
    }

    private Properties(Properties defaults, int initialCapacity) {
        super((Void) null);
        map = new ConcurrentHashMap<>(initialCapacity);
        this.defaults = defaults;
    }

    public synchronized Object setProperty(String key, String value) {
        return put(key, value);
    }

    public synchronized void load(java.io.Reader reader) throws java.io.IOException {
        if (reader == null) throw new NullPointerException("reader parameter is null");
        load0(new LineReader(reader));
    }

    public synchronized void load(java.io.InputStream inStream) throws java.io.IOException {
        if (inStream == null) throw new NullPointerException("inStream parameter is null");
        load0(new LineReader(inStream));
    }

    /** The JDK's parse of the logical lines: key up to an unescaped '=', ':' or white space; one
     *  separator and the white space around it skipped; both converted by loadConvert. */
    private void load0(LineReader lr) throws java.io.IOException {
        StringBuilder outBuffer = new StringBuilder();
        int limit;
        while ((limit = lr.readLine()) >= 0) {
            int keyLen = 0;
            int valueStart = limit;
            boolean hasSep = false;
            boolean precedingBackslash = false;
            while (keyLen < limit) {
                char c = lr.lineBuf[keyLen];
                if ((c == '=' || c == ':') && !precedingBackslash) {
                    valueStart = keyLen + 1;
                    hasSep = true;
                    break;
                } else if ((c == ' ' || c == '\t' || c == '\f') && !precedingBackslash) {
                    valueStart = keyLen + 1;
                    break;
                }
                precedingBackslash = (c == '\\') ? !precedingBackslash : false;
                keyLen++;
            }
            while (valueStart < limit) {
                char c = lr.lineBuf[valueStart];
                if (c != ' ' && c != '\t' && c != '\f') {
                    if (!hasSep && (c == '=' || c == ':')) hasSep = true;
                    else break;
                }
                valueStart++;
            }
            String key = loadConvert(lr.lineBuf, 0, keyLen, outBuffer);
            String value = loadConvert(lr.lineBuf, valueStart, limit - valueStart, outBuffer);
            put(key, value);
        }
    }

    /** A logical line of the input (comment lines and blank lines skipped, continuation lines
     *  joined), read in chunks of 8192 bytes or chars as the JDK reads them. */
    private static final class LineReader {
        char[] lineBuf = new char[1024];
        private byte[] inByteBuf;
        private char[] inCharBuf;
        private int inLimit = 0;
        private int inOff = 0;
        private java.io.InputStream inStream;
        private java.io.Reader reader;

        LineReader(java.io.InputStream inStream) {
            this.inStream = inStream;
            inByteBuf = new byte[8192];
        }

        LineReader(java.io.Reader reader) {
            this.reader = reader;
            inCharBuf = new char[8192];
        }

        private int fill() throws java.io.IOException {
            return inStream != null ? inStream.read(inByteBuf) : reader.read(inCharBuf);
        }

        private char at(int i) {
            return inStream != null ? (char) (inByteBuf[i] & 0xFF) : inCharBuf[i];
        }

        int readLine() throws java.io.IOException {
            int len = 0;
            int off = inOff;
            int limit = inLimit;
            boolean skipWhiteSpace = true;
            boolean appendedLineBegin = false;
            boolean precedingBackslash = false;
            char c;
            while (true) {
                if (off >= limit) {
                    inLimit = limit = fill();
                    if (limit <= 0) {
                        if (len == 0) return -1;
                        return precedingBackslash ? len - 1 : len;
                    }
                    off = 0;
                }
                c = at(off++);
                if (skipWhiteSpace) {
                    if (c == ' ' || c == '\t' || c == '\f') continue;
                    if (!appendedLineBegin && (c == '\r' || c == '\n')) continue;
                    skipWhiteSpace = false;
                    appendedLineBegin = false;
                }
                if (len == 0) {
                    if (c == '#' || c == '!') {
                        commentLoop:
                        while (true) {
                            while (off < limit) {
                                char d = at(off++);
                                if (d == '\r' || d == '\n') break commentLoop;
                            }
                            if (off == limit) {
                                inLimit = limit = fill();
                                if (limit <= 0) return -1;
                                off = 0;
                            }
                        }
                        skipWhiteSpace = true;
                        continue;
                    }
                }
                if (c != '\n' && c != '\r') {
                    lineBuf[len++] = c;
                    if (len == lineBuf.length) {
                        char[] nb = new char[len * 2];
                        System.arraycopy(lineBuf, 0, nb, 0, len);
                        lineBuf = nb;
                    }
                    precedingBackslash = (c == '\\') ? !precedingBackslash : false;
                } else {
                    if (len == 0) {
                        skipWhiteSpace = true;
                        continue;
                    }
                    if (off >= limit) {
                        inLimit = limit = fill();
                        off = 0;
                        if (limit <= 0) return precedingBackslash ? len - 1 : len;
                    }
                    if (precedingBackslash) {
                        len -= 1;
                        skipWhiteSpace = true;
                        appendedLineBegin = true;
                        precedingBackslash = false;
                        if (c == '\r' && at(off) == '\n') off++;
                    } else {
                        inOff = off;
                        return len;
                    }
                }
            }
        }
    }

    /** Escapes: \\uxxxx ("Malformed \\uxxxx encoding."), \\t \\r \\n \\f, any other char after a backslash
     *  stands for itself. */
    private String loadConvert(char[] in, int off, int len, StringBuilder out) {
        int end = off + len;
        int start = off;
        while (off < end) {
            if (in[off++] == '\\') break;
        }
        if (off == end) return new String(in, start, len);
        out.setLength(0);
        off--;
        out.append(in, start, off - start);
        while (off < end) {
            char aChar = in[off++];
            if (aChar == '\\') {
                aChar = in[off++];
                if (aChar == 'u') {
                    if (off > end - 4) throw new IllegalArgumentException("Malformed \\uxxxx encoding.");
                    int value = 0;
                    for (int i = 0; i < 4; i++) {
                        aChar = in[off++];
                        if (aChar >= '0' && aChar <= '9') value = (value << 4) + aChar - '0';
                        else if (aChar >= 'a' && aChar <= 'f') value = (value << 4) + 10 + aChar - 'a';
                        else if (aChar >= 'A' && aChar <= 'F') value = (value << 4) + 10 + aChar - 'A';
                        else throw new IllegalArgumentException("Malformed \\uxxxx encoding.");
                    }
                    out.append((char) value);
                } else {
                    if (aChar == 't') aChar = '\t';
                    else if (aChar == 'r') aChar = '\r';
                    else if (aChar == 'n') aChar = '\n';
                    else if (aChar == 'f') aChar = '\f';
                    out.append(aChar);
                }
            } else {
                out.append(aChar);
            }
        }
        return out.toString();
    }

    @Deprecated
    public void save(java.io.OutputStream out, String comments) {
        throw ModelStuck.unsupported("Properties.save");
    }

    public void store(java.io.Writer writer, String comments) throws java.io.IOException {
        throw ModelStuck.unsupported("Properties.store");
    }

    public void store(java.io.OutputStream out, String comments) throws java.io.IOException {
        throw ModelStuck.unsupported("Properties.store");
    }

    public synchronized void loadFromXML(java.io.InputStream in) throws java.io.IOException {
        throw ModelStuck.unsupported("Properties.loadFromXML");
    }

    public void storeToXML(java.io.OutputStream os, String comment) throws java.io.IOException {
        throw ModelStuck.unsupported("Properties.storeToXML");
    }

    public void storeToXML(java.io.OutputStream os, String comment, String encoding) throws java.io.IOException {
        throw ModelStuck.unsupported("Properties.storeToXML");
    }

    public void storeToXML(java.io.OutputStream os, String comment, java.nio.charset.Charset charset) throws java.io.IOException {
        throw ModelStuck.unsupported("Properties.storeToXML");
    }

    public String getProperty(String key) {
        Object oval = map.get(nk(key));
        String sval = (oval instanceof String) ? (String) oval : null;
        Properties defaults;
        return ((sval == null) && ((defaults = this.defaults) != null)) ? defaults.getProperty(key) : sval;
    }

    public String getProperty(String key, String defaultValue) {
        String val = getProperty(key);
        return (val == null) ? defaultValue : val;
    }

    public Enumeration<?> propertyNames() {
        Hashtable<String, Object> h = new Hashtable<>();
        enumerate(h);
        return h.keys();
    }

    public Set<String> stringPropertyNames() {
        Map<String, String> h = new HashMap<>();
        enumerateStringProperties(h);
        return Collections.unmodifiableSet(h.keySet());
    }

    public void list(java.io.PrintStream out) {
        throw ModelStuck.unsupported("Properties.list");
    }

    public void list(java.io.PrintWriter out) {
        throw ModelStuck.unsupported("Properties.list");
    }

    /** Defaults first; a key that is not a String: the JDK's cast fails. */
    private void enumerate(Map<String, Object> h) {
        if (defaults != null) defaults.enumerate(h);
        for (Map.Entry<Object, Object> e : entrySet()) {
            Object k = e.getKey();
            if (!(k instanceof String)) throw TreeMap.castFail(k, "java.lang.String");
            h.put((String) k, e.getValue());
        }
    }

    private void enumerateStringProperties(Map<String, String> h) {
        if (defaults != null) defaults.enumerateStringProperties(h);
        for (Map.Entry<Object, Object> e : entrySet()) {
            Object k = e.getKey();
            Object v = e.getValue();
            if (k instanceof String && v instanceof String) h.put((String) k, (String) v);
        }
    }

    public int size() {
        return map.size();
    }

    public boolean isEmpty() {
        return map.isEmpty();
    }

    public Enumeration<Object> keys() {
        return Hashtable.enumeration(map.keySet());
    }

    public Enumeration<Object> elements() {
        return Hashtable.enumeration(map.values());
    }

    public boolean contains(Object value) {
        return map.contains(value);
    }

    public boolean containsValue(Object value) {
        return map.containsValue(value);
    }

    public boolean containsKey(Object key) {
        return map.containsKey(nk(key));
    }

    public Object get(Object key) {
        return map.get(nk(key));
    }

    /** The ConcurrentHashMap's key.hashCode() on a null key, with HotSpot's message. */
    private static Object nk(Object key) {
        if (key == null) throw TreeMap.invokeOnNull("Object.hashCode()", "key");
        return key;
    }

    public synchronized Object put(Object key, Object value) {
        return map.put(key, value);
    }

    public synchronized Object remove(Object key) {
        return map.remove(nk(key));
    }

    public synchronized void putAll(Map<?, ?> t) {
        map.putAll(t);
    }

    public synchronized void clear() {
        map.clear();
    }

    public synchronized String toString() {
        return map.toString();
    }

    public Set<Object> keySet() {
        return new SyncSet<>(map.keySet(), this);
    }

    public Collection<Object> values() {
        return new SyncCollection<>(map.values(), this);
    }

    public Set<Map.Entry<Object, Object>> entrySet() {
        return new SyncSet<>(new EntrySet(map.entrySet()), this);
    }

    /** The entry set of the map, without add/addAll. */
    private static class EntrySet implements Set<Map.Entry<Object, Object>> {
        private Set<Map.Entry<Object, Object>> entrySet;

        private EntrySet(Set<Map.Entry<Object, Object>> entrySet) {
            this.entrySet = entrySet;
        }

        public int size() {
            return entrySet.size();
        }

        public boolean isEmpty() {
            return entrySet.isEmpty();
        }

        public boolean contains(Object o) {
            return entrySet.contains(o);
        }

        public Object[] toArray() {
            return entrySet.toArray();
        }

        public <T> T[] toArray(T[] a) {
            return entrySet.toArray(a);
        }

        public void clear() {
            entrySet.clear();
        }

        public boolean remove(Object o) {
            return entrySet.remove(o);
        }

        public boolean add(Map.Entry<Object, Object> e) {
            throw new UnsupportedOperationException();
        }

        public boolean addAll(Collection<? extends Map.Entry<Object, Object>> c) {
            throw new UnsupportedOperationException();
        }

        public boolean containsAll(Collection<?> c) {
            return entrySet.containsAll(c);
        }

        public boolean equals(Object o) {
            return o == this || entrySet.equals(o);
        }

        public int hashCode() {
            return entrySet.hashCode();
        }

        public String toString() {
            return entrySet.toString();
        }

        public boolean removeAll(Collection<?> c) {
            return entrySet.removeAll(c);
        }

        public boolean retainAll(Collection<?> c) {
            return entrySet.retainAll(c);
        }

        public Iterator<Map.Entry<Object, Object>> iterator() {
            return entrySet.iterator();
        }

        public java.util.stream.Stream<Map.Entry<Object, Object>> stream() {
            throw ModelStuck.unsupported("Properties entry set: stream");
        }
    }

    public synchronized boolean equals(Object o) {
        return map.equals(o);
    }

    public synchronized int hashCode() {
        return map.hashCode();
    }

    public Object getOrDefault(Object key, Object defaultValue) {
        return map.getOrDefault(nk(key), defaultValue);
    }

    public synchronized void forEach(BiConsumer<? super Object, ? super Object> action) {
        map.forEach(action);
    }

    public synchronized void replaceAll(BiFunction<? super Object, ? super Object, ?> function) {
        map.replaceAll(function);
    }

    public synchronized Object putIfAbsent(Object key, Object value) {
        return map.putIfAbsent(key, value);
    }

    public synchronized boolean remove(Object key, Object value) {
        return map.remove(key, value);
    }

    public synchronized boolean replace(Object key, Object oldValue, Object newValue) {
        return map.replace(key, oldValue, newValue);
    }

    public synchronized Object replace(Object key, Object value) {
        return map.replace(key, value);
    }

    public synchronized Object computeIfAbsent(Object key, Function<? super Object, ?> mappingFunction) {
        return map.computeIfAbsent(key, mappingFunction);
    }

    public synchronized Object computeIfPresent(Object key, BiFunction<? super Object, ? super Object, ?> remappingFunction) {
        return map.computeIfPresent(key, remappingFunction);
    }

    public synchronized Object compute(Object key, BiFunction<? super Object, ? super Object, ?> remappingFunction) {
        return map.compute(key, remappingFunction);
    }

    public synchronized Object merge(Object key, Object value, BiFunction<? super Object, ? super Object, ?> remappingFunction) {
        return map.merge(key, value, remappingFunction);
    }

    protected void rehash() {
    }

    public synchronized Object clone() {
        Properties clone = (Properties) cloneHashtable();
        clone.map = new ConcurrentHashMap<>(map);
        return clone;
    }
}

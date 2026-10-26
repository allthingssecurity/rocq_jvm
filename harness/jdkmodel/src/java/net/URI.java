/*
 * rocq-jvm model of java.net.URI (clean-room, Apache-2.0), from the Javadoc (RFC 2396 with the
 * RFC 2732 IPv6 literals and the documented deviations: empty authority before a non-empty path,
 * query or fragment, empty relative paths, IPv6 scope ids) and JDK 21's observable behaviour:
 * - parsing as JDK 21 does it: the same scan order, hence the same URISyntaxException reason and
 *   index ("Illegal character in path at index 1: a b", "Expected authority at index 2: //", ...);
 *   a server-based authority is tried first and the authority falls back to a registry name (getHost
 *   null) unless a server authority is required (the 7-argument constructor, parseServerAuthority);
 *   ports beyond int range ("Malformed port number"), IPv4 bytes of at most 3 significant digits and
 *   at most 255, IPv6 addresses of 16 bytes (or fewer with "::"), scope ids;
 * - the multi-argument constructors quote the characters each component does not allow (%XX of the
 *   UTF-8 bytes for ASCII; non-ASCII space and control characters are escaped, other non-ASCII
 *   characters stay), JDK 21's quirk included that an opaque part beginning with "//[" but with no
 *   ']' or no ':' is dropped;
 * - getters (raw and decoded: %XX runs are decoded as UTF-8 with U+FFFD for malformed input, as
 *   new String(bytes, UTF_8) does; '%' inside [...] stays in getAuthority/getPath/getSchemeSpecificPart),
 *   normalize/resolve/relativize (RFC 2396 5.2 with JDK 21's leading "./" before a segment with ':'),
 *   equals/hashCode/compareTo (case-insensitive scheme and host, %XX compared case-insensitively),
 *   toString (the parsed string itself) and URI.create (IllegalArgumentException with the cause).
 * - toASCIIString escapes the UTF-8 bytes of non-ASCII characters after Unicode NFC normalization:
 *   only text whose non-ASCII characters are NFC-stable is modelled (below U+0300, Cyrillic U+0400-0482,
 *   currency symbols, CJK U+4E00-9FFF, Hangul syllables, Linear B, emoji U+1F300-1FAFF; checked against
 *   java.text.Normalizer); other non-ASCII text is STUCK. A lone surrogate gives JDK 21's
 *   NullPointerException (its encoder reports the error and the result buffer stays null).
 * - Character.isSpaceChar (which decides whether a non-ASCII character may appear unescaped) is
 *   written out for JDK 21 (Unicode 15.0 Zs/Zl/Zp: U+0020, U+00A0, U+1680, U+2000-200A, U+2028,
 *   U+2029, U+202F, U+205F, U+3000), independent of the Unicode tables given to the machine.
 * STUCK: toURL, serialization; the helpful NullPointerException messages of JDK 21 are thrown
 * explicitly where the JDK has them (null argument of the constructor, create, resolve, relativize,
 * compareTo).
 */
package java.net;

import java.nio.charset.StandardCharsets;

public final class URI implements Comparable<URI>, java.io.Serializable {
    private static final long serialVersionUID = -6052424284110960213L;

    // [scheme:]scheme-specific-part[#fragment]; hierarchical: [//authority]path[?query];
    // server authority: [userInfo@]host[:port]
    private transient String scheme;
    private transient String fragment;
    private transient String authority;
    private transient String userInfo;
    private transient String host;
    private transient int port = -1;
    private transient String path;          // null: opaque
    private transient String query;
    private transient String schemeSpecificPart;
    private transient int hash;
    private transient String decodedUserInfo;
    private transient String decodedAuthority;
    private transient String decodedPath;
    private transient String decodedQuery;
    private transient String decodedFragment;
    private transient String decodedSchemeSpecificPart;
    private volatile String string;

    private URI() {
    }

    public URI(String str) throws URISyntaxException {
        if (str == null)
            throw new NullPointerException("Cannot invoke \"String.length()\" because \"this.input\" is null");
        new Parser(str).parse(false);
    }

    public URI(String scheme, String userInfo, String host, int port, String path, String query, String fragment)
            throws URISyntaxException {
        String s = build(scheme, null, null, userInfo, host, port, path, query, fragment);
        checkPath(s, scheme, path);
        new Parser(s).parse(true);
    }

    public URI(String scheme, String authority, String path, String query, String fragment) throws URISyntaxException {
        String s = build(scheme, null, authority, null, null, -1, path, query, fragment);
        checkPath(s, scheme, path);
        new Parser(s).parse(false);
    }

    public URI(String scheme, String host, String path, String fragment) throws URISyntaxException {
        this(scheme, null, host, -1, path, null, fragment);
    }

    public URI(String scheme, String ssp, String fragment) throws URISyntaxException {
        new Parser(build(scheme, ssp, null, null, null, -1, null, null, fragment)).parse(false);
    }

    public static URI create(String str) {
        try {
            return new URI(str);
        } catch (URISyntaxException x) {
            throw new IllegalArgumentException(x.getMessage(), x);
        }
    }

    public URI parseServerAuthority() throws URISyntaxException {
        if (host != null || authority == null) return this;
        new Parser(toString()).parse(true);
        return this;
    }

    public URI normalize() {
        if (path == null || path.isEmpty()) return this;
        String np = normalizePath(path);
        if (np == path) return this;
        URI v = new URI();
        v.scheme = scheme;
        v.fragment = fragment;
        v.authority = authority;
        v.userInfo = userInfo;
        v.host = host;
        v.port = port;
        v.path = np;
        v.query = query;
        return v;
    }

    public URI resolve(URI uri) {
        if (uri == null)
            throw new NullPointerException("Cannot invoke \"java.net.URI.isOpaque()\" because \"child\" is null");
        URI base = this, child = uri;
        if (child.path == null || base.path == null) return child;
        // a lone fragment refers to the base document
        if (child.scheme == null && child.authority == null && child.path.isEmpty() && child.fragment != null
                && child.query == null) {
            if (base.fragment != null && child.fragment.equals(base.fragment)) return base;
            URI r = new URI();
            r.scheme = base.scheme;
            r.authority = base.authority;
            r.userInfo = base.userInfo;
            r.host = base.host;
            r.port = base.port;
            r.path = base.path;
            r.fragment = child.fragment;
            r.query = base.query;
            return r;
        }
        if (child.scheme != null) return child;
        URI r = new URI();
        r.scheme = base.scheme;
        r.query = child.query;
        r.fragment = child.fragment;
        if (child.authority == null) {
            r.authority = base.authority;
            r.host = base.host;
            r.userInfo = base.userInfo;
            r.port = base.port;
            String cp = child.path;
            if (!cp.isEmpty() && cp.charAt(0) == '/') {
                r.path = child.path;
            } else {
                // merge with the base path up to its last '/', then remove dot segments
                int i = base.path.lastIndexOf('/');
                String merged = "";
                if (cp.isEmpty()) {
                    if (i >= 0) merged = base.path.substring(0, i + 1);
                } else if (i >= 0 || base.scheme == null) {
                    merged = base.path.substring(0, i + 1).concat(cp);
                } else {
                    merged = "/".concat(cp);
                }
                r.path = normalizePath(merged);
            }
        } else {
            r.authority = child.authority;
            r.host = child.host;
            r.userInfo = child.userInfo;
            r.port = child.port;
            r.path = child.path;
        }
        return r;
    }

    public URI resolve(String str) {
        return resolve(URI.create(str));
    }

    public URI relativize(URI uri) {
        if (uri == null)
            throw new NullPointerException("Cannot invoke \"java.net.URI.isOpaque()\" because \"child\" is null");
        URI base = this, child = uri;
        if (child.path == null || base.path == null) return child;
        if (!equalIgnoringCase(base.scheme, child.scheme) || !equal(base.authority, child.authority)) return child;
        String bp = normalizePath(base.path);
        String cp = normalizePath(child.path);
        if (!bp.equals(cp)) {
            if (!bp.endsWith("/")) bp = bp + "/";
            if (!cp.startsWith(bp)) return child;
        }
        URI v = new URI();
        v.path = cp.substring(bp.length());
        v.query = child.query;
        v.fragment = child.fragment;
        return v;
    }

    public URL toURL() throws MalformedURLException {
        throw ModelStuck.unsupported("URI.toURL (java.net.URL is not modelled)");
    }

    public String getScheme() {
        return scheme;
    }

    public boolean isAbsolute() {
        return scheme != null;
    }

    public boolean isOpaque() {
        return path == null;
    }

    public String getRawSchemeSpecificPart() {
        String part = schemeSpecificPart;
        if (part != null) return part;
        String s = string;
        if (s != null) {
            int start = scheme != null ? scheme.length() + 1 : 0;
            int end = s.length();
            if (fragment != null) end -= fragment.length() + 1;
            part = (path != null && path.length() == end - start) ? path : s.substring(start, end);
        } else {
            StringBuilder sb = new StringBuilder();
            appendSsp(sb, null, getAuthority(), getUserInfo(), host, port, getPath(), getQuery());
            part = sb.toString();
        }
        schemeSpecificPart = part;
        return part;
    }

    public String getSchemeSpecificPart() {
        String part = decodedSchemeSpecificPart;
        if (part == null) {
            part = decode(getRawSchemeSpecificPart(), true);
            decodedSchemeSpecificPart = part;
        }
        return part;
    }

    public String getRawAuthority() {
        return authority;
    }

    public String getAuthority() {
        String a = decodedAuthority;
        if (a == null && authority != null) {
            a = decode(authority, true);
            decodedAuthority = a;
        }
        return a;
    }

    public String getRawUserInfo() {
        return userInfo;
    }

    public String getUserInfo() {
        String u = decodedUserInfo;
        if (u == null && userInfo != null) {
            u = decode(userInfo, true);
            decodedUserInfo = u;
        }
        return u;
    }

    public String getHost() {
        return host;
    }

    public int getPort() {
        return port;
    }

    public String getRawPath() {
        return path;
    }

    public String getPath() {
        String d = decodedPath;
        if (d == null && path != null) {
            d = decode(path, true);
            decodedPath = d;
        }
        return d;
    }

    public String getRawQuery() {
        return query;
    }

    public String getQuery() {
        String d = decodedQuery;
        if (d == null && query != null) {
            d = decode(query, false);
            decodedQuery = d;
        }
        return d;
    }

    public String getRawFragment() {
        return fragment;
    }

    public String getFragment() {
        String d = decodedFragment;
        if (d == null && fragment != null) {
            d = decode(fragment, false);
            decodedFragment = d;
        }
        return d;
    }

    public boolean equals(Object ob) {
        if (ob == this) return true;
        if (!(ob instanceof URI)) return false;
        URI that = (URI) ob;
        if ((this.path == null) != (that.path == null)) return false;
        if (!equalIgnoringCase(this.scheme, that.scheme)) return false;
        if (!equal(this.fragment, that.fragment)) return false;
        if (this.path == null) return equal(this.schemeSpecificPart, that.schemeSpecificPart);
        if (!equal(this.path, that.path)) return false;
        if (!equal(this.query, that.query)) return false;
        if (this.authority == that.authority) return true;
        if (this.host != null) {
            if (!equal(this.userInfo, that.userInfo)) return false;
            if (!equalIgnoringCase(this.host, that.host)) return false;
            if (this.port != that.port) return false;
        } else if (this.authority != null) {
            if (!equal(this.authority, that.authority)) return false;
        } else {
            return false;   // this.authority == null != that.authority
        }
        return true;
    }

    public int hashCode() {
        int h = hash;
        if (h == 0) {
            h = hashIgnoringCase(0, scheme);
            h = hashPart(h, fragment);
            if (path == null) {
                h = hashPart(h, schemeSpecificPart);
            } else {
                h = hashPart(h, path);
                h = hashPart(h, query);
                if (host != null) {
                    h = hashPart(h, userInfo);
                    h = hashIgnoringCase(h, host);
                    h += 1949 * port;
                } else {
                    h = hashPart(h, authority);
                }
            }
            if (h != 0) hash = h;
        }
        return h;
    }

    public int compareTo(URI that) {
        if (that == null)
            throw new NullPointerException("Cannot read field \"scheme\" because \"that\" is null");
        int c;
        if ((c = compareIgnoringCase(this.scheme, that.scheme)) != 0) return c;
        if (this.path == null) {
            if (that.path == null) {
                if ((c = compare(this.schemeSpecificPart, that.schemeSpecificPart)) != 0) return c;
                return compare(this.fragment, that.fragment);
            }
            return 1;
        } else if (that.path == null) {
            return -1;
        }
        if (this.host != null && that.host != null) {
            if ((c = compare(this.userInfo, that.userInfo)) != 0) return c;
            if ((c = compareIgnoringCase(this.host, that.host)) != 0) return c;
            if ((c = this.port - that.port) != 0) return c;
        } else {
            if ((c = compare(this.authority, that.authority)) != 0) return c;
        }
        if ((c = compare(this.path, that.path)) != 0) return c;
        if ((c = compare(this.query, that.query)) != 0) return c;
        return compare(this.fragment, that.fragment);
    }

    public String toString() {
        String s = string;
        if (s != null) return s;
        StringBuilder sb = new StringBuilder();
        if (scheme != null) sb.append(scheme).append(':');
        if (path == null) {
            sb.append(schemeSpecificPart);
        } else {
            if (host != null) {
                sb.append("//");
                if (userInfo != null) sb.append(userInfo).append('@');
                boolean br = host.indexOf(':') >= 0 && !host.startsWith("[") && !host.endsWith("]");
                if (br) sb.append('[');
                sb.append(host);
                if (br) sb.append(']');
                if (port != -1) sb.append(':').append(port);
            } else if (authority != null) {
                sb.append("//").append(authority);
            }
            sb.append(path);
            if (query != null) sb.append('?').append(query);
        }
        if (fragment != null) sb.append('#').append(fragment);
        s = sb.toString();
        string = s;
        return s;
    }

    public String toASCIIString() {
        return encodeNonAscii(toString());
    }

    // ---- comparison and hashing of components (ASCII case folding; %XX case-insensitive) ----

    private static int lower(char c) {
        return (c >= 'A' && c <= 'Z') ? c + 32 : c;
    }

    private static int upper(char c) {
        return (c >= 'a' && c <= 'z') ? c - 32 : c;
    }

    private static boolean equal(String s, String t) {
        return pctCompare(s, t, true) == 0;
    }

    private static int compare(String s, String t) {
        return pctCompare(s, t, false);
    }

    private static boolean equalIgnoringCase(String s, String t) {
        if (s == t) return true;
        if (s == null || t == null) return false;
        int n = s.length();
        if (t.length() != n) return false;
        for (int i = 0; i < n; i++)
            if (lower(s.charAt(i)) != lower(t.charAt(i))) return false;
        return true;
    }

    private static int hashPart(int h, String s) {
        if (s == null) return h;
        if (s.indexOf('%') < 0) return h * 127 + s.hashCode();
        int g = 0;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            g = 31 * g + c;
            if (c == '%') {
                g = 31 * g + upper(s.charAt(i + 1));
                g = 31 * g + upper(s.charAt(i + 2));
                i += 2;
            }
        }
        return h * 127 + g;
    }

    private static int hashIgnoringCase(int h, String s) {
        if (s == null) return h;
        for (int i = 0; i < s.length(); i++) h = 31 * h + lower(s.charAt(i));
        return h;
    }

    // s without '%': plain String.compareTo; otherwise the two hex digits after each '%' of s are
    // compared case-insensitively (equality first compares the lengths)
    private static int pctCompare(String s, String t, boolean eq) {
        if (s == t) return 0;
        if (s == null) return -1;
        if (t == null) return 1;
        if (s.indexOf('%') < 0) return s.compareTo(t);
        int sn = s.length(), tn = t.length();
        if (sn != tn && eq) return sn - tn;
        int n = Math.min(sn, tn);
        int i = 0;
        while (i < n) {
            char c = s.charAt(i), d = t.charAt(i);
            int v = c - d;
            if (c != '%') {
                if (v != 0) return v;
                i++;
                continue;
            }
            if (d != '%' && v != 0) return v;
            i++;
            v = lower(s.charAt(i)) - lower(t.charAt(i));
            if (v != 0) return v;
            i++;
            v = lower(s.charAt(i)) - lower(t.charAt(i));
            if (v != 0) return v;
            i++;
        }
        return sn - tn;
    }

    private static int compareIgnoringCase(String s, String t) {
        if (s == t) return 0;
        if (s == null) return -1;
        if (t == null) return 1;
        int sn = s.length(), tn = t.length();
        int n = sn < tn ? sn : tn;
        for (int i = 0; i < n; i++) {
            int c = lower(s.charAt(i)) - lower(t.charAt(i));
            if (c != 0) return c;
        }
        return sn - tn;
    }

    // ---- building the string of the multi-argument constructors ----

    private static void checkPath(String s, String scheme, String path) throws URISyntaxException {
        if (scheme != null && path != null && !path.isEmpty() && path.charAt(0) != '/')
            throw new URISyntaxException(s, "Relative path in absolute URI");
    }

    private static void appendAuthority(StringBuilder sb, String authority, String userInfo, String host, int port) {
        if (host != null) {
            sb.append("//");
            if (userInfo != null) sb.append(quote(userInfo, L_USERINFO, H_USERINFO)).append('@');
            boolean br = host.indexOf(':') >= 0 && !host.startsWith("[") && !host.endsWith("]");
            if (br) sb.append('[');
            sb.append(host);
            if (br) sb.append(']');
            if (port != -1) sb.append(':').append(port);
        } else if (authority != null) {
            sb.append("//");
            String rest = authority;
            if (authority.startsWith("[")) {
                int end = authority.indexOf(']');
                if (end != -1 && authority.indexOf(':') != -1) {
                    // a bracketed IPv6 literal is kept as it is
                    sb.append(authority, 0, end + 1);
                    rest = authority.substring(end + 1);
                }
            }
            sb.append(quote(rest, L_REG_NAME | L_SERVER, H_REG_NAME | H_SERVER));
        }
    }

    private static void appendSsp(StringBuilder sb, String opaque, String authority, String userInfo, String host,
                                  int port, String path, String query) {
        if (opaque != null) {
            if (opaque.startsWith("//[")) {
                int end = opaque.indexOf(']');
                if (end != -1 && opaque.indexOf(':') != -1) {
                    sb.append(opaque, 0, end + 1);
                    sb.append(quote(opaque.substring(end + 1), L_URIC, H_URIC));
                }
                // JDK 21: otherwise nothing is appended
            } else {
                sb.append(quote(opaque, L_URIC, H_URIC));
            }
        } else {
            appendAuthority(sb, authority, userInfo, host, port);
            if (path != null) sb.append(quote(path, L_PATH, H_PATH));
            if (query != null) sb.append('?').append(quote(query, L_URIC, H_URIC));
        }
    }

    private static String build(String scheme, String opaque, String authority, String userInfo, String host,
                                int port, String path, String query, String fragment) {
        StringBuilder sb = new StringBuilder();
        if (scheme != null) sb.append(scheme).append(':');
        appendSsp(sb, opaque, authority, userInfo, host, port, path, query);
        if (fragment != null) sb.append('#').append(quote(fragment, L_URIC, H_URIC));
        return sb.toString();
    }

    // ---- path normalization (RFC 2396 5.2 step 6 c-f; trailing slashes are kept) ----

    // Segments are the maximal runs of non-'/' characters after the leading slashes; a "." segment
    // goes, a ".." segment goes with the nearest preceding remaining segment unless that one is
    // "..". A segment keeps the '/' that followed it. A relative result whose first remaining segment
    // was not the first one and contains ':' gets a leading "./" (it would read as a scheme).
    private static String normalizePath(String ps) {
        int n = ps.length();
        int p = 0;
        while (p < n && ps.charAt(p) == '/') p++;
        boolean abs = p > 0;
        int max = (n - p) / 2 + 1;
        int[] st = new int[max];
        int[] en = new int[max];
        boolean[] slash = new boolean[max];
        boolean[] gone = new boolean[max];
        int ns = 0;
        while (p < n) {
            int q = p;
            while (q < n && ps.charAt(q) != '/') q++;
            st[ns] = p;
            en[ns] = q;
            slash[ns] = q < n;
            ns++;
            while (q < n && ps.charAt(q) == '/') q++;
            p = q;
        }
        for (int i = 0; i < ns; i++) {
            int len = en[i] - st[i];
            if (len == 1 && ps.charAt(st[i]) == '.') {
                gone[i] = true;
            } else if (len == 2 && ps.charAt(st[i]) == '.' && ps.charAt(st[i] + 1) == '.') {
                int j = i - 1;
                while (j >= 0 && gone[j]) j--;
                if (j >= 0 && !(en[j] - st[j] == 2 && ps.charAt(st[j]) == '.' && ps.charAt(st[j] + 1) == '.')) {
                    gone[i] = true;
                    gone[j] = true;
                }
            }
        }
        StringBuilder sb = new StringBuilder(n + 2);
        if (abs) sb.append('/');
        int f = 0;
        while (f < ns && gone[f]) f++;
        if (!abs && f > 0 && f < ns && ps.indexOf(':', st[f]) >= 0 && ps.indexOf(':', st[f]) < en[f])
            sb.append("./");
        for (int i = 0; i < ns; i++) {
            if (gone[i]) continue;
            sb.append(ps, st[i], en[i]);
            if (slash[i]) sb.append('/');
        }
        String s = sb.toString();
        return s.equals(ps) ? ps : s;
    }

    // ---- character classes (bit c of the 128-bit mask: character c is allowed; bit 0: %XX escapes
    // and visible non-ASCII characters are allowed) ----

    private static final long L_DIGIT = 0x3ff000000000000L, H_DIGIT = 0L;
    private static final long L_ALPHA = 0L, H_ALPHA = 0x7fffffe07fffffeL;
    private static final long L_ALPHANUM = 0x3ff000000000000L, H_ALPHANUM = 0x7fffffe07fffffeL;
    private static final long L_HEX = 0x3ff000000000000L, H_HEX = 0x7e0000007eL;
    private static final long L_DASH = 0x200000000000L;
    private static final long L_DOT = 0x400000000000L;
    private static final long L_ESCAPED = 1L;
    private static final long L_URIC = 0xafffffd200000001L, H_URIC = 0x47fffffeafffffffL;
    private static final long L_PATH = 0x2fffffd200000001L, H_PATH = 0x47fffffe87ffffffL;
    private static final long L_USERINFO = 0x2fff7fd200000001L, H_USERINFO = 0x47fffffe87fffffeL;
    private static final long L_REG_NAME = 0x2fff7fd200000001L, H_REG_NAME = 0x47fffffe87ffffffL;
    private static final long L_SERVER = 0x2fff7fd200000001L, H_SERVER = 0x47fffffeafffffffL;
    private static final long L_SERVER_PERCENT = 0x2fff7ff200000001L, H_SERVER_PERCENT = 0x47fffffeafffffffL;
    private static final long L_SCHEME = 0x3ff680000000000L, H_SCHEME = 0x7fffffe07fffffeL;
    private static final long L_SCOPE_ID = 0x3ff400000000000L, H_SCOPE_ID = 0x7fffffe87fffffeL;

    private static boolean match(char c, long lo, long hi) {
        if (c == 0) return false;
        if (c < 64) return ((1L << c) & lo) != 0;
        if (c < 128) return ((1L << (c - 64)) & hi) != 0;
        return false;
    }

    // ---- quoting, encoding, decoding ----

    private static final String HEXD = "0123456789ABCDEF";

    private static void appendEscape(StringBuilder sb, int b) {
        sb.append('%').append(HEXD.charAt((b >> 4) & 15)).append(HEXD.charAt(b & 15));
    }

    // UTF-8 of the code point; bytes >= 0x80 escaped
    private static void appendUtf8(StringBuilder sb, int cp) {
        if (cp < 0x80) {
            sb.append((char) cp);
        } else if (cp < 0x800) {
            appendEscape(sb, 0xC0 | (cp >> 6));
            appendEscape(sb, 0x80 | (cp & 63));
        } else if (cp < 0x10000) {
            appendEscape(sb, 0xE0 | (cp >> 12));
            appendEscape(sb, 0x80 | ((cp >> 6) & 63));
            appendEscape(sb, 0x80 | (cp & 63));
        } else {
            appendEscape(sb, 0xF0 | (cp >> 18));
            appendEscape(sb, 0x80 | ((cp >> 12) & 63));
            appendEscape(sb, 0x80 | ((cp >> 6) & 63));
            appendEscape(sb, 0x80 | (cp & 63));
        }
    }

    // Character.isSpaceChar of JDK 21 (Unicode 15.0 general categories Zs, Zl, Zp), written out so
    // that it does not depend on the Unicode tables given to the machine
    private static boolean isSpaceChar(char c) {
        return c == 0x20 || c == 0xA0 || c == 0x1680 || (c >= 0x2000 && c <= 0x200A) || c == 0x2028 || c == 0x2029
            || c == 0x202F || c == 0x205F || c == 0x3000;
    }

    private static String quote(String s, long lo, long hi) {
        StringBuilder sb = null;
        boolean nonAscii = (lo & L_ESCAPED) != 0;
        int n = s.length();
        for (int i = 0; i < n; i++) {
            char c = s.charAt(i);
            boolean esc;
            if (c < 0x80) esc = !match(c, lo, hi);
            else esc = nonAscii && (isSpaceChar(c) || Character.isISOControl(c));
            if (esc) {
                if (sb == null) {
                    sb = new StringBuilder();
                    sb.append(s, 0, i);
                }
                if (c < 0x80) appendEscape(sb, c);
                else appendUtf8(sb, c);   // a space or control character: never a surrogate
            } else if (sb != null) {
                sb.append(c);
            }
        }
        return sb == null ? s : sb.toString();
    }

    private static boolean nfcStable(int cp) {
        return cp < 0x300 || (cp >= 0x400 && cp <= 0x482) || (cp >= 0x20A0 && cp <= 0x20BF)
            || (cp >= 0x4E00 && cp <= 0x9FFF) || (cp >= 0xAC00 && cp <= 0xD7A3)
            || (cp >= 0x10000 && cp <= 0x1007F) || (cp >= 0x1F300 && cp <= 0x1FAFF);
    }

    private static String encodeNonAscii(String s) {
        int n = s.length();
        int i = 0;
        while (i < n && s.charAt(i) < 0x80) i++;
        if (i == n) return s;
        boolean stable = true;
        for (int k = i; k < n; k++) {
            char c = s.charAt(k);
            if (c < 0x80) continue;
            if (Character.isHighSurrogate(c) && k + 1 < n && Character.isLowSurrogate(s.charAt(k + 1))) {
                stable &= nfcStable(Character.toCodePoint(c, s.charAt(k + 1)));
                k++;
            } else if (Character.isHighSurrogate(c) || Character.isLowSurrogate(c)) {
                // JDK 21: the UTF-8 encoder reports the lone surrogate, the byte buffer stays null
                throw new NullPointerException("Cannot invoke \"java.nio.ByteBuffer.hasRemaining()\" because \"bb\" is null");
            } else {
                stable &= nfcStable(c);
            }
        }
        if (!stable) throw ModelStuck.unsupported("URI.toASCIIString: Unicode NFC normalization of non-ASCII text");
        StringBuilder sb = new StringBuilder(n + 16);
        for (int k = 0; k < n; k++) {
            char c = s.charAt(k);
            if (Character.isHighSurrogate(c)) {
                appendUtf8(sb, Character.toCodePoint(c, s.charAt(k + 1)));
                k++;
            } else {
                appendUtf8(sb, c);
            }
        }
        return sb.toString();
    }

    private static int hexValue(char c) {
        if (c >= '0' && c <= '9') return c - '0';
        if (c >= 'a' && c <= 'f') return c - 'a' + 10;
        if (c >= 'A' && c <= 'F') return c - 'A' + 10;
        return -1;
    }

    // every run of %XX escapes is decoded as UTF-8 (malformed input: U+FFFD); with inBrackets, a '%'
    // between '[' and ']' (an IPv6 scope id) stays
    private static String decode(String s, boolean inBrackets) {
        if (s == null) return s;
        int n = s.length();
        if (n == 0) return s;
        if (s.indexOf('%') < 0) return s;
        StringBuilder sb = new StringBuilder(n);
        byte[] buf = new byte[n];
        boolean br = false;
        int i = 0;
        while (i < n) {
            char c = s.charAt(i);
            if (c == '[') br = true;
            else if (br && c == ']') br = false;
            if (c != '%' || (br && inBrackets)) {
                sb.append(c);
                i++;
                continue;
            }
            int k = 0;
            do {
                int hi = hexValue(s.charAt(i + 1)) & 15;
                int lo = hexValue(s.charAt(i + 2)) & 15;
                buf[k++] = (byte) ((hi << 4) | lo);
                i += 3;
            } while (i < n && s.charAt(i) == '%');
            sb.append(new String(buf, 0, k, StandardCharsets.UTF_8));
        }
        return sb.toString();
    }

    // ---- the parser: fills in the fields of the enclosing URI ----

    private final class Parser {
        private final String in;
        private boolean rsa;       // a server-based authority is required
        private int v6bytes;

        Parser(String s) {
            in = s;
            string = s;
        }

        private void fail(String reason) throws URISyntaxException {
            throw new URISyntaxException(in, reason);
        }

        private void fail(String reason, int p) throws URISyntaxException {
            throw new URISyntaxException(in, reason, p);
        }

        private void failExpecting(String what, int p) throws URISyntaxException {
            fail("Expected " + what, p);
        }

        private boolean at(int p, int end, char c) {
            return p < end && in.charAt(p) == c;
        }

        private boolean at2(int p, int end, char c) {   // "cc" at p
            return end - p >= 2 && in.charAt(p) == c && in.charAt(p + 1) == c;
        }

        private int scanChar(int p, int end, char c) {
            return (p < end && in.charAt(p) == c) ? p + 1 : p;
        }

        // the first position in [p, end) holding a character of stop (or end); -1 if a character of
        // err comes first
        private int scanUntil(int p, int end, String err, String stop) {
            while (p < end) {
                char c = in.charAt(p);
                if (err.indexOf(c) >= 0) return -1;
                if (stop.indexOf(c) >= 0) break;
                p++;
            }
            return p;
        }

        private int scanStop(int p, int end, String stop) {
            while (p < end && stop.indexOf(in.charAt(p)) < 0) p++;
            return p;
        }

        private int scanEscape(int p, int end, char c) throws URISyntaxException {
            if (c == '%') {
                if (p + 3 <= end && match(in.charAt(p + 1), L_HEX, H_HEX) && match(in.charAt(p + 2), L_HEX, H_HEX))
                    return p + 3;
                fail("Malformed escape pair", p);
            } else if (c > 128 && !isSpaceChar(c) && !Character.isISOControl(c)) {
                return p + 1;
            }
            return p;
        }

        private int scan(int p, int end, long lo, long hi) throws URISyntaxException {
            while (p < end) {
                char c = in.charAt(p);
                if (match(c, lo, hi)) {
                    p++;
                    continue;
                }
                if ((lo & L_ESCAPED) != 0) {
                    int q = scanEscape(p, end, c);
                    if (q > p) {
                        p = q;
                        continue;
                    }
                }
                break;
            }
            return p;
        }

        private void checkChars(int p, int end, long lo, long hi, String what) throws URISyntaxException {
            int q = scan(p, end, lo, hi);
            if (q < end) fail("Illegal character in " + what, q);
        }

        void parse(boolean requireServer) throws URISyntaxException {
            rsa = requireServer;
            int n = in.length();
            int p = scanUntil(0, n, "/?#", ":");
            if (p >= 0 && at(p, n, ':')) {
                if (p == 0) failExpecting("scheme name", 0);
                checkChars(0, 1, L_ALPHA, H_ALPHA, "scheme name");
                checkChars(1, p, L_SCHEME, H_SCHEME, "scheme name");
                scheme = in.substring(0, p);
                p++;
                if (at(p, n, '/')) {
                    p = hierarchical(p, n);
                } else {
                    int q = scanStop(p, n, "#");
                    if (q <= p) failExpecting("scheme-specific part", p);
                    checkChars(p, q, L_URIC, H_URIC, "opaque part");
                    schemeSpecificPart = in.substring(p, q);
                    p = q;
                }
            } else {
                p = hierarchical(0, n);
            }
            if (at(p, n, '#')) {
                checkChars(p + 1, n, L_URIC, H_URIC, "fragment");
                fragment = in.substring(p + 1, n);
                p = n;
            }
            if (p < n) fail("end of URI", p);
        }

        private int hierarchical(int p, int n) throws URISyntaxException {
            if (at(p, n, '/') && at(p + 1, n, '/')) {
                p += 2;
                int q = scanStop(p, n, "/?#");
                if (q > p) p = authority(p, q);
                else if (q >= n) failExpecting("authority", p);
                // an empty authority before a path, query or fragment is allowed
            }
            int q = scanStop(p, n, "?#");
            checkChars(p, q, L_PATH, H_PATH, "path");
            path = in.substring(p, q);
            p = q;
            if (at(p, n, '?')) {
                p++;
                q = scanStop(p, n, "#");
                checkChars(p, q, L_URIC, H_URIC, "query");
                query = in.substring(p, q);
                p = q;
            }
            return p;
        }

        private int authority(int p, int n) throws URISyntaxException {
            int q = p;
            URISyntaxException ex = null;
            // JDK 21 allows '%' unescaped (an IPv6 scope id) unless the authority starts with ']'
            boolean serverChars = scanStop(p, n, "]") > p
                ? scan(p, n, L_SERVER_PERCENT, H_SERVER_PERCENT) == n
                : scan(p, n, L_SERVER, H_SERVER) == n;
            int qreg = scan(p, n, L_REG_NAME, H_REG_NAME);
            boolean regChars = qreg == n;
            if (regChars && !serverChars) {
                authority = in.substring(p, n);
                return n;
            }
            boolean skip = !rsa && regChars;
            if (serverChars) {
                try {
                    q = server(p, n, skip);
                    if (q < n) {
                        if (skip) {
                            userInfo = null;
                            host = null;
                            port = -1;
                            q = p;
                        } else {
                            failExpecting("end of authority", q);
                        }
                    } else {
                        authority = in.substring(p, n);
                    }
                } catch (URISyntaxException x) {
                    userInfo = null;
                    host = null;
                    port = -1;
                    if (rsa) throw x;
                    ex = x;
                    q = p;
                }
            }
            if (q < n) {
                if (regChars) authority = in.substring(p, n);
                else if (ex != null) throw ex;
                else fail("Illegal character in authority", serverChars ? q : qreg);
            }
            return n;
        }

        private int server(int p, int n, boolean skip) throws URISyntaxException {
            int q = scanUntil(p, n, "/?#", "@");
            if (q >= p && at(q, n, '@')) {
                checkChars(p, q, L_USERINFO, H_USERINFO, "user info");
                userInfo = in.substring(p, q);
                p = q + 1;
            }
            if (at(p, n, '[')) {
                p++;
                q = scanUntil(p, n, "/?#", "]");
                if (q > p && at(q, n, ']')) {
                    int r = scanStop(p, q, "%");
                    if (r > p) {
                        ipv6(p, r);
                        if (r + 1 == q) fail("scope id expected");
                        checkChars(r + 1, q, L_SCOPE_ID, H_SCOPE_ID, "scope id");
                    } else {
                        ipv6(p, q);
                    }
                    host = in.substring(p - 1, q + 1);
                    p = q + 1;
                } else {
                    failExpecting("closing bracket for IPv6 address", q);
                }
            } else {
                q = ipv4(p, n);
                if (q <= p) q = hostname(p, n, skip);
                p = q;
            }
            if (at(p, n, ':')) {
                p++;
                q = scanStop(p, n, "/");
                if (q > p) {
                    checkChars(p, q, L_DIGIT, H_DIGIT, "port number");
                    try {
                        port = Integer.parseInt(in, p, q, 10);
                    } catch (NumberFormatException x) {
                        fail("Malformed port number", p);
                    }
                    p = q;
                }
            } else if (p < n && skip) {
                return p;
            }
            if (p < n) failExpecting("port number", p);
            return p;
        }

        // decimal digits whose value fits in a byte (at most 3 significant digits, at most 255)
        private int scanByte(int p, int n) throws URISyntaxException {
            int q = scan(p, n, L_DIGIT, H_DIGIT);
            if (q <= p) return q;
            int i = p;
            while (i < q && in.charAt(i) == '0') i++;
            int sig = q - i;
            if (sig < 3) return q;
            if (sig > 3) return p;
            if (Integer.parseInt(in, p, q, 10) > 255) return p;
            return q;
        }

        // an IPv4 address at p within [p, n) (strict: exactly [p, n)); -1 if [p, n) does not start
        // with digits and dots
        private int scanIPv4(int p, int n, boolean strict) throws URISyntaxException {
            int m = scan(p, n, L_DIGIT | L_DOT, H_DIGIT);
            if (m <= p || (strict && m != n)) return -1;
            int q = p;
            for (int part = 0; ; part++) {
                if ((q = scanByte(p, m)) <= p) break;
                p = q;
                if (part == 3) {
                    if (q < m) break;
                    return q;
                }
                if ((q = scanChar(p, m, '.')) <= p) break;
                p = q;
            }
            if (strict) fail("Malformed IPv4 address", q);
            return -1;
        }

        private int takeIPv4(int p, int n, String expected) throws URISyntaxException {
            int q = scanIPv4(p, n, true);
            if (q <= p) failExpecting(expected, p);
            return q;
        }

        private int ipv4(int p, int n) {
            int q;
            try {
                q = scanIPv4(p, n, false);
            } catch (URISyntaxException | NumberFormatException x) {
                return -1;
            }
            if (q == -1) return q;
            if (q > p && q < n && in.charAt(q) != ':') return -1;
            if (q > p) host = in.substring(p, q);
            return q;
        }

        private int hostname(int start, int n, boolean skip) throws URISyntaxException {
            int p = start, q;
            int last = -1;   // start of the last label
            do {
                q = scan(p, n, L_ALPHANUM, H_ALPHANUM);
                if (q <= p) break;
                last = p;
                p = q;
                q = scan(p, n, L_ALPHANUM | L_DASH, H_ALPHANUM);
                if (q > p) {
                    if (in.charAt(q - 1) == '-') fail("Illegal character in hostname", q - 1);
                    p = q;
                }
                q = scanChar(p, n, '.');
                if (q <= p) break;
                p = q;
            } while (p < n);
            if (p < n && !at(p, n, ':')) {
                if (skip) return p;
                fail("Illegal character in hostname", p);
            }
            if (last < 0) failExpecting("hostname", start);
            if (last > start && !match(in.charAt(last), L_ALPHA, H_ALPHA)) fail("Illegal character in hostname", last);
            host = in.substring(start, p);
            return p;
        }

        private int ipv6(int start, int n) throws URISyntaxException {
            int p = start;
            boolean compressed = false;
            int q = hexSeq(p, n);
            if (q > p) {
                p = q;
                if (at2(p, n, ':')) {
                    compressed = true;
                    p = hexPost(p + 2, n);
                } else if (at(p, n, ':')) {
                    p = takeIPv4(p + 1, n, "IPv4 address");
                    v6bytes += 4;
                }
            } else if (at2(p, n, ':')) {
                compressed = true;
                p = hexPost(p + 2, n);
            }
            if (p < n) fail("Malformed IPv6 address", start);
            if (v6bytes > 16) fail("IPv6 address too long", start);
            if (!compressed && v6bytes < 16) fail("IPv6 address too short", start);
            if (compressed && v6bytes == 16) fail("Malformed IPv6 address", start);
            return p;
        }

        private int hexPost(int p, int n) throws URISyntaxException {
            if (p == n) return p;
            int q = hexSeq(p, n);
            if (q > p) {
                p = q;
                if (at(p, n, ':')) {
                    p = takeIPv4(p + 1, n, "hex digits or IPv4 address");
                    v6bytes += 4;
                }
            } else {
                p = takeIPv4(p, n, "hex digits or IPv4 address");
                v6bytes += 4;
            }
            return p;
        }

        // hex4 *(":" hex4), stopping before "::" and before a hex4 that starts an IPv4 address;
        // -1 if there is none
        private int hexSeq(int p, int n) throws URISyntaxException {
            int q = scan(p, n, L_HEX, H_HEX);
            if (q <= p) return -1;
            if (at(q, n, '.')) return -1;
            if (q > p + 4) fail("IPv6 hexadecimal digit sequence too long", p);
            v6bytes += 2;
            p = q;
            while (p < n) {
                if (!at(p, n, ':')) break;
                if (at(p + 1, n, ':')) break;
                p++;
                q = scan(p, n, L_HEX, H_HEX);
                if (q <= p) failExpecting("digits for an IPv6 address", p);
                if (at(q, n, '.')) {
                    p--;
                    break;
                }
                if (q > p + 4) fail("IPv6 hexadecimal digit sequence too long", p);
                v6bytes += 2;
                p = q;
            }
            return p;
        }
    }
}

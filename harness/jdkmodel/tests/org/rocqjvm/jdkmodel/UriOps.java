package org.rocqjvm.jdkmodel;

import java.net.URI;
import java.net.URISyntaxException;

/** Differential tests of java.net.URI: parsing (all getters, raw and decoded, or the
 *  URISyntaxException's reason, index and input), URI.create, the multi-argument constructors'
 *  quoting, normalize/resolve/relativize, equals/hashCode/compareTo, authorities (IPv4, IPv6 with
 *  scope ids, ports, registry names, parseServerAuthority) and toASCIIString / %XX decoding. */
public final class UriOps {
    private UriOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static String pick(String[] a) { return a[r(a.length)]; }

    static final String[] SCHEME = {"http:", "HTTP:", "file:", "s+1.-:", "mailto:", "urn:", "a:", "", "", "", "1s:", ":", "h_t:"};
    static final String[] USER = {"", "", "", "u@", "u:p@", "u%41@", "@", "u;x=1@", "a b@", "u%4@", "[u]@", "é@"};
    static final String[] HOST = {"example.com", "Example.COM", "a-b.c", "localhost", "1.2.3.4", "01.002.0003.4", "a.b.", "x9.y9",
        "[::1]", "[FE80::1%eth0]", "[1:2:3:4:5:6:7:8]", "[::ffff:1.2.3.4]", "", "a-.b", "-a", "a..b", "9a.b9", "a.9b", "256.1.1.1",
        "1.2.3", "1.2.3.4.5", "x_y", "[1:2:3:4:5:6:7]", "[12345::]", "[::1%]", "[g::]", "[1::2::3]", "[::1", "[1:2:3:4:5:6:7:8:9]",
        "[::1.2.3]", "[1:2:3:4:5:6:1.2.3.4]", "[]", "h%41", "[::1]x", "a]b"};
    static final String[] PORT = {"", "", "", ":80", ":8080", ":", ":0080", ":2147483647", ":2147483648", ":99999999999", ":-1", ":8a"};
    static final String[] PATH = {"/", "/a/b", "/a/b/", "", "a/b", "a", "/a/./b/../c", "./x:y", "../..", "/%41%7e", "/%e2%82%ac",
        "/%C3%A9", "/é", "//x", "a//b//", "/./", "x/../y:z/w", ".", "..", "/..", "a/b/../../..", "/a;p", "/%F0%9F%98%80",
        "/%C3", "/%ED%A0%80", "/%FF%41", "/a b", "/%zz", "/%4", "/[x]", "/\u00a0", "/\u0080", "/\u3000"};
    static final String[] QUERY = {"", "", "", "?q=1&r", "?", "?%41", "?[%41]", "?x/y?z", "?%e2%82", "?a b", "?é"};
    static final String[] FRAG = {"", "", "", "#f", "#", "#%41%42", "#[%41]", "#%E2%82", "#é", "#a#b", "# "};
    static final String MUT = " %[]:@/?#.é\u0001\u3000-_~\u0080\u0081\u00a0A9";

    /** a URI-like string: mostly well-formed, sometimes with a broken piece or a random edit */
    static String uri() {
        StringBuilder b = new StringBuilder();
        boolean clean = r(4) != 0;
        b.append(clean ? SCHEME[r(8)] : pick(SCHEME));
        int k = r(6);
        if (k < 3) {
            b.append("//").append(clean ? USER[r(8)] : pick(USER)).append(clean ? HOST[r(12)] : pick(HOST));
            b.append(clean ? PORT[r(7)] : pick(PORT));
        } else if (k == 3) {
            b.append(r(2) == 0 ? "//" : "///");
        }
        b.append(clean ? PATH[r(23)] : pick(PATH));
        if (r(4) == 0) b.append(PATH[r(23)].replace("/", ""));
        b.append(clean ? QUERY[r(8)] : pick(QUERY)).append(clean ? FRAG[r(9)] : pick(FRAG));
        String t = b.toString();
        if (r(6) == 0) {
            int i = r(t.length() + 1);
            t = t.substring(0, i) + MUT.charAt(r(MUT.length())) + t.substring(Math.min(t.length(), i + r(2)));
        }
        return t;
    }

    static String exc(Throwable x) {
        StringBuilder b = new StringBuilder("!").append(x.getClass().getName()).append(':').append(x.getMessage());
        if (x instanceof URISyntaxException) {
            URISyntaxException u = (URISyntaxException) x;
            b.append('/').append(u.getIndex()).append('/').append(u.getReason()).append('/').append(u.getInput().length());
        }
        if (x.getCause() != null) b.append(" cause=").append(x.getCause().getClass().getName());
        return b.toString();
    }

    static void desc(StringBuilder o, URI u) {
        o.append(u.getScheme()).append('|').append(u.getRawSchemeSpecificPart()).append('|').append(u.getSchemeSpecificPart())
            .append('|').append(u.getRawAuthority()).append('|').append(u.getAuthority()).append('|').append(u.getRawUserInfo())
            .append('|').append(u.getUserInfo()).append('|').append(u.getHost()).append('|').append(u.getPort())
            .append('|').append(u.getRawPath()).append('|').append(u.getPath()).append('|').append(u.getRawQuery())
            .append('|').append(u.getQuery()).append('|').append(u.getRawFragment()).append('|').append(u.getFragment())
            .append('|').append(u.isAbsolute()).append(u.isOpaque()).append('|').append(u).append('|').append(u.hashCode());
    }

    public static String parse(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            String t = uri();
            try {
                URI u = new URI(t);
                desc(o, u);
                o.append(u.toString() == t).append(u.getRawPath() == u.getRawSchemeSpecificPart());
            } catch (URISyntaxException | RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        return o.toString();
    }

    public static String create(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            String t = r(10) == 0 ? null : uri();
            try {
                URI u = r(2) == 0 ? URI.create(t) : new URI(t);
                o.append(u).append('|').append(u.getHost()).append('|').append(u.getPath());
            } catch (URISyntaxException x) {
                o.append(exc(x)).append('|').append(x);
            } catch (RuntimeException x) {
                o.append(exc(x)).append('|').append(x);
            }
            o.append(";\n");
        }
        return o.toString();
    }

    static String comp(String[] a) { return r(4) == 0 ? null : pick(a); }

    static final String[] CSCHEME = {"http", "s", "file", "1x", "mailto", "h t"};
    static final String[] CPART = {"a b", "x@y", "", "é\u3000", "%41", "a%zz", "/p q", "p", "?#", "[::1]", "u:p", "\u0001\u0085", "//h/p",
        "//[abc", "//[::1]a b", "//[x:y", "a/../b", "#f", "100%", "\u00a0\u2028x"};

    public static String ctor(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                URI u;
                switch (r(4)) {
                    case 0:
                        u = new URI(comp(CSCHEME), comp(CPART), comp(new String[]{"example.com", "::1", "[::1]", "1.2.3.4", "a_b", "", "h"}),
                            r(3) == 0 ? -1 : r(3) == 0 ? r(100000) - 2 : 80, comp(CPART), comp(CPART), comp(CPART));
                        break;
                    case 1:
                        u = new URI(comp(CSCHEME), comp(new String[]{"a b", "[::1]x y", "[x", "h:80", "u@h", "é", "%41", "a%zz", "[::1]:8", "[a]b%"}),
                            comp(CPART), comp(CPART), comp(CPART));
                        break;
                    case 2:
                        u = new URI(comp(CSCHEME), comp(new String[]{"example.com", "::1", "a.b", "", "x y"}), comp(CPART), comp(CPART));
                        break;
                    default:
                        u = new URI(comp(CSCHEME), comp(CPART), comp(CPART));
                }
                desc(o, u);
            } catch (URISyntaxException | RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        return o.toString();
    }

    static final String[] NPATH = {"a", "b", ".", "..", "", "c:d", "e%2F", "..."};

    static String path() {
        StringBuilder b = new StringBuilder();
        for (int i = r(3); i > 0; i--) b.append('/');
        for (int i = r(6); i > 0; i--) {
            b.append(pick(NPATH));
            for (int j = r(3) == 0 ? 2 : 1; j > 0; j--) b.append('/');
        }
        if (r(2) == 0 && b.length() > 0) b.setLength(b.length() - 1);
        return b.toString();
    }

    public static String norm(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            String p = path();
            if (r(4) == 0)   // a relative path whose first remaining segment has a ':' (gets a leading "./")
                p = pick(new String[]{"./", "a/../", "./.././", "b/./../", ".//", "a/b/../../"}) + pick(new String[]{"c:d", "x:", ":y"})
                    + pick(new String[]{"", "/", "/e", "/../f"});
            String t = (r(3) == 0 ? "s://h" + (p.startsWith("/") || p.isEmpty() ? "" : "/") : r(2) == 0 ? "s:" : "") + p
                + (r(3) == 0 ? "?q" : "") + (r(3) == 0 ? "#f" : "");
            try {
                URI u = new URI(t);
                URI n = u.normalize();
                o.append(n == u).append('|').append(n).append('|').append(n.getRawSchemeSpecificPart()).append('|').append(n.getPath())
                    .append('|').append(n.equals(u)).append(n.hashCode() == u.hashCode()).append(n.compareTo(u));
            } catch (URISyntaxException | RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        return o.toString();
    }

    static final String[] BASE = {"http://a/b/c/d;p?q", "http://a/b/c/", "http://a", "s:/x/y", "s:x", "mailto:a@b", "/rel/base", "rel/base",
        "", "#f", "http://u@h:8/p?q#f", "file:///tmp/a/", "s://h", "./a:b/c"};
    static final String[] REF = {"g", "./g", "g/", "/g", "//g", "?y", "g?y", "#s", "g#s", "g?y#s", ";x", "g;x", "", ".", "./", "..", "../",
        "../g", "../..", "../../", "../../g", "../../../g", "/./g", "/../g", "g.", ".g", "g..", "..g", "./../g", "./g/.", "g/./h",
        "g/../h", "a:b", "http:g", "#f", "x:y/z", "c:d/../e", "../c:d", "http://a/b/c/x", "http://A/b/c/d;p?q", "mailto:x"};

    public static String resolve(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                URI b = new URI(r(4) == 0 ? uri() : pick(BASE));
                String rs = r(4) == 0 ? uri() : pick(REF);
                if (r(3) == 0) {
                    URI x = b.resolve(rs);
                    o.append(x).append('|').append(x.getRawSchemeSpecificPart());
                } else {
                    URI c = new URI(rs);
                    URI x = b.resolve(c);
                    o.append(x == b).append(x == c).append(x).append('|').append(x.getRawSchemeSpecificPart()).append('|')
                        .append(x.getSchemeSpecificPart()).append('|').append(x.getAuthority()).append('|').append(x.hashCode());
                    URI y = b.relativize(x);
                    o.append("|R").append(y == x).append(y).append('|').append(y.getRawSchemeSpecificPart());
                    URI z = b.relativize(c);
                    o.append("|R").append(z == c).append(z);
                }
            } catch (URISyntaxException | RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        if (r(8) == 0) {
            try {
                URI.create("http://a/").resolve(r(2) == 0 ? (URI) null : URI.create("mailto:x").resolve((URI) null));
            } catch (RuntimeException x) {
                o.append(exc(x));
            }
            try {
                URI.create("a").relativize(null);
            } catch (RuntimeException x) {
                o.append(exc(x));
            }
            try {
                URI.create("a").resolve((String) null);
            } catch (RuntimeException x) {
                o.append(exc(x));
            }
        }
        return o.toString();
    }

    static final String[] EQ = {"http://h/p", "HTTP://H/p", "http://h/P", "http://h/%7e", "http://h/%7E", "http://h/~", "http://u@h:80/p",
        "http://U@h:80/p", "http://h:80/p", "http://h:81/p", "mailto:a", "MAILTO:a", "mailto:%41", "mailto:%61", "s://reg_name/p",
        "s://Reg_name/p", "/p", "p", "", "#f", "#F", "?q", "//h", "//h/", "http://h/p?%41", "http://h/p?%61#%41", "http://h/p#x",
        "http://[::1]/", "http://[::1%a]/", "http://h/p%2", "http://h/%41%42c", "http://h/%41%42"};

    public static String cmp(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        URI[] us = new URI[5];
        for (int i = 0; i < us.length; i++) {
            String t = r(3) == 0 ? uri() : pick(EQ);
            try {
                us[i] = new URI(t);
            } catch (URISyntaxException x) {
                us[i] = URI.create(pick(EQ).replace("%2", "%20"));
            }
            o.append(us[i].hashCode()).append(',');
        }
        for (int i = 0; i < us.length; i++)
            for (int j = 0; j < us.length; j++) {
                int c = us[i].compareTo(us[j]);
                o.append(us[i].equals(us[j]) ? 'T' : 'F').append(c < 0 ? -1 : c > 0 ? 1 : 0).append(c).append(' ');
            }
        o.append(us[0].equals(null)).append(us[0].equals("x")).append(us[0].equals(us[0]));
        if (r(4) == 0) {
            try {
                o.append(us[0].compareTo(null));
            } catch (RuntimeException x) {
                o.append(exc(x));
            }
        }
        return o.toString();
    }

    static final String[] UI2 = {"", "", "u@", "u:p@", "%41b@", ";:&=+$,@", "a@b@", "@"};
    static final String[] H2 = {"h", "h.example", "h-1.x-2.org", "1.2.3.4", "255.255.255.255", "256.0.0.1", "1.2.3.04", "001.2.3.4",
        "0001.2.3.4", "1.2.3", "1.2.3.4.", "1..2.3", "[::]", "[::1]", "[1::]", "[1:2::3:4]", "[1:2:3:4:5:6:7:8]", "[1:2:3:4:5:6:7::]",
        "[1:2:3:4:5:6:7:8:9]", "[::1.2.3.4]", "[1::1.2.3.4]", "[1:2:3:4:5:6:1.2.3.4]", "[1:2:3:4:5:1.2.3.4]", "[::1%eth0]",
        "[::1%e_t.0]", "[::1%]", "[::1%e-t]", "[%1]", "[12345::]", "[1:::2]", "[1::2::3]", "[:1]", "[1:]", "[::1", "[]", "[x]",
        "[::1.2.3]", "[::1.2.3.256]", "[1:2:3:4:5:6:7:1.2.3.4]", "a_b", "-h", "h-", "h.-x", "1h.2x", "h.1x", "h..x", "h%41", "h.", "x:y",
        "ab.cd.", "9.9.9.9x", "[::1]x", "h]"};
    static final String[] P2 = {"", "", ":1", ":", ":65535", ":0", ":007", ":2147483647", ":2147483648", ":-1", ":1a", ":1:2"};

    public static String auth(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            String t = (r(3) == 0 ? "" : "s:") + "//" + pick(UI2) + pick(H2) + pick(P2) + (r(2) == 0 ? "/p" : r(2) == 0 ? "?q" : "");
            try {
                URI u = new URI(t);
                o.append(u.getRawAuthority()).append('|').append(u.getAuthority()).append('|').append(u.getRawUserInfo())
                    .append('|').append(u.getHost()).append('|').append(u.getPort()).append('|').append(u.hashCode());
                try {
                    URI v = u.parseServerAuthority();
                    o.append("|P").append(v == u).append(v.getHost()).append(v.getPort()).append(v.getUserInfo());
                } catch (URISyntaxException x) {
                    o.append("|P").append(exc(x)).append(u.getHost()).append(u.getPort()).append(u.getAuthority());
                }
            } catch (URISyntaxException | RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        return o.toString();
    }

    static final String[] NA = {"é", "ü", "ÿ", "ĀŁ", "Жи", "€", "中文", "한", "😀", "𐀀", "\u00a0", "\u0085", "\u3000", "%C3%A9",
        "%E2%82%AC", "%F0%9F%98%80", "%C3", "%E2%82", "%FF", "%80%80", "%C0%80", "%ED%A0%80", "%F4%90%80%80", "%F0%9F%98", "%41%42", "a", "/", "x"};

    public static String ascii(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            StringBuilder b = new StringBuilder();
            for (int i = r(5); i > 0; i--) b.append(pick(NA));
            String seg = b.toString();
            if (r(30) == 0) seg = seg + "\ud800";
            String t;
            switch (r(4)) {
                case 0: t = "http://h/" + seg + "?" + seg + "#" + seg; break;
                case 1: t = "s:" + seg + "x"; break;
                case 2: t = "//" + seg + "x/" + seg; break;
                default: t = seg + "?q";
            }
            try {
                URI u = r(3) == 0 ? new URI("s", "u" + seg, "h", -1, "/" + seg, seg, seg) : new URI(t);
                o.append(u).append('|').append(u.getPath()).append('|').append(u.getQuery()).append('|').append(u.getFragment())
                    .append('|').append(u.getSchemeSpecificPart()).append('|').append(u.getAuthority()).append('|').append(u.getUserInfo());
                o.append('|').append(u.toASCIIString());
            } catch (URISyntaxException | RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        return o.toString();
    }
}

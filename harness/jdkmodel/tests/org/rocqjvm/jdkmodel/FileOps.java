package org.rocqjvm.jdkmodel;

import java.io.File;
import java.io.IOException;
import java.net.URI;

/** Differential tests of the pure path operations of java.io.File (Unix): normalization in the
 *  constructors, getName/getParent/getParentFile/getPath/isAbsolute/getAbsolutePath (absolute paths),
 *  equals/hashCode/compareTo, File(URI), toURI of "/" and of invalid (NUL) absolute paths, and the
 *  file-system queries that JDK 21 answers without the file system for an invalid path. */
public final class FileOps {
    private FileOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }
    static String pick(String[] a) { return a[r(a.length)]; }

    static final String[] SEG = {"a", "b", ".", "..", "", "x.txt", ".h", "a b", "é", "c:d", "\\"};

    static String path() {
        StringBuilder b = new StringBuilder();
        for (int i = r(4) == 0 ? r(4) : r(2); i > 0; i--) b.append('/');
        int n = r(5);
        for (int i = 0; i < n; i++) {
            b.append(pick(SEG));
            if (i < n - 1 || r(3) == 0)
                for (int j = r(4) == 0 ? 1 + r(3) : 1; j > 0; j--) b.append('/');
        }
        return b.toString();
    }

    static String exc(Throwable x) {
        return "!" + x.getClass().getName() + ":" + x.getMessage();
    }

    static void desc(StringBuilder o, File f) {
        o.append(f.getPath()).append('|').append(f.getName()).append('|').append(f.getParent()).append('|').append(f.isAbsolute())
            .append('|').append(f).append('|').append(f.hashCode());
        File p = f.getParentFile();
        o.append('|').append(p == null ? "-" : p.getPath() + p.isAbsolute() + p.getName());
        if (f.isAbsolute()) o.append('|').append(f.getAbsolutePath()).append(f.getAbsoluteFile().equals(f));
    }

    public static String paths(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        File prev = null;
        for (int k = 0; k < 8; k++) {
            String t = r(16) == 0 ? null : path();
            try {
                File f = new File(t);
                desc(o, f);
                o.append('|').append(f.getPath() == t);
                if (prev != null) {
                    int c = f.compareTo(prev);
                    o.append('|').append(f.equals(prev)).append(c < 0 ? -1 : c > 0 ? 1 : 0).append(c);
                }
                prev = f;
            } catch (RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        return o.toString();
    }

    public static String join(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 8; k++) {
            String a = r(6) == 0 ? null : path(), c = r(10) == 0 ? null : path();
            try {
                File f;
                switch (r(3)) {
                    case 0: f = new File(a, c); break;
                    case 1: f = new File(a == null ? null : new File(a), c); break;
                    default: f = new File(new File(a == null ? "" : a), c);
                }
                desc(o, f);
                File g = new File(f.getPath());
                o.append('|').append(g.equals(f)).append(g.hashCode() == f.hashCode()).append(f.equals(f.getPath()))
                    .append(f.equals(null)).append(f.compareTo(g));
            } catch (RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        return o.toString();
    }

    static final String[] FURI = {"file:/a/b", "file:/a/b/", "file:///a//b", "FILE:/x", "file:/a%20b/%C3%A9", "file:/", "file://h/a",
        "file:/a?q", "file:/a#f", "file:a", "http:/a", "/a", "file:", "file:/%2F", "file:/a/../b", "file:/./", "file:/%00"};

    public static String misc(int seed) {
        s = seed;
        StringBuilder o = new StringBuilder();
        for (int k = 0; k < 6; k++) {
            try {
                switch (r(4)) {
                    case 0: {
                        String u = pick(FURI);
                        File f = r(12) == 0 ? new File((URI) null) : new File(URI.create(u.equals("file:") ? "file:x" : u));
                        desc(o, f);
                        break;
                    }
                    case 1: {
                        // an invalid path (NUL): JDK 21 answers these without the file system
                        File f = new File("/" + path() + "\u0000" + path());
                        o.append(f.exists()).append(f.isDirectory()).append(f.isFile()).append(f.isHidden()).append(f.canRead())
                            .append(f.canWrite()).append(f.canExecute()).append(f.length()).append(f.lastModified())
                            .append(f.list() == null).append(f.listFiles() == null).append(f.mkdir()).append(f.mkdirs())
                            .append(f.delete()).append(f.setReadOnly()).append(f.setWritable(true)).append(f.setReadable(false))
                            .append(f.setExecutable(true)).append(f.renameTo(new File("x"))).append(f.getTotalSpace())
                            .append(f.getFreeSpace()).append(f.getUsableSpace()).append(f.setLastModified(5));
                        o.append('|').append(f.toURI()).append('|').append(f.toURI().getPath().equals(f.getPath()));
                        try {
                            f.createNewFile();
                        } catch (IOException x) {
                            o.append(exc(x));
                        }
                        try {
                            o.append(f.getCanonicalPath());
                        } catch (IOException x) {
                            o.append(exc(x));
                        }
                        try {
                            o.append(f.setLastModified(-1));
                        } catch (RuntimeException x) {
                            o.append(exc(x));
                        }
                        break;
                    }
                    case 2: {
                        String pre = r(5) == 0 ? null : pick(new String[]{"", "a", "ab", "a/"});
                        try {
                            File.createTempFile(pre, r(2) == 0 ? null : ".x");
                        } catch (IOException x) {
                            o.append(exc(x));
                        }
                        break;
                    }
                    default: {
                        File[] roots = File.listRoots();
                        o.append(roots.length).append(roots[0]).append(File.separator).append(File.separatorChar)
                            .append(File.pathSeparator).append(File.pathSeparatorChar).append(new File("/").toURI())
                            .append(new File("//").toURI());
                        File a = new File(path());
                        if (r(3) == 0) o.append(a.compareTo(null));
                        if (r(3) == 0) o.append(a.renameTo(null));
                        if (r(3) == 0) o.append(new File("a", (String) null));
                        if (r(3) == 0) o.append(new File((File) null, (String) null));
                    }
                }
            } catch (RuntimeException x) {
                o.append(exc(x));
            }
            o.append(";\n");
        }
        return o.toString();
    }
}

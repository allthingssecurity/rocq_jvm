/*
 * rocq-jvm model of java.io.File (clean-room, Apache-2.0), from the Javadoc, for the Unix file system
 * of JDK 21 (separator '/', path separator ':'): the pure path operations only.
 * - Constructors normalize the pathname as UnixFileSystem does: runs of '/' become one '/', a trailing
 *   '/' goes (but "/" stays); File(parent, child) joins with one '/' (an empty parent means "/");
 *   File(URI) takes the decoded path of an absolute, hierarchical "file" URI without authority, query
 *   or fragment (JDK 21's IllegalArgumentException messages).
 * - getName, getParent, getParentFile, getPath, toString, isAbsolute (starts with '/'), equals /
 *   compareTo (String order of the paths), hashCode (path.hashCode() ^ 1234321), listRoots ("/").
 * - getAbsolutePath / getAbsoluteFile of an absolute path; toURI of an absolute path when it needs no
 *   isDirectory() (the path is "/" or contains NUL, an invalid path, for which isDirectory() is false).
 * - A path containing NUL is invalid: the file-system queries then answer without the file system
 *   (exists() false, length() 0, list() null, createNewFile/getCanonicalPath IOException
 *   "Invalid file path", ...), as JDK 21 does; createTempFile's prefix check, setLastModified's
 *   negative-time check and renameTo's null check come before any file-system access.
 * STUCK: every other file-system access (exists, isDirectory, length, list, mkdir, delete, ...), the
 * current directory (user.dir: getAbsolutePath of a relative path), getCanonicalPath, toPath, toURL.
 * The NullPointerException texts of JDK 21 are thrown explicitly where the JDK has helpful ones.
 */
package java.io;

import java.net.URI;
import java.net.URISyntaxException;

public class File implements Serializable, Comparable<File> {
    private static final long serialVersionUID = 301077366599181567L;

    private final String path;
    private final transient int prefixLength;   // 1 for an absolute path, else 0
    private transient int status;               // 0 unknown, 1 valid, 2 invalid (contains NUL)

    public static final char separatorChar = slash();
    public static final String separator = String.valueOf(separatorChar);
    public static final char pathSeparatorChar = colon();
    public static final String pathSeparator = String.valueOf(pathSeparatorChar);

    private static char slash() {
        return '/';
    }

    private static char colon() {
        return ':';
    }

    private File(String pathname, int prefixLength) {
        this.path = pathname;
        this.prefixLength = prefixLength;
    }

    public File(String pathname) {
        if (pathname == null) throw new NullPointerException();
        this.path = normalize(pathname);
        this.prefixLength = prefix(this.path);
    }

    public File(String parent, String child) {
        if (child == null) throw new NullPointerException();
        if (parent != null) {
            if (parent.isEmpty()) this.path = join("/", normalize(child));
            else this.path = join(normalize(parent), normalize(child));
        } else {
            this.path = normalize(child);
        }
        this.prefixLength = prefix(this.path);
    }

    public File(File parent, String child) {
        if (child == null) throw new NullPointerException();
        if (parent != null) {
            if (parent.path.isEmpty()) this.path = join("/", normalize(child));
            else this.path = join(parent.path, normalize(child));
        } else {
            this.path = normalize(child);
        }
        this.prefixLength = prefix(this.path);
    }

    public File(URI uri) {
        if (uri == null)
            throw new NullPointerException("Cannot invoke \"java.net.URI.isAbsolute()\" because \"uri\" is null");
        if (!uri.isAbsolute()) throw new IllegalArgumentException("URI is not absolute");
        if (uri.isOpaque()) throw new IllegalArgumentException("URI is not hierarchical");
        String scheme = uri.getScheme();
        if (scheme == null || !scheme.equalsIgnoreCase("file"))
            throw new IllegalArgumentException("URI scheme is not \"file\"");
        if (uri.getRawAuthority() != null) throw new IllegalArgumentException("URI has an authority component");
        if (uri.getRawFragment() != null) throw new IllegalArgumentException("URI has a fragment component");
        if (uri.getRawQuery() != null) throw new IllegalArgumentException("URI has a query component");
        String p = uri.getPath();
        if (p.isEmpty()) throw new IllegalArgumentException("URI path component is empty");
        if (p.endsWith("/") && p.length() > 1) p = p.substring(0, p.length() - 1);
        this.path = normalize(p);
        this.prefixLength = prefix(this.path);
    }

    // ---- the Unix path rules ----

    // one '/' for each run of '/' from the first run on; no trailing '/' unless the path is "/"
    private static String normalize(String s) {
        int from = s.indexOf("//");
        if (from < 0) {
            if (!s.endsWith("/")) return s;
            from = s.length() - 1;
        }
        int n = s.length();
        while (n > from && s.charAt(n - 1) == '/') n--;
        if (n == 0) return "/";
        if (n == from) return s.substring(0, from);
        StringBuilder sb = new StringBuilder(n);
        if (from > 0) sb.append(s, 0, from);
        boolean afterSlash = false;
        for (int i = from; i < n; i++) {
            char c = s.charAt(i);
            if (afterSlash && c == '/') continue;
            sb.append(c);
            afterSlash = c == '/';
        }
        return sb.toString();
    }

    private static int prefix(String s) {
        return s.startsWith("/") ? 1 : 0;
    }

    private static String dropTrailingSlash(String s) {
        int n = s.length();
        return (n > 1 && s.charAt(n - 1) == '/') ? s.substring(0, n - 1) : s;
    }

    // parent and child are normalized
    private static String join(String parent, String child) {
        if (child.isEmpty()) return parent;
        if (child.charAt(0) == '/') {
            if (parent.equals("/")) return child;
            return dropTrailingSlash(parent + child);
        }
        if (parent.equals("/")) return dropTrailingSlash(parent + child);
        return dropTrailingSlash(parent + '/' + child);
    }

    final boolean isInvalid() {
        int st = status;
        if (st == 0) {
            st = getPath().indexOf('\u0000') >= 0 ? 2 : 1;
            status = st;
        }
        return st == 2;
    }

    int getPrefixLength() {
        return prefixLength;
    }

    private RuntimeException fileSystem(String what) {
        return FileModelStuck.unsupported("File." + what + ": file-system access");
    }

    // ---- path operations ----

    public String getName() {
        int i = path.lastIndexOf(separatorChar);
        if (i < prefixLength) return path.substring(prefixLength);
        return path.substring(i + 1);
    }

    public String getParent() {
        int i = path.lastIndexOf(separatorChar);
        if (i < prefixLength) {
            if (prefixLength > 0 && path.length() > prefixLength) return path.substring(0, prefixLength);
            return null;
        }
        return path.substring(0, i);
    }

    public File getParentFile() {
        String p = getParent();
        if (p == null) return null;
        if (getClass() != File.class) p = normalize(p);
        return new File(p, prefixLength);
    }

    public String getPath() {
        return path;
    }

    public boolean isAbsolute() {
        return prefixLength != 0;
    }

    public String getAbsolutePath() {
        if (prefixLength != 0) return getPath();
        throw FileModelStuck.unsupported("File.getAbsolutePath of a relative path (the current directory, user.dir)");
    }

    public File getAbsoluteFile() {
        String abs = getAbsolutePath();
        if (getClass() != File.class) abs = normalize(abs);
        return new File(abs, prefix(abs));
    }

    public String getCanonicalPath() throws IOException {
        if (isInvalid()) throw new IOException("Invalid file path");
        throw fileSystem("getCanonicalPath");
    }

    public File getCanonicalFile() throws IOException {
        String c = getCanonicalPath();
        if (getClass() != File.class) c = normalize(c);
        return new File(c, prefix(c));
    }

    @Deprecated
    public java.net.URL toURL() throws java.net.MalformedURLException {
        throw FileModelStuck.unsupported("File.toURL (java.net.URL is not modelled)");
    }

    public URI toURI() {
        try {
            File f = getAbsoluteFile();
            String sp = f.getPath();
            if (!sp.startsWith("/")) sp = "/" + sp;
            if (!sp.endsWith("/") && f.isDirectory()) sp = sp + "/";
            if (sp.startsWith("//")) sp = "//" + sp;
            return new URI("file", null, sp, null);
        } catch (URISyntaxException x) {
            throw new Error(x);
        }
    }

    public java.nio.file.Path toPath() {
        throw FileModelStuck.unsupported("File.toPath (java.nio.file is not modelled)");
    }

    // ---- file-system queries: only an invalid path (containing NUL) is answered ----

    public boolean canRead() {
        if (isInvalid()) return false;
        throw fileSystem("canRead");
    }

    public boolean canWrite() {
        if (isInvalid()) return false;
        throw fileSystem("canWrite");
    }

    public boolean canExecute() {
        if (isInvalid()) return false;
        throw fileSystem("canExecute");
    }

    public boolean exists() {
        if (isInvalid()) return false;
        throw fileSystem("exists");
    }

    public boolean isDirectory() {
        if (isInvalid()) return false;
        throw fileSystem("isDirectory");
    }

    public boolean isFile() {
        if (isInvalid()) return false;
        throw fileSystem("isFile");
    }

    public boolean isHidden() {
        if (isInvalid()) return false;
        throw fileSystem("isHidden");
    }

    public long lastModified() {
        if (isInvalid()) return 0L;
        throw fileSystem("lastModified");
    }

    public long length() {
        if (isInvalid()) return 0L;
        throw fileSystem("length");
    }

    public boolean createNewFile() throws IOException {
        if (isInvalid()) throw new IOException("Invalid file path");
        throw fileSystem("createNewFile");
    }

    public boolean delete() {
        if (isInvalid()) return false;
        throw fileSystem("delete");
    }

    public void deleteOnExit() {
        if (isInvalid()) return;
        throw fileSystem("deleteOnExit");
    }

    public String[] list() {
        if (isInvalid()) return null;
        throw fileSystem("list");
    }

    public String[] list(FilenameFilter filter) {
        if (isInvalid()) return null;
        throw fileSystem("list");
    }

    public File[] listFiles() {
        if (isInvalid()) return null;
        throw fileSystem("listFiles");
    }

    public File[] listFiles(FilenameFilter filter) {
        if (isInvalid()) return null;
        throw fileSystem("listFiles");
    }

    public File[] listFiles(FileFilter filter) {
        if (isInvalid()) return null;
        throw fileSystem("listFiles");
    }

    public boolean mkdir() {
        if (isInvalid()) return false;
        throw fileSystem("mkdir");
    }

    public boolean mkdirs() {
        // JDK 21: exists() and mkdir() are false and getCanonicalFile() throws for an invalid path
        if (isInvalid()) return false;
        throw fileSystem("mkdirs");
    }

    public boolean renameTo(File dest) {
        if (dest == null) throw new NullPointerException();
        if (isInvalid() || dest.isInvalid()) return false;
        throw fileSystem("renameTo");
    }

    public boolean setLastModified(long time) {
        if (time < 0) throw new IllegalArgumentException("Negative time");
        if (isInvalid()) return false;
        throw fileSystem("setLastModified");
    }

    public boolean setReadOnly() {
        if (isInvalid()) return false;
        throw fileSystem("setReadOnly");
    }

    public boolean setWritable(boolean writable, boolean ownerOnly) {
        if (isInvalid()) return false;
        throw fileSystem("setWritable");
    }

    public boolean setWritable(boolean writable) {
        return setWritable(writable, true);
    }

    public boolean setReadable(boolean readable, boolean ownerOnly) {
        if (isInvalid()) return false;
        throw fileSystem("setReadable");
    }

    public boolean setReadable(boolean readable) {
        return setReadable(readable, true);
    }

    public boolean setExecutable(boolean executable, boolean ownerOnly) {
        if (isInvalid()) return false;
        throw fileSystem("setExecutable");
    }

    public boolean setExecutable(boolean executable) {
        return setExecutable(executable, true);
    }

    public long getTotalSpace() {
        if (isInvalid()) return 0L;
        throw fileSystem("getTotalSpace");
    }

    public long getFreeSpace() {
        if (isInvalid()) return 0L;
        throw fileSystem("getFreeSpace");
    }

    public long getUsableSpace() {
        if (isInvalid()) return 0L;
        throw fileSystem("getUsableSpace");
    }

    public static File[] listRoots() {
        return new File[] {new File("/")};
    }

    public static File createTempFile(String prefix, String suffix, File directory) throws IOException {
        if (prefix == null)
            throw new NullPointerException("Cannot invoke \"String.length()\" because \"prefix\" is null");
        if (prefix.length() < 3)
            throw new IllegalArgumentException("Prefix string \"" + prefix + "\" too short: length must be at least 3");
        throw FileModelStuck.unsupported("File.createTempFile: file-system access");
    }

    public static File createTempFile(String prefix, String suffix) throws IOException {
        return createTempFile(prefix, suffix, null);
    }

    // ---- comparison ----

    public int compareTo(File pathname) {
        if (pathname == null)
            throw new NullPointerException("Cannot invoke \"java.io.File.getPath()\" because \"f2\" is null");
        return getPath().compareTo(pathname.getPath());
    }

    public boolean equals(Object obj) {
        if (obj instanceof File) return compareTo((File) obj) == 0;
        return false;
    }

    public int hashCode() {
        return getPath().hashCode() ^ 1234321;
    }

    public String toString() {
        return getPath();
    }
}

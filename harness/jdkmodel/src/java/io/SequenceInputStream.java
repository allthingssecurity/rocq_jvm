/*
 * rocq-jvm model of java.io.SequenceInputStream (clean-room, Apache-2.0), JDK 21 behaviour: the
 * streams are read in turn (each one closed when it is exhausted, the next one taken from the
 * enumeration; a null element is a NullPointerException), read(byte[], ..) returns what one
 * stream gives, close closes all remaining streams (the first IOException thrown at the end,
 * with the later ones suppressed), transferTo transfers each stream in turn (for the class
 * itself).
 */
package java.io;

import java.util.Enumeration;

public class SequenceInputStream extends InputStream {
    private final Enumeration<? extends InputStream> e;
    private InputStream in;

    public SequenceInputStream(Enumeration<? extends InputStream> e) {
        this.e = e;
        peekNextStream();
    }

    public SequenceInputStream(InputStream s1, InputStream s2) {
        this(new Two(s1, s2));
    }

    /** Collections.enumeration(Arrays.asList(s1, s2)). */
    private static final class Two implements Enumeration<InputStream> {
        private final InputStream a, b;
        private int next = 0;

        Two(InputStream a, InputStream b) {
            this.a = a;
            this.b = b;
        }

        public boolean hasMoreElements() {
            return next < 2;
        }

        public InputStream nextElement() {
            if (next >= 2) throw new java.util.NoSuchElementException();
            return next++ == 0 ? a : b;
        }
    }

    final void nextStream() throws IOException {
        if (in != null) in.close();
        peekNextStream();
    }

    private void peekNextStream() {
        if (e == null) throw ModelIo.invokeOnNull("java.util.Enumeration.hasMoreElements()", "this.e");
        if (e.hasMoreElements()) {
            in = (InputStream) e.nextElement();
            if (in == null) throw new NullPointerException();
        } else {
            in = null;
        }
    }

    public int available() throws IOException {
        if (in == null) return 0;
        return in.available();
    }

    public int read() throws IOException {
        while (in != null) {
            int c = in.read();
            if (c != -1) return c;
            nextStream();
        }
        return -1;
    }

    public int read(byte[] b, int off, int len) throws IOException {
        if (in == null) return -1;
        if (b == null) throw new NullPointerException();
        ModelIo.checkFromIndexSize(off, len, b.length);
        if (len == 0) return 0;
        do {
            int n = in.read(b, off, len);
            if (n > 0) return n;
            nextStream();
        } while (in != null);
        return -1;
    }

    public void close() throws IOException {
        IOException first = null;
        while (in != null) {
            try {
                in.close();
            } catch (IOException x) {
                if (first == null) first = x;
                else first.addSuppressed(x);
            }
            peekNextStream();
        }
        if (first != null) throw first;
    }

    public long transferTo(OutputStream out) throws IOException {
        if (out == null) throw new NullPointerException("out");
        if (getClass() == SequenceInputStream.class) {
            long total = 0;
            while (in != null) {
                long k = in.transferTo(out);
                if (total < Long.MAX_VALUE) {
                    long t = total + k;
                    total = (((total ^ t) & (k ^ t)) < 0) ? Long.MAX_VALUE : t;
                }
                nextStream();
            }
            return total;
        }
        return super.transferTo(out);
    }
}

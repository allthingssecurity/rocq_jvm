/*
 * rocq-jvm model of java.io.PrintStream (clean-room, Apache-2.0) over in-memory streams, JDK 21
 * behaviour: text goes through the JDK's layering, a BufferedWriter (8192 chars) over an
 * OutputStreamWriter in the stream's charset (default UTF-8) that writes its bytes back into
 * this.write(byte[], int, int), both flushed after every print / println (so the wrapped stream
 * receives one write per print, and a surrogate pair split across two prints is encoded as a
 * pair); IOExceptions set the error flag; autoflush flushes after println, after write(byte[]),
 * after write('\n') and after a print whose text contains '\n'; println writes "\n" and, for
 * the class itself, in one write with the text (subclasses: print, then newLine).
 * printf/format: the model Formatter formats into a buffer whose contents (also the part written
 * before a format exception) are printed in one print; the JDK prints piece by piece, which only
 * a stream that sees the individual writes can tell apart, so format is STUCK unless this is a
 * PrintStream (exact class) over a ByteArrayOutputStream (or over nested PrintStreams over one).
 * System.out / System.err are host I/O and not modelled.
 * Not modelled (STUCK): files, explicit locales, InterruptedIOException.
 */
package java.io;

import java.nio.charset.Charset;
import java.util.Locale;

public class PrintStream extends FilterOutputStream implements Appendable, Closeable {
    private final boolean autoFlush;
    private boolean trouble = false;
    private final Charset charset;
    private BufferedWriter textOut;
    private OutputStreamWriter charOut;
    private boolean closing = false;

    private static <T> T nonNull(T obj, String message) {
        if (obj == null) throw new NullPointerException(message);
        return obj;
    }

    private static Charset toCharset(String csn) throws UnsupportedEncodingException {
        nonNull(csn, "charsetName");
        return ModelIo.charsetFor(csn);
    }

    private PrintStream(boolean autoFlush, OutputStream out) {
        super(out);
        this.autoFlush = autoFlush;
        this.charset = out instanceof PrintStream ? ((PrintStream) out).charset() : Charset.defaultCharset();
        this.charOut = new OutputStreamWriter(this, charset);
        this.textOut = new BufferedWriter(charOut);
    }

    public PrintStream(OutputStream out) {
        this(out, false);
    }

    public PrintStream(OutputStream out, boolean autoFlush) {
        this(autoFlush, nonNull(out, "Null output stream"));
    }

    public PrintStream(OutputStream out, boolean autoFlush, String encoding) throws UnsupportedEncodingException {
        this(nonNull(out, "Null output stream"), autoFlush, toCharset(encoding));
    }

    public PrintStream(OutputStream out, boolean autoFlush, Charset charset) {
        super(out);
        this.autoFlush = autoFlush;
        this.charOut = new OutputStreamWriter(this, charset);
        this.textOut = new BufferedWriter(charOut);
        this.charset = charset;
    }

    public PrintStream(String fileName) throws FileNotFoundException {
        this(noFiles(), false);
    }

    public PrintStream(String fileName, String csn) throws FileNotFoundException, UnsupportedEncodingException {
        this(noFiles(), false);
    }

    public PrintStream(String fileName, Charset charset) throws IOException {
        this(noFiles(), false);
    }

    public PrintStream(File file) throws FileNotFoundException {
        this(noFiles(), false);
    }

    public PrintStream(File file, String csn) throws FileNotFoundException, UnsupportedEncodingException {
        this(noFiles(), false);
    }

    public PrintStream(File file, Charset charset) throws IOException {
        this(noFiles(), false);
    }

    private static OutputStream noFiles() {
        throw ModelIo.unsupported("PrintStream on a file");
    }

    private void checkOpen() throws IOException {
        if (out == null) throw new IOException("Stream closed");
    }

    private void failed(IOException x) {
        if (x instanceof InterruptedIOException) throw ModelIo.unsupported("InterruptedIOException in a PrintStream");
        trouble = true;
    }

    public void flush() {
        synchronized (this) {
            try {
                checkOpen();
                out.flush();
            } catch (IOException x) {
                trouble = true;
            }
        }
    }

    public void close() {
        synchronized (this) {
            if (!closing) {
                closing = true;
                try {
                    textOut.close();
                    out.close();
                } catch (IOException x) {
                    trouble = true;
                }
                textOut = null;
                charOut = null;
                out = null;
            }
        }
    }

    public boolean checkError() {
        if (out != null) flush();
        if (out instanceof PrintStream) return ((PrintStream) out).checkError();
        return trouble;
    }

    protected void setError() {
        trouble = true;
    }

    protected void clearError() {
        trouble = false;
    }

    public void write(int b) {
        try {
            synchronized (this) {
                checkOpen();
                out.write(b);
                if (b == '\n' && autoFlush) out.flush();
            }
        } catch (IOException x) {
            failed(x);
        }
    }

    public void write(byte[] buf, int off, int len) {
        try {
            synchronized (this) {
                checkOpen();
                out.write(buf, off, len);
                if (autoFlush) out.flush();
            }
        } catch (IOException x) {
            failed(x);
        }
    }

    public void write(byte[] buf) throws IOException {
        if (buf == null) throw ModelIo.arrayLengthOfNull("buf");
        this.write(buf, 0, buf.length);
    }

    public void writeBytes(byte[] buf) {
        if (buf == null) throw ModelIo.arrayLengthOfNull("buf");
        this.write(buf, 0, buf.length);
    }

    private void writeText(char[] buf) {
        try {
            synchronized (this) {
                checkOpen();
                textOut.write(buf);
                textOut.flushBuffer();
                charOut.flushBuffer();
                if (autoFlush) {
                    for (char c : buf) {
                        if (c == '\n') {
                            out.flush();
                            break;
                        }
                    }
                }
            }
        } catch (IOException x) {
            failed(x);
        }
    }

    private void writelnText(char[] buf) {
        try {
            synchronized (this) {
                checkOpen();
                textOut.write(buf);
                textOut.newLine();
                textOut.flushBuffer();
                charOut.flushBuffer();
                if (autoFlush) out.flush();
            }
        } catch (IOException x) {
            failed(x);
        }
    }

    private void writeText(String s) {
        try {
            synchronized (this) {
                checkOpen();
                textOut.write(s);
                textOut.flushBuffer();
                charOut.flushBuffer();
                if (autoFlush && s.indexOf('\n') >= 0) out.flush();
            }
        } catch (IOException x) {
            failed(x);
        }
    }

    private void writelnText(String s) {
        try {
            synchronized (this) {
                checkOpen();
                textOut.write(s);
                textOut.newLine();
                textOut.flushBuffer();
                charOut.flushBuffer();
                if (autoFlush) out.flush();
            }
        } catch (IOException x) {
            failed(x);
        }
    }

    private void newLine() {
        try {
            synchronized (this) {
                checkOpen();
                textOut.newLine();
                textOut.flushBuffer();
                charOut.flushBuffer();
                if (autoFlush) out.flush();
            }
        } catch (IOException x) {
            failed(x);
        }
    }

    public void print(boolean b) {
        writeText(String.valueOf(b));
    }

    public void print(char c) {
        writeText(String.valueOf(c));
    }

    public void print(int i) {
        writeText(String.valueOf(i));
    }

    public void print(long l) {
        writeText(String.valueOf(l));
    }

    public void print(float f) {
        writeText(String.valueOf(f));
    }

    public void print(double d) {
        writeText(String.valueOf(d));
    }

    public void print(char[] s) {
        writeText(s);
    }

    public void print(String s) {
        writeText(String.valueOf(s));
    }

    public void print(Object obj) {
        writeText(String.valueOf(obj));
    }

    public void println() {
        newLine();
    }

    private boolean exact() {
        return getClass() == PrintStream.class;
    }

    public void println(boolean x) {
        if (exact()) {
            writelnText(String.valueOf(x));
        } else {
            synchronized (this) {
                print(x);
                newLine();
            }
        }
    }

    public void println(char x) {
        if (exact()) {
            writelnText(String.valueOf(x));
        } else {
            synchronized (this) {
                print(x);
                newLine();
            }
        }
    }

    public void println(int x) {
        if (exact()) {
            writelnText(String.valueOf(x));
        } else {
            synchronized (this) {
                print(x);
                newLine();
            }
        }
    }

    public void println(long x) {
        if (exact()) {
            writelnText(String.valueOf(x));
        } else {
            synchronized (this) {
                print(x);
                newLine();
            }
        }
    }

    public void println(float x) {
        if (exact()) {
            writelnText(String.valueOf(x));
        } else {
            synchronized (this) {
                print(x);
                newLine();
            }
        }
    }

    public void println(double x) {
        if (exact()) {
            writelnText(String.valueOf(x));
        } else {
            synchronized (this) {
                print(x);
                newLine();
            }
        }
    }

    public void println(char[] x) {
        if (exact()) {
            writelnText(x);
        } else {
            synchronized (this) {
                print(x);
                newLine();
            }
        }
    }

    public void println(String x) {
        if (exact()) {
            writelnText(String.valueOf(x));
        } else {
            synchronized (this) {
                print(x);
                newLine();
            }
        }
    }

    public void println(Object x) {
        String s = String.valueOf(x);
        if (exact()) {
            writelnText(String.valueOf(s));
        } else {
            synchronized (this) {
                print(s);
                newLine();
            }
        }
    }

    public PrintStream printf(String format, Object... args) {
        return format(format, args);
    }

    public PrintStream printf(Locale l, String format, Object... args) {
        return format(l, format, args);
    }

    /** Whether the stream cannot tell one write from the Formatter's piecewise prints. */
    private static boolean seesOneWrite(OutputStream o) {
        if (o == null) return true;
        Class<?> c = o.getClass();
        if (c == ByteArrayOutputStream.class) return true;
        if (c == PrintStream.class) return seesOneWrite(((PrintStream) o).out);
        return false;
    }

    public PrintStream format(String format, Object... args) {
        try {
            synchronized (this) {
                checkOpen();
                StringBuilder text = new StringBuilder();
                try {
                    new java.util.Formatter(text).format(format, args);
                } finally {
                    if (text.length() > 0) {
                        if (!exact() || !seesOneWrite(out))
                            throw ModelIo.unsupported("PrintStream.format onto a stream that may see the Formatter's pieces");
                        writeText(text.toString());
                    }
                }
            }
        } catch (IOException x) {
            failed(x);
        }
        return this;
    }

    public PrintStream format(Locale l, String format, Object... args) {
        throw ModelIo.unsupported("PrintStream.format with an explicit locale");
    }

    public PrintStream append(CharSequence csq) {
        print(ModelIo.valueOf(csq));
        return this;
    }

    public PrintStream append(CharSequence csq, int start, int end) {
        if (csq == null) csq = "null";
        return append(ModelIo.subSequence(csq, start, end));
    }

    public PrintStream append(char c) {
        print(c);
        return this;
    }

    public Charset charset() {
        return charset;
    }
}

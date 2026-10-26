/*
 * rocq-jvm model of java.io.PrintWriter (clean-room, Apache-2.0), JDK 21 behaviour: IOExceptions
 * of the wrapped writer set the error flag (checkError flushes first and asks a wrapped
 * PrintWriter / PrintStream), the print methods write String.valueOf of their argument, println
 * writes the line separator "\n" and flushes when autoflush is on, an OutputStream is wrapped in
 * a BufferedWriter over an OutputStreamWriter (the PrintStream's charset, else UTF-8).
 * printf/format: the model Formatter (java.util.Formatter, default locale) formats into a
 * buffer whose contents (also the part written before a format exception) are written in one
 * write; the JDK's Formatter appends piece by piece, which only a writer that sees the
 * individual writes can tell apart, so format is STUCK unless this is a PrintWriter (exact
 * class) over a StringWriter, a CharArrayWriter, a nested PrintWriter, or a BufferedWriter whose
 * buffer takes the text without a flush or that writes into a StringWriter / CharArrayWriter
 * (exact classes; its flushes then happen at the same text positions and cannot fail).
 * An InterruptedIOException interrupts the current thread in the JDK: STUCK here.
 * Not modelled (STUCK): files, explicit locales.
 */
package java.io;

import java.nio.charset.Charset;
import java.util.Locale;

public class PrintWriter extends Writer {
    protected Writer out;
    private final boolean autoFlush;
    private boolean trouble = false;
    private PrintStream psOut = null;

    public PrintWriter(Writer out) {
        this(out, false);
    }

    public PrintWriter(Writer out, boolean autoFlush) {
        super(out);
        this.out = out;
        this.autoFlush = autoFlush;
    }

    public PrintWriter(OutputStream out) {
        this(out, false);
    }

    public PrintWriter(OutputStream out, boolean autoFlush) {
        this(out, autoFlush, out instanceof PrintStream ? ((PrintStream) out).charset() : Charset.defaultCharset());
    }

    public PrintWriter(OutputStream out, boolean autoFlush, Charset charset) {
        this(new BufferedWriter(new OutputStreamWriter(out, charset)), autoFlush);
        if (out instanceof PrintStream) psOut = (PrintStream) out;
    }

    public PrintWriter(String fileName) throws FileNotFoundException {
        this(noFiles());
    }

    public PrintWriter(String fileName, String csn) throws FileNotFoundException, UnsupportedEncodingException {
        this(noFiles());
    }

    public PrintWriter(String fileName, Charset charset) throws IOException {
        this(noFiles());
    }

    public PrintWriter(File file) throws FileNotFoundException {
        this(noFiles());
    }

    public PrintWriter(File file, String csn) throws FileNotFoundException, UnsupportedEncodingException {
        this(noFiles());
    }

    public PrintWriter(File file, Charset charset) throws IOException {
        this(noFiles());
    }

    private static Writer noFiles() {
        throw ModelIo.unsupported("PrintWriter on a file");
    }

    private void checkOpen() throws IOException {
        if (out == null) throw new IOException("Stream closed");
    }

    private void failed(IOException x) {
        if (x instanceof InterruptedIOException) throw ModelIo.unsupported("InterruptedIOException in a PrintWriter");
        trouble = true;
    }

    public void flush() {
        synchronized (lock) {
            try {
                checkOpen();
                out.flush();
            } catch (IOException x) {
                trouble = true;
            }
        }
    }

    public void close() {
        synchronized (lock) {
            try {
                if (out != null) {
                    out.close();
                    out = null;
                }
            } catch (IOException x) {
                trouble = true;
            }
        }
    }

    public boolean checkError() {
        if (out != null) flush();
        if (out instanceof PrintWriter) return ((PrintWriter) out).checkError();
        if (psOut != null) return psOut.checkError();
        return trouble;
    }

    protected void setError() {
        trouble = true;
    }

    protected void clearError() {
        trouble = false;
    }

    public void write(int c) {
        synchronized (lock) {
            try {
                checkOpen();
                out.write(c);
            } catch (IOException x) {
                failed(x);
            }
        }
    }

    public void write(char[] buf, int off, int len) {
        synchronized (lock) {
            try {
                checkOpen();
                out.write(buf, off, len);
            } catch (IOException x) {
                failed(x);
            }
        }
    }

    public void write(char[] buf) {
        if (buf == null) throw ModelIo.arrayLengthOfNull("buf");
        write(buf, 0, buf.length);
    }

    public void write(String s, int off, int len) {
        synchronized (lock) {
            try {
                checkOpen();
                out.write(s, off, len);
            } catch (IOException x) {
                failed(x);
            }
        }
    }

    public void write(String s) {
        if (s == null) throw ModelIo.invokeOnNull("String.length()", "s");
        write(s, 0, s.length());
    }

    private void newLine() {
        synchronized (lock) {
            try {
                checkOpen();
                out.write(ModelIo.LINE_SEPARATOR);
                if (autoFlush) out.flush();
            } catch (IOException x) {
                failed(x);
            }
        }
    }

    public void print(boolean b) {
        write(String.valueOf(b));
    }

    public void print(char c) {
        write(c);
    }

    public void print(int i) {
        write(String.valueOf(i));
    }

    public void print(long l) {
        write(String.valueOf(l));
    }

    public void print(float f) {
        write(String.valueOf(f));
    }

    public void print(double d) {
        write(String.valueOf(d));
    }

    public void print(char[] s) {
        write(s);
    }

    public void print(String s) {
        write(String.valueOf(s));
    }

    public void print(Object obj) {
        write(String.valueOf(obj));
    }

    public void println() {
        newLine();
    }

    public void println(boolean x) {
        synchronized (lock) {
            print(x);
            println();
        }
    }

    public void println(char x) {
        synchronized (lock) {
            print(x);
            println();
        }
    }

    public void println(int x) {
        synchronized (lock) {
            print(x);
            println();
        }
    }

    public void println(long x) {
        synchronized (lock) {
            print(x);
            println();
        }
    }

    public void println(float x) {
        synchronized (lock) {
            print(x);
            println();
        }
    }

    public void println(double x) {
        synchronized (lock) {
            print(x);
            println();
        }
    }

    public void println(char[] x) {
        synchronized (lock) {
            print(x);
            println();
        }
    }

    public void println(String x) {
        synchronized (lock) {
            print(x);
            println();
        }
    }

    public void println(Object x) {
        String s = String.valueOf(x);
        synchronized (lock) {
            print(s);
            println();
        }
    }

    public PrintWriter printf(String format, Object... args) {
        return format(format, args);
    }

    public PrintWriter printf(Locale l, String format, Object... args) {
        return format(l, format, args);
    }

    /** Whether the wrapped writer w cannot tell one write of n chars from the Formatter's
     *  piecewise appends of the same text (no write reaches a writer that could see the pieces
     *  or fail between them). */
    private static boolean seesOneWrite(Writer w, int n) {
        Class<?> c = w.getClass();
        if (c == StringWriter.class || c == CharArrayWriter.class) return true;
        if (c == BufferedWriter.class) return ((BufferedWriter) w).holds$(n) || ((BufferedWriter) w).intoTextSink$();
        if (c == PrintWriter.class) {
            Writer inner = ((PrintWriter) w).out;
            return inner == null || seesOneWrite(inner, n);
        }
        return false;
    }

    public PrintWriter format(String format, Object... args) {
        synchronized (lock) {
            try {
                checkOpen();
                StringBuilder text = new StringBuilder();
                try {
                    new java.util.Formatter(text).format(format, args);
                } finally {
                    if (text.length() > 0) {
                        if (getClass() != PrintWriter.class || !seesOneWrite(out, text.length()))
                            throw ModelIo.unsupported("PrintWriter.format onto a writer that may see the Formatter's pieces");
                        write(text.toString());
                    }
                }
                if (autoFlush) out.flush();
            } catch (IOException x) {
                failed(x);
            }
        }
        return this;
    }

    public PrintWriter format(Locale l, String format, Object... args) {
        throw ModelIo.unsupported("PrintWriter.format with an explicit locale");
    }

    public PrintWriter append(CharSequence csq) {
        write(ModelIo.valueOf(csq));
        return this;
    }

    public PrintWriter append(CharSequence csq, int start, int end) {
        if (csq == null) csq = "null";
        return append(ModelIo.subSequence(csq, start, end));
    }

    public PrintWriter append(char c) {
        write(c);
        return this;
    }
}

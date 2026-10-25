package org.rocqjvm.jdkmodel;

/** Differential tests of java.lang.Throwable: causes (constructors, initCause and its errors),
 *  suppressed exceptions (addSuppressed, try-with-resources, disabled suppression), messages,
 *  toString of JDK and user exception classes, getLocalizedMessage overrides. */
public final class ExcOps {
    private ExcOps() {
    }

    static int s;
    static int r(int n) { s = s * 1103515245 + 12345; return ((s >>> 8) & 0x7fffff) % n; }

    static class AppEx extends RuntimeException {
        AppEx(String m) { super(m); }
        AppEx(String m, Throwable c) { super(m, c); }
        AppEx(Throwable c) { super(c); }
    }

    static class Localized extends Exception {
        Localized(String m) { super(m); }
        @Override public String getLocalizedMessage() { return "L(" + getMessage() + ")"; }
    }

    static class Quiet extends RuntimeException {
        Quiet(String m, boolean suppression) { super(m, null, suppression, false); }
    }

    static class MsgOverride extends IllegalStateException {
        MsgOverride() { super("orig"); }
        @Override public String getMessage() { return "over"; }
    }

    static final class Res implements AutoCloseable {
        final String name;
        final boolean failClose;
        Res(String name, boolean failClose) { this.name = name; this.failClose = failClose; }
        @Override public void close() { if (failClose) throw new IllegalStateException("close " + name); }
    }

    static Throwable make() {
        switch (r(10)) {
            case 0: return new RuntimeException("rt" + r(3));
            case 1: return new IllegalArgumentException();
            case 2: return new AppEx("app", new IllegalStateException("inner"));
            case 3: return new AppEx(new ArithmeticException("div"));
            case 4: return new AppEx((Throwable) null);
            case 5: return new Localized("loc");
            case 6: return new MsgOverride();
            case 7: return new RuntimeException(new Exception("e"));
            case 8: return new Quiet("q", r(2) == 0);
            default: return new UnsupportedOperationException("uoe", null);
        }
    }

    static String show(Throwable t) {
        if (t == null) return "null";
        return t.toString() + "{" + t.getMessage() + "|" + t.getLocalizedMessage() + "|c=" + (t.getCause() == null ? "-" : t.getCause().toString())
            + "|s=" + t.getSuppressed().length + "}";
    }

    public static String causes(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 5; k++) {
            Throwable t = make();
            try {
                switch (r(6)) {
                    case 0: out.append(show(t)); break;
                    case 1: t.initCause(make()); out.append(show(t)); break;
                    case 2: t.initCause(null); out.append(show(t)); t.initCause(make()); break;
                    case 3: t.initCause(t); break;
                    case 4: out.append(t.initCause(make()) == t); t.initCause(null); break;
                    default: out.append(t.fillInStackTrace() == t).append(show(t.getCause())); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(show(e)).append("<").append(e.getCause() == t).append(">");
            }
            out.append(';');
        }
        return out.toString();
    }

    public static String suppressed(int seed) {
        s = seed;
        StringBuilder out = new StringBuilder();
        for (int k = 0; k < 4; k++) {
            Throwable t = make();
            try {
                switch (r(5)) {
                    case 0: { int n = r(3); for (int i = 0; i < n; i++) t.addSuppressed(make()); out.append(show(t));
                              for (Throwable x : t.getSuppressed()) out.append(',').append(x); break; }
                    case 1: t.addSuppressed(t); break;
                    case 2: t.addSuppressed(null); break;
                    case 3: { try (Res a = new Res("a", r(2) == 0); Res b = new Res("b", r(2) == 0)) {
                                  if (r(2) == 0) throw new AppEx("body");
                                  out.append("ok");
                              } catch (RuntimeException e) {
                                  out.append(show(e));
                                  for (Throwable x : e.getSuppressed()) out.append(',').append(x);
                              }
                              break; }
                    default: t.addSuppressed(new RuntimeException("x")); out.append(t.getSuppressed().length); break;
                }
            } catch (RuntimeException e) {
                out.append('!').append(show(e)).append("<").append(e.getCause() == t).append(">");
            }
            out.append(';');
        }
        return out.toString();
    }
}

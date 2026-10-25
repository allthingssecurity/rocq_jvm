/*
 * rocq-jvm helper (not a JDK class): calling a native method of a loaded class that has no Rocq
 * model makes the machine STUCK, i.e. it makes no claim about the rest of the run. The stream
 * model classes call it on paths that are deliberately not modelled (parallel streams,
 * spliterators, JDK messages that cannot be reproduced exactly, ...).
 * HotSpot never loads this class: it runs the real JDK.
 */
package java.util.stream;

final class ModelStuckS {
    private ModelStuckS() {
    }

    static native RuntimeException unsupported(String what);

    /** STUCK when f is null: the JDK would throw a "helpful" NullPointerException (its message
     *  names the variable) when it dereferences f. */
    static void nn(Object f) {
        if (f == null) throw unsupported("helpful NullPointerException message");
    }

    /** Objects.requireNonNull(x) (no message). */
    static <T> T req(T x) {
        if (x == null) throw new NullPointerException();
        return x;
    }
}

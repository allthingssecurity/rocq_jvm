/*
 * rocq-jvm helper (not a JDK class): calling a native method of a loaded class that has no Rocq
 * model makes the machine STUCK ("no model for java/util/ModelStuck.unsupported..."), i.e. the
 * machine makes no claim about the rest of the run.  The model classes call it on paths that are
 * not modelled (instead of throwing an exception the real JDK would not throw).
 * HotSpot never loads this class: it runs the real JDK.
 */
package java.util;

final class ModelStuck {
    private ModelStuck() {
    }

    static native RuntimeException unsupported(String what);
}

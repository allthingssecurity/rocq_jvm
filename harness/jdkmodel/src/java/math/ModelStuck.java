/*
 * rocq-jvm helper (not a JDK class): calling a native method that has no Rocq model makes the
 * machine STUCK ("no model for java/math/ModelStuck.unsupported..."), i.e. the machine makes no
 * claim about the rest of the run. The java.math model classes call it on paths that are not
 * modelled. (java.util.ModelStuck is package-private, so java.math has its own.)
 * HotSpot never loads this class: it runs the real JDK.
 */
package java.math;

final class ModelStuck {
    private ModelStuck() {
    }

    static native RuntimeException unsupported(String what);
}

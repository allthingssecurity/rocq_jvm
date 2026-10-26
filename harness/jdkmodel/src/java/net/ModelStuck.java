/*
 * rocq-jvm helper (not a JDK class): calling a native method that has no Rocq model makes the
 * machine STUCK ("model class: <reason>"), i.e. the machine makes no claim about the rest of the
 * run. The java.net model classes (URI) call it on paths that are not modelled. (java.util.ModelStuck
 * is package-private, so java.net has its own.) HotSpot never loads this class: it runs the real JDK.
 */
package java.net;

final class ModelStuck {
    private ModelStuck() {
    }

    static native RuntimeException unsupported(String what);
}

/*
 * rocq-jvm helper (not a JDK class): calling a native method that has no Rocq model makes the
 * machine STUCK ("model class: <reason>"), i.e. no claim about the rest of the run. The
 * java.time.format model classes call it on paths that are not modelled. HotSpot never loads it.
 */
package java.time.format;

final class ModelStuckFormat {
    private ModelStuckFormat() {
    }

    static native RuntimeException unsupported(String what);
}

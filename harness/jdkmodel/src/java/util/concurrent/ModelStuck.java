/*
 * rocq-jvm helper (not a JDK class), as java.util.ModelStuck: calling this native method makes
 * the machine STUCK ("no model for java/util/concurrent/ModelStuck.unsupported..."), so the
 * machine makes no claim about the rest of the run.  HotSpot never loads this class.
 */
package java.util.concurrent;

final class ModelStuck {
    private ModelStuck() {
    }

    static native RuntimeException unsupported(String what);
}

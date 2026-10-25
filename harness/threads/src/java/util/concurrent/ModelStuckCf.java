/*
 * rocq-jvm helper (not a JDK class) for the CompletableFuture / StampedLock models (clean-room,
 * Apache-2.0): calling this native method, which has no Rocq model, makes the machine STUCK
 * ("no model for java/util/concurrent/ModelStuckCf.unsupported..."), so the machine makes no claim
 * about the rest of the run. HotSpot never loads this class: it runs the real JDK.
 */
package java.util.concurrent;

public final class ModelStuckCf {
    private ModelStuckCf() { }

    public static native RuntimeException unsupported(String what);
}

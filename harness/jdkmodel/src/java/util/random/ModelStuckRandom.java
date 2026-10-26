/* rocq-jvm helper (not a JDK class): a native method without a Rocq model, so that a call makes
 * the machine STUCK (no claim), as java.util.ModelStuck. HotSpot never loads this class. */
package java.util.random;

final class ModelStuckRandom {
    private ModelStuckRandom() {
    }

    static native RuntimeException unsupported(String what);
}

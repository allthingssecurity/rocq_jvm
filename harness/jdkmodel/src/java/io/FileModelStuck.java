/*
 * rocq-jvm helper (not a JDK class) for the java.io.File model: calling a native method that has no
 * Rocq model makes the machine STUCK ("model class: <reason>"; the machine intercepts every class
 * whose name contains "ModelStuck"), i.e. no claim about the rest of the run. HotSpot never loads
 * this class: it runs the real JDK.
 */
package java.io;

final class FileModelStuck {
    private FileModelStuck() {
    }

    static native RuntimeException unsupported(String what);
}

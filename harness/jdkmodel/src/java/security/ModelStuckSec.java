/*
 * rocq-jvm: the java.security model classes' "no claim" helper (native; theories/Jdk/Jdk.v makes a
 * call STUCK with the reason).
 */
package java.security;

final class ModelStuckSec {
    private ModelStuckSec() {
    }

    static native RuntimeException unsupported(String what);
}

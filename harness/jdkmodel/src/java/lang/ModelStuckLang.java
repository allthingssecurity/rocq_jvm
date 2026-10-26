/*
 * rocq-jvm: the java.lang model classes' "no claim" helper (native; theories/Jdk/Jdk.v makes a call
 * STUCK with the reason).
 */
package java.lang;

final class ModelStuckLang {
    private ModelStuckLang() {
    }

    static native RuntimeException unsupported(String what);
}

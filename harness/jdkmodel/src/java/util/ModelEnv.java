/*
 * rocq-jvm helper (not a JDK class): values that the JDK draws from the outside world once per
 * run (seeds), supplied by the model's environment (jenv.j_seed in theories/Jdk/Jdk.v), so a
 * theorem states them. seed(0) = the SALT32L of ImmutableCollections (Set.of/Map.of iteration
 * order). HotSpot never loads this class.
 */
package java.util;

final class ModelEnv {
    private ModelEnv() {
    }

    static native long seed(int which);
}

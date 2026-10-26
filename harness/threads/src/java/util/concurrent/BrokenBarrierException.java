/* rocq-jvm model of java.util.concurrent.BrokenBarrierException (clean-room, Apache-2.0). */
package java.util.concurrent;

public class BrokenBarrierException extends Exception {
    private static final long serialVersionUID = 7117394618823254244L;

    public BrokenBarrierException() { }

    public BrokenBarrierException(String message) {
        super(message);
    }

    // Throwable.toString (the machine's covers only classes it does not load)
    @Override public String toString() { String m = getLocalizedMessage(); return m != null ? getClass().getName() + ": " + m : getClass().getName(); }
}

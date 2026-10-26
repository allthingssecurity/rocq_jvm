/*
 * rocq-jvm model of java.math.MathContext (clean-room, Apache-2.0): precision and rounding mode,
 * the four constants, the String form "precision=N roundingMode=MODE" and its parser (every
 * malformation is "bad string format"), equals and hashCode (precision + 59 * the rounding mode's
 * identity hash code, as in JDK 21).
 */
package java.math;

public final class MathContext implements java.io.Serializable {
    private static final long serialVersionUID = 5579720004786848255L;

    public static final MathContext UNLIMITED = new MathContext(0, RoundingMode.HALF_UP);
    public static final MathContext DECIMAL32 = new MathContext(7, RoundingMode.HALF_EVEN);
    public static final MathContext DECIMAL64 = new MathContext(16, RoundingMode.HALF_EVEN);
    public static final MathContext DECIMAL128 = new MathContext(34, RoundingMode.HALF_EVEN);

    final int precision;
    final RoundingMode roundingMode;

    public MathContext(int setPrecision) {
        this(setPrecision, RoundingMode.HALF_UP);
    }

    public MathContext(int setPrecision, RoundingMode setRoundingMode) {
        if (setPrecision < 0) throw new IllegalArgumentException("Digits < 0");
        if (setRoundingMode == null) throw new NullPointerException("null RoundingMode");
        precision = setPrecision;
        roundingMode = setRoundingMode;
    }

    public MathContext(String val) {
        if (val == null) throw new NullPointerException("null String");
        int p;
        RoundingMode rm = null;
        boolean ok = val.startsWith("precision=");
        int fence = ok ? val.indexOf(' ') : -1;
        p = 0;
        if (ok && fence < 10) ok = false;
        if (ok) {
            try {
                p = Integer.parseInt(val.substring(10, fence));
            } catch (NumberFormatException e) {
                ok = false;
            }
        }
        if (ok && !val.startsWith("roundingMode=", fence + 1)) ok = false;
        if (ok) {
            String name = val.substring(fence + 14);
            RoundingMode[] all = RoundingMode.values();
            for (int i = 0; i < all.length; i++) {
                if (all[i].name().equals(name)) rm = all[i];
            }
            if (rm == null) ok = false;
        }
        if (!ok) throw new IllegalArgumentException("bad string format");
        if (p < 0) throw new IllegalArgumentException("Digits < 0");
        precision = p;
        roundingMode = rm;
    }

    public int getPrecision() {
        return precision;
    }

    public RoundingMode getRoundingMode() {
        return roundingMode;
    }

    public boolean equals(Object x) {
        if (!(x instanceof MathContext)) return false;
        MathContext mc = (MathContext) x;
        return mc.precision == precision && mc.roundingMode == roundingMode;
    }

    public int hashCode() {
        return precision + roundingMode.hashCode() * 59;
    }

    public String toString() {
        return "precision=" + precision + " roundingMode=" + roundingMode.toString();
    }
}

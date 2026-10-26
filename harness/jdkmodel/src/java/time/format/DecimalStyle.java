/* rocq-jvm model of java.time.format.DecimalStyle (clean-room, Apache-2.0): STANDARD and the with*
 * copies of JDK 21, digit conversion, equals/hashCode/toString. of(Locale), ofDefaultLocale and
 * getAvailableLocales need the locale data: STUCK. */
package java.time.format;

import java.util.Locale;
import java.util.Objects;
import java.util.Set;

public final class DecimalStyle {
    public static final DecimalStyle STANDARD = new DecimalStyle('0', '+', '-', '.');

    private final char zeroDigit;
    private final char positiveSign;
    private final char negativeSign;
    private final char decimalSeparator;

    private DecimalStyle(char zeroChar, char positiveSignChar, char negativeSignChar, char decimalPointChar) {
        this.zeroDigit = zeroChar;
        this.positiveSign = positiveSignChar;
        this.negativeSign = negativeSignChar;
        this.decimalSeparator = decimalPointChar;
    }

    public static Set<Locale> getAvailableLocales() {
        throw ModelStuckFormat.unsupported("DecimalStyle.getAvailableLocales: locale data");
    }

    public static DecimalStyle ofDefaultLocale() {
        throw ModelStuckFormat.unsupported("DecimalStyle.ofDefaultLocale: host locale");
    }

    public static DecimalStyle of(Locale locale) {
        Objects.requireNonNull(locale, "locale");
        throw ModelStuckFormat.unsupported("DecimalStyle.of: locale data");
    }

    public char getZeroDigit() {
        return zeroDigit;
    }

    public DecimalStyle withZeroDigit(char zeroDigit) {
        if (zeroDigit == this.zeroDigit) return this;
        return new DecimalStyle(zeroDigit, positiveSign, negativeSign, decimalSeparator);
    }

    public char getPositiveSign() {
        return positiveSign;
    }

    public DecimalStyle withPositiveSign(char positiveSign) {
        if (positiveSign == this.positiveSign) return this;
        return new DecimalStyle(zeroDigit, positiveSign, negativeSign, decimalSeparator);
    }

    public char getNegativeSign() {
        return negativeSign;
    }

    public DecimalStyle withNegativeSign(char negativeSign) {
        if (negativeSign == this.negativeSign) return this;
        return new DecimalStyle(zeroDigit, positiveSign, negativeSign, decimalSeparator);
    }

    public char getDecimalSeparator() {
        return decimalSeparator;
    }

    public DecimalStyle withDecimalSeparator(char decimalSeparator) {
        if (decimalSeparator == this.decimalSeparator) return this;
        return new DecimalStyle(zeroDigit, positiveSign, negativeSign, decimalSeparator);
    }

    int convertToDigit(char ch) {
        int val = ch - zeroDigit;
        return (val >= 0 && val <= 9) ? val : -1;
    }

    String convertNumberToI18N(String numericText) {
        if (zeroDigit == '0') return numericText;
        int diff = zeroDigit - '0';
        char[] array = numericText.toCharArray();
        for (int i = 0; i < array.length; i++) array[i] = (char) (array[i] + diff);
        return new String(array);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof DecimalStyle)) return false;
        DecimalStyle o = (DecimalStyle) obj;
        return zeroDigit == o.zeroDigit && positiveSign == o.positiveSign && negativeSign == o.negativeSign
            && decimalSeparator == o.decimalSeparator;
    }

    @Override
    public int hashCode() {
        return zeroDigit + positiveSign + negativeSign + decimalSeparator;
    }

    @Override
    public String toString() {
        return "DecimalStyle[" + zeroDigit + positiveSign + negativeSign + decimalSeparator + "]";
    }
}

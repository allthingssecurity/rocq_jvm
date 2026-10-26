/*
 * rocq-jvm model of java.util.Locale (clean-room, Apache-2.0), from the Javadoc: a language
 * (lower-cased, the legacy codes iw/in/ji mapped to he/id/yi), a region (upper-cased) and a variant
 * (as given), with no script and no extensions. The constants (ENGLISH, US, ROOT, ...), getters,
 * toString (JDK 21's rules for empty parts), equals, hashCode (the JDK's BaseLocale hash),
 * toLanguageTag for a well-formed language and region, forLanguageTag for language[-region] tags,
 * and the static helpers below used by the String and Formatter models.
 * Not modelled (STUCK): the default locale (getDefault/setDefault depend on the host), scripts and
 * extensions (Locale.Builder, the ja_JP_JP / th_TH_TH compatibility locales), display names, ISO3
 * codes, available locales, language ranges, other language tags.
 */
package java.util;

public final class Locale implements Cloneable, java.io.Serializable {
    private static final long serialVersionUID = 9149081749638150636L;

    public static final Locale ENGLISH = new Locale("en", "", 0);
    public static final Locale FRENCH = new Locale("fr", "", 0);
    public static final Locale GERMAN = new Locale("de", "", 0);
    public static final Locale ITALIAN = new Locale("it", "", 0);
    public static final Locale JAPANESE = new Locale("ja", "", 0);
    public static final Locale KOREAN = new Locale("ko", "", 0);
    public static final Locale CHINESE = new Locale("zh", "", 0);
    public static final Locale SIMPLIFIED_CHINESE = new Locale("zh", "CN", 0);
    public static final Locale TRADITIONAL_CHINESE = new Locale("zh", "TW", 0);
    public static final Locale FRANCE = new Locale("fr", "FR", 0);
    public static final Locale GERMANY = new Locale("de", "DE", 0);
    public static final Locale ITALY = new Locale("it", "IT", 0);
    public static final Locale JAPAN = new Locale("ja", "JP", 0);
    public static final Locale KOREA = new Locale("ko", "KR", 0);
    public static final Locale UK = new Locale("en", "GB", 0);
    public static final Locale US = new Locale("en", "US", 0);
    public static final Locale CANADA = new Locale("en", "CA", 0);
    public static final Locale CANADA_FRENCH = new Locale("fr", "CA", 0);
    public static final Locale ROOT = new Locale("", "", 0);
    public static final Locale CHINA = SIMPLIFIED_CHINESE;
    public static final Locale PRC = SIMPLIFIED_CHINESE;
    public static final Locale TAIWAN = TRADITIONAL_CHINESE;

    public static final char PRIVATE_USE_EXTENSION = 'x';
    public static final char UNICODE_LOCALE_EXTENSION = 'u';

    private static final Locale[] CONSTANTS = {ENGLISH, FRENCH, GERMAN, ITALIAN, JAPANESE, KOREAN, CHINESE,
        SIMPLIFIED_CHINESE, TRADITIONAL_CHINESE, FRANCE, GERMANY, ITALY, JAPAN, KOREA, UK, US, CANADA,
        CANADA_FRENCH, ROOT};

    private final String language;
    private final String region;
    private final String variant;
    private transient int hashCodeValue;

    private Locale(String language, String region, int constant) {
        this.language = language;
        this.region = region;
        this.variant = "";
    }

    @Deprecated
    public Locale(String language, String country, String variant) {
        if (language == null || country == null || variant == null) throw new NullPointerException();
        String l = convertOldISOCodes(lower(language));
        String r = upper(country);
        if ((l.equals("ja") && r.equals("JP") && variant.equals("JP")) || (l.equals("th") && r.equals("TH") && variant.equals("TH")))
            throw ModelStuck.unsupported("Locale: the " + l + "_" + r + "_" + variant + " compatibility locale (a Unicode extension)");
        this.language = l;
        this.region = r;
        this.variant = variant;
    }

    @Deprecated
    public Locale(String language, String country) {
        this(language, country, "");
    }

    @Deprecated
    public Locale(String language) {
        this(language, "", "");
    }

    public static Locale of(String language, String country, String variant) {
        if (language == null || country == null || variant == null) throw new NullPointerException();
        return cached(new Locale(language, country, variant));
    }

    public static Locale of(String language, String country) {
        return of(language, country, "");
    }

    public static Locale of(String language) {
        return of(language, "", "");
    }

    /** Locale.getInstance: the constant with the same parts, else the cache's locale. */
    private static final ArrayList<Locale> CACHE = new ArrayList<>();

    private static Locale cached(Locale l) {
        for (Locale c : CONSTANTS) if (c.equals(l)) return c;
        for (Locale c : CACHE) if (c.equals(l)) return c;
        CACHE.add(l);
        return l;
    }

    /** LocaleUtils.toLowerString / toUpperString: ASCII case only. */
    private static String lower(String s) {
        StringBuilder b = new StringBuilder(s.length());
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            b.append(c >= 'A' && c <= 'Z' ? (char) (c + 32) : c);
        }
        return b.toString();
    }

    private static String upper(String s) {
        StringBuilder b = new StringBuilder(s.length());
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            b.append(c >= 'a' && c <= 'z' ? (char) (c - 32) : c);
        }
        return b.toString();
    }

    private static String convertOldISOCodes(String l) {
        switch (l) {
            case "iw": return "he";
            case "in": return "id";
            case "ji": return "yi";
            default: return l;
        }
    }

    public static Locale getDefault() {
        throw ModelStuck.unsupported("Locale.getDefault: the host's default locale");
    }

    public static void setDefault(Locale newLocale) {
        throw ModelStuck.unsupported("Locale.setDefault");
    }

    public String getLanguage() {
        return language;
    }

    public String getCountry() {
        return region;
    }

    public String getVariant() {
        return variant;
    }

    public String getScript() {
        return "";
    }

    public boolean hasExtensions() {
        return false;
    }

    public Locale stripExtensions() {
        return this;
    }

    public final String toString() {
        boolean l = !language.isEmpty();
        boolean r = !region.isEmpty();
        boolean v = !variant.isEmpty();
        StringBuilder result = new StringBuilder(language);
        if (r || (l && v)) result.append('_').append(region);
        if (v && (l || r)) result.append('_').append(variant);
        return result.toString();
    }

    private static boolean alpha(String s, int min, int max) {
        if (s.length() < min || s.length() > max) return false;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            if (!((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))) return false;
        }
        return true;
    }

    private static boolean digits(String s, int n) {
        if (s.length() != n) return false;
        for (int i = 0; i < n; i++) if (s.charAt(i) < '0' || s.charAt(i) > '9') return false;
        return true;
    }

    public String toLanguageTag() {
        if (!variant.isEmpty()) throw ModelStuck.unsupported("Locale.toLanguageTag with a variant");
        String l;
        if (language.isEmpty()) l = "und";
        else if (alpha(language, 2, 8) && language.length() != 4) l = language;
        else throw ModelStuck.unsupported("Locale.toLanguageTag of an ill-formed language");
        if (region.isEmpty()) return l;
        if (alpha(region, 2, 2) || digits(region, 3)) return l + "-" + region;
        throw ModelStuck.unsupported("Locale.toLanguageTag of an ill-formed region");
    }

    public static Locale forLanguageTag(String languageTag) {
        if (languageTag == null) throw new NullPointerException("Cannot invoke \"String.length()\" because \"s\" is null");
        int dash = languageTag.indexOf('-');
        String l = dash < 0 ? languageTag : languageTag.substring(0, dash);
        String r = dash < 0 ? "" : languageTag.substring(dash + 1);
        if (!alpha(l, 2, 3) || !((dash < 0 && r.isEmpty()) || alpha(r, 2, 2) || digits(r, 3)))
            throw ModelStuck.unsupported("Locale.forLanguageTag: a tag other than language[-region]");
        if (lower(l).equals("und")) l = "";
        return cached(new Locale(l, r, ""));
    }

    public Object clone() {
        throw ModelStuck.unsupported("Locale.clone");
    }

    @Override
    public int hashCode() {
        int hc = hashCodeValue;
        if (hc == 0) {
            hc = language.hashCode();
            hc = 31 * hc;          // script ""
            hc = 31 * hc + region.hashCode();
            hc = 31 * hc + variant.hashCode();
            hashCodeValue = hc;
        }
        return hc;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof Locale)) return false;
        Locale o = (Locale) obj;
        return language.equals(o.language) && region.equals(o.region) && variant.equals(o.variant);
    }

    public String getDisplayName() {
        throw ModelStuck.unsupported("Locale display names");
    }

    public String getDisplayLanguage() {
        throw ModelStuck.unsupported("Locale display names");
    }

    public String getDisplayCountry() {
        throw ModelStuck.unsupported("Locale display names");
    }

    public String getISO3Language() {
        throw ModelStuck.unsupported("Locale ISO3 codes");
    }

    public String getISO3Country() {
        throw ModelStuck.unsupported("Locale ISO3 codes");
    }

    public static Locale[] getAvailableLocales() {
        throw ModelStuck.unsupported("Locale.getAvailableLocales");
    }

    /** String.toLowerCase/toUpperCase(Locale): null throws as the JDK does; the tr/az/lt rules are
     *  not modelled (the String models use the locale-independent mapping). */
    public static void caseCheck$(Locale l) {
        if (l == null) throw new NullPointerException();
        String g = l.language;
        if (g.equals("tr") || g.equals("az") || g.equals("lt"))
            throw ModelStuck.unsupported("case mapping in the " + g + " locale");
    }

    /** Formatter / String.format(Locale, ...): null (no localization), the root locale and English in
     *  the US, the UK and Canada format as the model Formatter does (digits 0-9, '.' and ','). */
    public static void formatCheck$(Locale l) {
        if (l == null) return;
        if (!l.variant.isEmpty()) throw ModelStuck.unsupported("Formatter: locale " + l);
        if (l.language.isEmpty() && l.region.isEmpty()) return;
        if (l.language.equals("en") && (l.region.isEmpty() || l.region.equals("US") || l.region.equals("GB") || l.region.equals("CA"))) return;
        throw ModelStuck.unsupported("Formatter: locale " + l);
    }
}

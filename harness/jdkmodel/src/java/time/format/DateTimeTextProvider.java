/*
 * rocq-jvm model of java.time.format.DateTimeTextProvider (clean-room, Apache-2.0): the texts of
 * month, day-of-week, AM/PM and era for the English locales "en" and "en_US" only (JDK 21's CLDR data
 * for them, checked against HotSpot), stored as the JDK's LocaleStore (value -> text per style; the
 * parsable lists longest text first, built with the JDK's HashMap/sort steps so that a narrow letter
 * shared by several values maps to the same value as in the JDK). Every other locale, the host's
 * default locale and non-ISO chronologies: STUCK. Fields without texts answer null, as in the JDK.
 */
package java.time.format;

import java.time.chrono.Chronology;
import java.time.chrono.IsoChronology;
import java.time.temporal.ChronoField;
import java.time.temporal.TemporalField;
import java.util.AbstractMap.SimpleImmutableEntry;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Map.Entry;

class DateTimeTextProvider {
    private static final Comparator<Entry<String, Long>> COMPARATOR = new Comparator<Entry<String, Long>>() {
        @Override
        public int compare(Entry<String, Long> obj1, Entry<String, Long> obj2) {
            return obj2.getKey().length() - obj1.getKey().length();
        }
    };

    private static final DateTimeTextProvider INSTANCE = new DateTimeTextProvider();
    private static LocaleStore[] english;

    DateTimeTextProvider() {
    }

    static DateTimeTextProvider getInstance() {
        return INSTANCE;
    }

    public String getText(TemporalField field, long value, TextStyle style, Locale locale) {
        Object store = findStore(field, locale);
        if (store instanceof LocaleStore) return ((LocaleStore) store).getText(value, style);
        return null;
    }

    public String getText(Chronology chrono, TemporalField field, long value, TextStyle style, Locale locale) {
        if (chrono == IsoChronology.INSTANCE || !(field instanceof ChronoField)) return getText(field, value, style, locale);
        throw ModelStuckFormat.unsupported("DateTimeTextProvider: texts of a non-ISO chronology");
    }

    public Iterator<Entry<String, Long>> getTextIterator(TemporalField field, TextStyle style, Locale locale) {
        Object store = findStore(field, locale);
        if (store instanceof LocaleStore) return ((LocaleStore) store).getTextIterator(style);
        return null;
    }

    public Iterator<Entry<String, Long>> getTextIterator(Chronology chrono, TemporalField field, TextStyle style,
                                                         Locale locale) {
        if (chrono == IsoChronology.INSTANCE || !(field instanceof ChronoField)) return getTextIterator(field, style, locale);
        throw ModelStuckFormat.unsupported("DateTimeTextProvider: texts of a non-ISO chronology");
    }

    static boolean isEnglish(Locale locale) {
        return locale != null && locale.getLanguage().equals("en") && locale.getVariant().isEmpty()
            && (locale.getCountry().isEmpty() || locale.getCountry().equals("US"));
    }

    private static final String[] MONTHS = {"January", "February", "March", "April", "May", "June", "July", "August",
        "September", "October", "November", "December"};
    private static final String[] DAYS = {"Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"};

    private Object findStore(TemporalField field, Locale locale) {
        int k = field == ChronoField.ERA ? 0 : field == ChronoField.MONTH_OF_YEAR ? 1
            : field == ChronoField.DAY_OF_WEEK ? 2 : field == ChronoField.AMPM_OF_DAY ? 3 : -1;
        if (k < 0) {
            if (field instanceof ChronoField) return "";
            throw ModelStuckFormat.unsupported("DateTimeTextProvider: texts of a non-ChronoField field");
        }
        if (locale == null) throw ModelStuckFormat.unsupported("DateTimeTextProvider: the host's default locale");
        if (!isEnglish(locale)) throw ModelStuckFormat.unsupported("DateTimeTextProvider: texts of locale " + locale);
        if (english == null) english = new LocaleStore[4];
        if (english[k] == null) english[k] = createStore(k);
        return english[k];
    }

    private static LocaleStore createStore(int k) {
        Map<TextStyle, Map<Long, String>> styleMap = new HashMap<>();
        for (TextStyle style : TextStyle.values()) {
            Map<Long, String> map = new HashMap<>();
            int width = style.ordinal() >> 1; // 0 full, 1 short, 2 narrow
            if (k == 0 || k == 3) {
                if (style.isStandalone()) continue;
                String[] names = k == 0
                    ? (width == 0 ? new String[] {"Before Christ", "Anno Domini"} : width == 1 ? new String[] {"BC", "AD"}
                        : new String[] {"B", "A"})
                    : (width == 2 ? new String[] {"a", "p"} : new String[] {"AM", "PM"});
                for (int v = 0; v < 2; v++) map.put((long) v, names[v]);
            } else {
                String[] full = k == 1 ? MONTHS : DAYS;
                for (int i = 0; i < full.length; i++) {
                    String name = width == 0 ? full[i] : width == 1 ? full[i].substring(0, 3) : full[i].substring(0, 1);
                    map.put((long) (i + 1), name);
                }
            }
            if (!map.isEmpty()) styleMap.put(style, map);
        }
        return new LocaleStore(styleMap);
    }

    static final class LocaleStore {
        private final Map<TextStyle, Map<Long, String>> valueTextMap;
        private final Map<TextStyle, List<Entry<String, Long>>> parsable;

        LocaleStore(Map<TextStyle, Map<Long, String>> valueTextMap) {
            this.valueTextMap = valueTextMap;
            Map<TextStyle, List<Entry<String, Long>>> map = new HashMap<>();
            List<Entry<String, Long>> allList = new ArrayList<>();
            for (Map.Entry<TextStyle, Map<Long, String>> vtmEntry : valueTextMap.entrySet()) {
                Map<String, Entry<String, Long>> reverse = new HashMap<>();
                for (Map.Entry<Long, String> entry : vtmEntry.getValue().entrySet()) {
                    reverse.put(entry.getValue(), new SimpleImmutableEntry<>(entry.getValue(), entry.getKey()));
                }
                List<Entry<String, Long>> list = new ArrayList<>(reverse.values());
                list.sort(COMPARATOR);
                map.put(vtmEntry.getKey(), list);
                allList.addAll(list);
                map.put(null, allList);
            }
            allList.sort(COMPARATOR);
            this.parsable = map;
        }

        String getText(long value, TextStyle style) {
            Map<Long, String> map = valueTextMap.get(style);
            return map != null ? map.get(value) : null;
        }

        Iterator<Entry<String, Long>> getTextIterator(TextStyle style) {
            List<Entry<String, Long>> list = parsable.get(style);
            return list != null ? list.iterator() : null;
        }
    }
}

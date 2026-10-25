import java.util.Iterator;
import java.util.NoSuchElementException;
import org.apache.camel.util.FilterIterator;

/** Finite, ordinary Iterator input for kernel execution; no replacement Camel methods. */
public final class FilterScenario {
    static final class Backing implements Iterator<String> {
        String[] items = {"a", "b", "c"};
        int size = 3, cursor, last = -1;
        public boolean hasNext() { return cursor < size; }
        public String next() {
            if (!hasNext()) throw new NoSuchElementException();
            last = cursor;
            return items[cursor++];
        }
        public void remove() {
            if (last < 0) throw new IllegalStateException();
            for (int i = last; i + 1 < size; i++) items[i] = items[i + 1];
            items[--size] = null;
            cursor = last;
            last = -1;
        }
        String remaining() { return items[0] + items[1]; }
    }
    public static String afterLookahead(int wrap) {
        Backing b = new Backing();
        Iterator<String> it = wrap == 0 ? b : new FilterIterator<>(b);
        if (!"a".equals(it.next())) return "bad-first";
        if (!it.hasNext()) return "bad-hasNext";
        it.remove();
        return b.remaining();
    }
    public static int beforeNext(int wrap) {
        Backing b = new Backing();
        Iterator<String> it = wrap == 0 ? b : new FilterIterator<>(b);
        it.hasNext();
        try { it.remove(); return b.size; }
        catch (IllegalStateException expected) { return -1; }
    }
}

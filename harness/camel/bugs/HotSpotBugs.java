import java.time.Duration;
import java.util.*;
import org.apache.camel.util.FilterIterator;
import org.apache.camel.util.TimeUtils;
public class HotSpotBugs {
    public static void main(String[] args) {
        List<String> data = new ArrayList<>(List.of("a", "b", "c"));
        Iterator<String> it = new FilterIterator<>(data.iterator());
        System.out.println("returned=" + it.next());
        System.out.println("hasNext=" + it.hasNext());
        it.remove();
        System.out.println("remaining=" + data + " expected=[b, c]");
        System.out.println("nextAfterRemove=" + it.next());
        data = new ArrayList<>(List.of("a", "b", "c"));
        it = new FilterIterator<>(data.iterator());
        it.hasNext();
        try { it.remove(); System.out.println("removeBeforeNext=accepted remaining=" + data); }
        catch (IllegalStateException e) { System.out.println("removeBeforeNext=rejected"); }
        for (long n : new long[]{-1000000001L,-1000000000L,-999999999L,-1L,0L,1L,1000000000L}) {
            Duration d=Duration.ofNanos(n);
            System.out.println("nanos="+n+" seconds="+d.getSeconds()+" nanoField="+d.getNano()
                +" camelPositive="+TimeUtils.isPositive(d)+" jdkPositive="+d.isPositive());
        }
        for(int wrap=0; wrap<2; wrap++) {
            System.out.println("formalDriver wrap="+wrap+" remaining="+FilterScenario.afterLookahead(wrap)
                +" beforeNext="+FilterScenario.beforeNext(wrap));
        }
    }
}

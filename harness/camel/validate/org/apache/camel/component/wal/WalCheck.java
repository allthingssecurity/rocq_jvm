package org.apache.camel.component.wal;

/** CAMEL-26088: TransactionLog.update marks the wrong entry / rejects a live one. Must live in the
 *  package because TransactionLog is package-private. Prints, for (cap, n, k), which entry update(k) marked. */
public class WalCheck {
    static int check(int cap, int n, int k) {
        TransactionLog t = new TransactionLog(cap);
        TransactionLog.LayerInfo[] infos = new TransactionLog.LayerInfo[n];
        LogEntry[] es = new LogEntry[n];
        for (int i = 0; i < n; i++) {
            es[i] = new LogEntry(LogEntry.EntryState.NEW, i, new byte[0], 0, new byte[0]);
            infos[i] = t.add(es[i]);
        }
        t.update(infos[k], LogEntry.EntryState.FAILED);
        for (int i = 0; i < n; i++) if (es[i].getEntryState() == LogEntry.EntryState.FAILED) return i;
        return -1;
    }
    public static void main(String[] a) {
        int[][] cases = {{3, 10, 2}, {4, 9, 5}, {3, 10, 8}};
        for (int[] c : cases) {
            int exp = (c[2] >= c[1] - c[0]) ? c[2] : -1;
            System.out.println("TransactionLog cap=" + c[0] + " adds=" + c[1] + " update(entry " + c[2] + ") marked "
                + check(c[0], c[1], c[2]) + "   expected " + exp + " (-1 = none)");
        }
    }
}

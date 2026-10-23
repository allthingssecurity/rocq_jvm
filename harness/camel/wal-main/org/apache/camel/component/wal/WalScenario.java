package org.apache.camel.component.wal;

/** Test driver (ours, not Camel code): a TransactionLog of capacity cap gets n entries
 *  (entry i has keyMetadata i), then the k-th entry is updated to FAILED through the LayerInfo
 *  that add() returned for it. Returns the keyMetadata of the entry that is FAILED afterwards,
 *  or -1 if none; returns -2 for invalid parameters. The contract: k if entry k is still in the
 *  ring buffer (n - cap <= k < n), else -1. */
class WalScenario {
    static int check(int cap, int n, int k) {
        if (cap < 1 || n < 0 || k < 0 || k >= n || n > 1000 || cap > 1000) return -2;
        TransactionLog t = new TransactionLog(cap);
        TransactionLog.LayerInfo[] infos = new TransactionLog.LayerInfo[n];
        LogEntry[] es = new LogEntry[n];
        for (int i = 0; i < n; i++) {
            LogEntry e = new LogEntry(LogEntry.EntryState.NEW, i, new byte[0], 0, new byte[0]);
            es[i] = e;
            infos[i] = t.add(e);
        }
        t.update(infos[k], LogEntry.EntryState.FAILED);
        for (int i = 0; i < n; i++) if (es[i].getEntryState() == LogEntry.EntryState.FAILED) return es[i].getKeyMetadata();
        return -1;
    }
}

#!/usr/bin/env bash
# Canary: the harness must REPORT mismatches when model and HotSpot run different methods
# (model: Ops.iadd, HotSpot: Ops.isub) and when main and fix canUpdate are compared.
# A differential "agree" without a failing canary is not evidence.
set -uo pipefail
cd "$(dirname "$0")/.."
in=harness/work/canary.in
python3 harness/gen_inputs.py '(II)I' 1000 3 > "$in"
java -Xmx256m -cp harness/work DiffRunner classes/corpus org.rocqjvm.corpus.Ops isub '(II)I' "$in" 2>/dev/null > harness/work/canary.hs
harness/model_main.exe classes/corpus/org/rocqjvm/corpus/Ops.class iadd '(II)I' "$in" 2000000 > harness/work/canary.md
python3 harness/compare.py "$in" harness/work/canary.hs harness/work/canary.md >/dev/null && { echo "CANARY FAILED: iadd vs isub reported as agreeing"; exit 1; }
python3 harness/gen_inputs.py '(IIII)Z' 100000 5 > "$in"
harness/model_main.exe classes/wal-main/org/apache/camel/component/wal/TransactionLog.class canUpdate '(IIII)Z' "$in" 100 > harness/work/canary.a
harness/model_main.exe classes/wal-fix/org/apache/camel/component/wal/TransactionLog.class canUpdate '(IIII)Z' "$in" 100 > harness/work/canary.b
python3 harness/compare.py "$in" harness/work/canary.a harness/work/canary.b | head -1
python3 harness/compare.py "$in" harness/work/canary.a harness/work/canary.b >/dev/null && { echo "CANARY FAILED: main and fix canUpdate agree on all inputs"; exit 1; }
echo "canaries ok: both deliberate differences were detected"

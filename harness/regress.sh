#!/usr/bin/env bash
# Rerun every differential corpus with N inputs per method (default 300) against HotSpot.
#   harness/regress.sh [N] [seed]
# Frame interpreter: phase1, stackops, ops2. Machine: everything else. Thread layer: threads*.
set -uo pipefail
cd "$(dirname "$0")/.."
n=${1:-300}; seed=${2:-1}; rc=0
run() { local mode=$1 f=$2; echo "### $f ($mode)"; MODE=$mode FUEL=${FUEL:-20000000} harness/difftest.sh "$f" "$n" "$seed" | grep -v '^Picked' | grep -E '^[^ ].*inputs=' || true; [[ ${PIPESTATUS[0]} -ne 0 ]] && rc=1; }
for f in phase1 stackops ops2; do run frame harness/targets-$f.txt; done
# Ops2.big is a 28,000-instruction method (goto_w): the extracted loader needs ~45 s to parse it and
# fetch is linear in the code, so about 25 s per loop iteration. 20 inputs keep the run under an hour.
n_all=$n; n=20; run frame harness/targets-ops2big.txt; n=$n_all
for f in heap strs flt lam cim jdkmodel fld sel indy box msg refl refl2 math sync1 lamconv tostr chm tree fmt sort deque regex strregex walscen; do run machine harness/targets-$f.txt; done
for f in threads threads2 threads3 chmthreads sched pool time; do run threads harness/targets-$f.txt; done
exit $rc

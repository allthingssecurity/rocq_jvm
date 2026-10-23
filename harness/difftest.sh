#!/usr/bin/env bash
# Differential test: random inputs through the extracted Rocq model and through HotSpot.
#   harness/difftest.sh <targets-file> <inputs-per-method> [seed]
# targets-file lines: <classdir> <binary class name> <method> <descriptor> [fresh]
#   fresh = this method changes static state: HotSpot uses a new class loader per input
# Appends one line per method to harness/results/<UTC date>.tsv and exits 1 on any mismatch.
# MODE=machine: the Phase 2/3 machine (all classes under <classdir>, fresh state per input; HotSpot
# side then needs FRESH=1 for a fresh class loader per input).
# Resource rules: one JVM at a time, -Xmx512m, niced (the runs are tiny).
set -uo pipefail
cd "$(dirname "$0")/.."
targets=$1; n=$2; seed=${3:-1}
JAVA=${JAVA:-java}
FUEL=${FUEL:-2000000}
mkdir -p harness/results harness/work
res=harness/results/$(date -u +%Y-%m-%d).tsv
[[ -f $res ]] || printf 'time\tclass\tmethod\tdesc\tinputs\tagree\tmismatches\thotspot_exceptions\tmodel_stuck\tseed\n' > "$res"
[[ -x harness/model_main.exe ]] || { echo "build harness/model_main.exe first (harness/build.sh)"; exit 2; }
[[ -f harness/work/DiffRunner.class ]] || javac -d harness/work harness/java/DiffRunner.java 2>/dev/null
rc=0
while read -r dir cls meth desc opt; do
  [[ -z "$dir" || "$dir" == \#* ]] && continue
  f="$dir/${cls//.//}.class"
  tag="$(basename "$dir")-${cls##*.}-$meth"
  in=harness/work/$tag.in
  python3 harness/gen_inputs.py "$desc" "$n" "$seed" > "$in"
  fresh=${FRESH:-}; [[ "${opt:-}" == fresh ]] && fresh=1
  FRESH=$fresh nice "$JAVA" -Xmx512m -cp harness/work:harness/work/slf4j DiffRunner "$dir" "$cls" "$meth" "$desc" "$in" 2>/dev/null > harness/work/$tag.hs
  if [[ "${MODE:-frame}" == machine ]]; then
    nice harness/machine_main.exe "$dir" "$cls" "$meth" "$desc" "$in" "$FUEL" harness/work/unicode-21.txt > harness/work/$tag.md
  else
    nice harness/model_main.exe "$f" "$meth" "$desc" "$in" "$FUEL" > harness/work/$tag.md
  fi
  summary=$(python3 harness/compare.py "$in" harness/work/$tag.hs harness/work/$tag.md); ok=$?
  stuck=$(grep -c '^STUCK\|^FUEL' harness/work/$tag.md)
  echo "$tag: $summary" | head -12
  [[ $ok -ne 0 ]] && rc=1
  read -r _ agree mism exc _ <<<"$(echo "$summary" | head -1 | sed 's/[a-z_]*=//g')"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$(date -u +%H:%M:%S)" "$cls" "$meth" "$desc" "$n" \
    "$agree" "$mism" "$exc" "$stuck" "$seed" >> "$res"
done < "$targets"
exit $rc

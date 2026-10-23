#!/usr/bin/env bash
# Float/double differential test: Rocq model (extracted) vs HotSpot.
#   harness/float/run.sh            # N=250000 inputs per op, default seed
#   N=1000 SEED=7 harness/float/run.sh
#   JAVA_OPTS=-Xint harness/float/run.sh   # interpreter only
# Work files go to $WORK (default harness/float/_work); results summary to
# $WORK/summary.txt.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
N="${N:-250000}"
SEED="${SEED:-20261023}"
WORK="${WORK:-$HERE/_work}"
JAVA_OPTS="${JAVA_OPTS:-}"
export OPAMROOT=/opt/opamroot
eval "$(opam env --switch rocq --set-switch 2>/dev/null)"

echo "== compile model"
(cd "$ROOT" && rocq compile -Q theories JVM theories/Core/Float.v)
echo "== extract"
mkdir -p "$HERE/_build"
(cd "$HERE/_build" && rocq compile -w -extraction-default-directory -Q "$ROOT/theories" JVM "$HERE/FloatExtract.v")
echo "== build OCaml driver"
(cd "$HERE/_build" && cp "$HERE/model_float.ml" . &&
 ocamlfind ocamlopt -O2 -w -a float_model.mli float_model.ml model_float.ml -o model_float.exe 2>/dev/null ||
 ocamlfind ocamlopt -w -a float_model.mli float_model.ml model_float.ml -o model_float.exe)
echo "== build Java side"
javac -d "$HERE/_build" "$HERE/FloatHarness.java"
java -version 2>&1 | grep -v JAVA_TOOL_OPTIONS | head -3

mkdir -p "$WORK"
echo "== generate inputs (N=$N, seed=$SEED)"
nice java -Xmx512m -cp "$HERE/_build" FloatHarness gen "$WORK" "$N" "$SEED"
echo "== run JVM"
nice java -Xmx512m $JAVA_OPTS -cp "$HERE/_build" FloatHarness eval "$WORK"
echo "== run model"
for f in "$WORK"/*.in; do
  op="$(basename "$f" .in)"
  t0=$(date +%s.%N)
  nice "$HERE/_build/model_float.exe" "$op" "$f" "$WORK/$op.model"
  printf "   %-10s %6.1fs\n" "$op" "$(echo "$(date +%s.%N) - $t0" | bc)"
done
for m in tiesaway ftz; do for op in fadd dadd fmul dmul; do
  nice "$HERE/_build/model_float.exe" "mut_${m}_$op" "$WORK/$op.in" "$WORK/mut_${m}_$op.model"
done; done
echo "== compare"
status=0
python3 "$HERE/compare.py" "$WORK" | tee "$WORK/summary.txt" || status=1
echo "== canaries (mismatches expected)"
python3 "$HERE/compare.py" "$WORK" --canary | tee -a "$WORK/summary.txt"
exit $status

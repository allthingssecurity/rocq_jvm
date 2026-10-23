#!/usr/bin/env bash
# Build the java.util model classes and their differential tests.
#   harness/jdkmodel/build.sh
# - model:  harness/jdkmodel/src/java/util/*.java  -> classes/jdkmodel/java/util/*.class
#           compiled as a patch of java.base (javac --release 17 --patch-module), so the classes
#           are in package java.util; they are loaded only by the Rocq machine, never by HotSpot.
# - tests:  harness/jdkmodel/tests/**/*.java      -> classes/jdkmodel-tests/
#           compiled against the REAL JDK (HotSpot runs them on the real java.util; the machine
#           runs them with classes/jdkmodel in front).
# Writes classes/jdkmodel/BUILD-INFO (javac version, sha256 of each class).
#
#   harness/jdkmodel/build.sh canary <name>
# builds a deliberately WRONG model into classes/jdkmodel-canary (tests unchanged), to check that
# the differential tests detect it (see docs/jdk-collections-status.md).  <name>:
#   nospread   HashMap.hash without the h ^ (h >>> 16) spreading (a different bin index)
#   rootfront  tree bins: the root is not moved to the front of the bin list
#   cia-tail   computeIfAbsent/compute/merge append new entries instead of prepending them
#   lhm-access access-ordered LinkedHashMap.get does not count as a modification
#   al-iobe    ArrayList.get(-1) throws ArrayIndexOutOfBoundsException instead of IndexOutOfBoundsException
set -euo pipefail
cd "$(dirname "$0")/../.."
src=harness/jdkmodel/src
out=classes/jdkmodel
tout=classes/jdkmodel-tests
if [[ "${1:-}" == canary ]]; then
  name=${2:?canary name}
  tmp=$(mktemp -d)
  cp -r "$src"/. "$tmp"/
  u=$tmp/java/util
  case $name in
    nospread)   sed -i 's|return h ^ (h >>> 16);|return h;|' "$u/HashMap.java" ;;
    rootfront)  sed -i 's|if (root == null \|\| tab == null \|\| tab.length == 0) return;|if (true) return;|' "$u/HashMap.java" ;;
    cia-tail)   python3 - "$u/HashMap.java" <<'PY'
import sys; p = sys.argv[1]; s = open(p).read()
old = """            tab[i] = newNode(h, key, v, first);
            if (count >= TREEIFY_BIN - 1) treeifyBin(tab, h);"""
new = """            if (first == null) tab[i] = newNode(h, key, v, null);
            else { Node<K, V> l = first; while (l.next != null) l = l.next; l.next = newNode(h, key, v, null); }
            if (count >= TREEIFY_BIN - 1) treeifyBin(tab, h);"""
assert old in s; open(p, "w").write(s.replace(old, new))
PY
                ;;
    lhm-access) sed -i 's|            modCount++;\n        }|X|; /tail = p;/{n;s|            modCount++;|            /* canary */|}' "$u/LinkedHashMap.java" ;;
    al-iobe)    sed -i '0,/if (index < 0 || index >= size) throw new IndexOutOfBoundsException();/s//if (index < 0 || index >= size) throw new ArrayIndexOutOfBoundsException();/' "$u/ArrayList.java" ;;
    *) echo "unknown canary $name"; exit 2 ;;
  esac
  if diff -rq "$src" "$tmp" >/dev/null; then echo "canary $name: mutation did not apply"; exit 1; fi
  diff -r "$src" "$tmp" || true
  rm -rf classes/jdkmodel-canary; mkdir -p classes/jdkmodel-canary
  nice javac -J-Xmx512m --release 17 -g -nowarn --patch-module java.base="$tmp" -d classes/jdkmodel-canary \
    $(find "$tmp" -name '*.java' | sort) 2>&1 | grep -v '^Picked up\|^Note:' || true
  rm -rf "$tmp"
  echo "canary $name: $(find classes/jdkmodel-canary -name '*.class' | wc -l) classes in classes/jdkmodel-canary"
  # run every target (or those matching $CANARY_TARGETS) on CANARY_N inputs against the canary,
  # without writing harness/results; the canary is DETECTED if some target has a mismatch
  n=${CANARY_N:-200}
  w=$(mktemp -d)
  detected=0
  while read -r dir cls meth desc opt; do
    [[ -z "$dir" || "$dir" == \#* ]] && continue
    [[ -n "${CANARY_TARGETS:-}" && ! "$meth" =~ ${CANARY_TARGETS} ]] && continue
    cdir=$(echo "$dir" | sed 's|classes/jdkmodel$|classes/jdkmodel-canary|; s|classes/jdkmodel:|classes/jdkmodel-canary:|')
    python3 harness/gen_inputs.py "$desc" "$n" 99 > "$w/in"
    nice java -Xmx512m -cp harness/work DiffRunner "${dir%%:*}" "$cls" "$meth" "$desc" "$w/in" 2>/dev/null > "$w/hs"
    nice harness/machine_main.exe "$cdir" "$cls" "$meth" "$desc" "$w/in" "${FUEL:-2000000}" harness/work/unicode-21.txt > "$w/md"
    python3 harness/compare.py "$w/in" "$w/hs" "$w/md" > "$w/cmp" || detected=1
    summary=$(head -1 "$w/cmp")
    echo "  canary $name ${cls##*.}.$meth: $summary"
  done < harness/targets-jdkmodel.txt
  rm -rf "$w"
  if [[ $detected == 1 ]]; then echo "canary $name DETECTED"; exit 0; else echo "canary $name NOT DETECTED"; exit 1; fi
fi
rm -rf "$out" "$tout"
mkdir -p "$out" "$tout"
nice javac -J-Xmx512m --release 17 -g -nowarn -Xlint:none --patch-module java.base="$src" -d "$out" \
  $(find "$src" -name '*.java' | sort) 2>&1 | grep -v '^Picked up\|^Note:' || true
[[ -f $out/java/util/HashMap.class ]] || { echo "model build failed"; exit 1; }
# javac puts patch-module output under the module name when -d is used with modules
if [[ -d $out/java.base ]]; then cp -r "$out"/java.base/* "$out"/ && rm -rf "$out"/java.base; fi
nice javac -J-Xmx512m --release 17 -g -d "$tout" $(find harness/jdkmodel/tests -name '*.java' | sort) 2>&1 | grep -v '^Picked up' || true
{
  echo "built $(date -u +%Y-%m-%dT%H:%M:%SZ) by harness/jdkmodel/build.sh"
  javac -version 2>&1 | grep -v '^Picked up'
  (cd "$out" && find . -name '*.class' | sort | xargs sha256sum)
} > "$out/BUILD-INFO"
echo "model: $(find "$out" -name '*.class' | wc -l) classes in $out; tests: $(find "$tout" -name '*.class' | wc -l) classes in $tout"

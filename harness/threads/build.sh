#!/usr/bin/env bash
# Build the java.lang.Thread model class (loaded only by the Rocq machine) and the thread tests.
#   harness/threads/build.sh
set -euo pipefail
cd "$(dirname "$0")/../.."
out=classes/threadmodel; tout=classes/thread-tests
rm -rf "$out" "$tout"; mkdir -p "$out" "$tout"
nice javac -J-Xmx512m --release 17 -g -nowarn -Xlint:none --patch-module java.base=harness/threads/src -d "$out" \
  $(find harness/threads/src -name "*.java" | sort) 2>&1 | grep -v '^Picked up\|^Note:' || true
if [[ -d $out/java.base ]]; then cp -r "$out"/java.base/* "$out"/ && rm -rf "$out"/java.base; fi
[[ -f $out/java/lang/Thread.class ]] || { echo "model build failed"; exit 1; }
nice javac -J-Xmx512m --release 17 -g -d "$tout" harness/threads/tests/*.java 2>&1 | grep -v '^Picked up' || true
{ echo "javac: $(javac -version 2>&1)"; (cd "$out" && find . -name '*.class' | sort | xargs sha256sum); } > "$out/BUILD-INFO"
echo "built $(find $out -name '*.class' | wc -l) model classes, $(find $tout -name '*.class' | wc -l) test classes"

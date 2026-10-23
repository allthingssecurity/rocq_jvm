#!/usr/bin/env bash
# Build .class files of Camel sources at an exact commit, with javac --release 17 -g
# (maven-compiler-plugin's default debug=true), into classes/<label>/.
#
#   tools/build-camel-classes.sh <label> <camel-git-dir> <commit> <module-src-dir> <Class.java path relative to module src>...
#
# Example:
#   tools/build-camel-classes.sh wal-main ~/src/camel 36bebb52 components/camel-wal/src/main/java \
#        org/apache/camel/component/wal/TransactionLog.java
#
# The module's whole source tree at that commit is exported (git archive) so javac's -sourcepath
# resolves same-module dependencies from the same commit. SLF4J_SRC (slf4j-api sources, version of
# Camel's parent pom) is used only for compile-time signatures; its classes are not kept.
# Writes classes/<label>/BUILD-INFO with commit, javac version, and sha256 of each produced class.
set -euo pipefail
label=$1; repo=$2; commit=$3; modsrc=$4; shift 4
here=$(cd "$(dirname "$0")/.." && pwd)
out="$here/classes/$label"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
full=$(git -C "$repo" rev-parse "$commit^{commit}")
mkdir -p "$work/src" "$work/out"
git -C "$repo" archive "$full" "$modsrc" | tar -x -C "$work/src"
SLF4J_SRC=${SLF4J_SRC:-$HOME/src/slf4j/slf4j-api/src/main/java}
files=()
for f in "$@"; do files+=("$work/src/$modsrc/$f"); done
nice javac -J-Xmx1g --release 17 -g -implicit:class -encoding UTF-8 \
  -sourcepath "$work/src/$modsrc:$SLF4J_SRC" -d "$work/out" "${files[@]}" 2> >(grep -v JAVA_TOOL_OPTIONS >&2)
rm -rf "$out"; mkdir -p "$out"
# keep only the classes of the module (drop org/slf4j)
(cd "$work/out" && find . -name '*.class' ! -path './org/slf4j/*' | while read -r c; do
   mkdir -p "$out/$(dirname "$c")"; cp "$c" "$out/$c"; done)
{
  echo "label: $label"
  echo "remote branches containing it: $(git -C "$repo" branch -r --contains "$full" 2>/dev/null | grep -v HEAD | head -3 | tr -s " \n" " ")"
  echo "commit: $full"
  echo "module: $modsrc"
  echo "sources: $*"
  echo "javac: $(javac -version 2>&1 | grep -v JAVA_TOOL_OPTIONS) --release 17 -g"
  echo "built: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "sha256:"
  (cd "$out" && find . -name '*.class' | sort | xargs sha256sum | sed 's/^/  /')
} > "$out/BUILD-INFO"
cat "$out/BUILD-INFO"

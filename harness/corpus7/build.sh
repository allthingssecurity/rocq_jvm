#!/usr/bin/env bash
# Build classes/corpus7: the main sources, then the stage-1 versions of XC, YC, ZC, SX compiled
# against older interfaces/classes (separate compilation), copied over the main ones, so that the
# loaded program is the one a JVM sees after classes changed incompatibly (JVMS 5.4.3, 6.5).
set -euo pipefail
cd "$(dirname "$0")/../.."
JAVAC=${JAVAC:-/usr/lib/jvm/java-1.21.0-openjdk-amd64/bin/javac}
rm -rf classes/corpus7 && mkdir -p classes/corpus7
"$JAVAC" --release 17 -g -d classes/corpus7 $(find harness/corpus7/org -name '*.java')
t=$(mktemp -d)
"$JAVAC" --release 17 -g -d "$t" -cp classes/corpus7 $(find harness/corpus7/stage1 -name '*.java')
for c in XC YC ZC SX; do cp "$t/org/rocqjvm/corpus7/$c.class" classes/corpus7/org/rocqjvm/corpus7/; done
rm -rf "$t"
echo "built classes/corpus7"

#!/usr/bin/env bash
# Check every generated class module theories/Classes/*.v against its .class file:
# the file named in the header must exist, have the recorded sha256, and its hex must be
# exactly the concatenated hex string of the module.
set -euo pipefail
cd "$(dirname "$0")/.."
rc=0
for v in theories/Classes/*.v; do
  f=$(sed -n 's/^   file:   //p' "$v")
  [[ -z "$f" ]] && continue
  want=$(sed -n 's/^   sha256: //p' "$v")
  got=$(sha256sum "$f" | cut -d' ' -f1)
  hexv=$(sed -n '/^Definition hex/,/%string\./p' "$v" | grep -o '"[0-9a-f]*"' | tr -d '"\n')
  hexf=$(python3 -c 'import sys;print(open(sys.argv[1],"rb").read().hex())' "$f")
  if [[ "$want" == "$got" && "$hexv" == "$hexf" ]]; then echo "ok   $v  <- $f"; else echo "FAIL $v  <- $f"; rc=1; fi
done
exit $rc

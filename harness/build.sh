#!/usr/bin/env bash
# Build the Rocq project (which also extracts extraction/jvm.ml) and both OCaml differential drivers.
set -euo pipefail
cd "$(dirname "$0")/.."
make
cd extraction
cp ../harness/model_main.ml ../harness/machine_main.ml ../harness/threads_main.ml .
ocamlfind ocamlopt -O2 -w -a -package zarith -linkpkg jvm.mli jvm.ml model_main.ml -o ../harness/model_main.exe.new
ocamlfind ocamlopt -O2 -w -a -package zarith -linkpkg jvm.mli jvm.ml machine_main.ml -o ../harness/machine_main.exe
ocamlfind ocamlopt -O2 -w -a -package zarith -linkpkg jvm.mli jvm.ml threads_main.ml -o ../harness/threads_main.exe
mv ../harness/model_main.exe.new ../harness/model_main.exe
echo "built harness/model_main.exe harness/machine_main.exe harness/threads_main.exe"

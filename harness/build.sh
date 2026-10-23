#!/usr/bin/env bash
# Build the Rocq project, extract the model, and compile the OCaml differential driver.
set -euo pipefail
cd "$(dirname "$0")/.."
make -j1
mkdir -p extraction
# Extract.v writes extraction/jvm.ml{,i} when it is compiled (part of make).
cd extraction
cp ../harness/model_main.ml .
ocamlfind ocamlopt -O2 -w -a jvm.mli jvm.ml model_main.ml -o ../harness/model_main.exe 2>/dev/null \
  || ocamlfind ocamlopt -w -a jvm.mli jvm.ml model_main.ml -o ../harness/model_main.exe
echo "built harness/model_main.exe"

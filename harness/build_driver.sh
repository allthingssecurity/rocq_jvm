#!/usr/bin/env bash
# Build only what the differential drivers need (Core, Loader, Jdk, Extract.v) and the two OCaml
# drivers, without the Camel proofs (harness/build.sh builds everything).
set -euo pipefail
cd "$(dirname "$0")/.."
[[ -f Makefile.rocq ]] || rocq makefile -f _RocqProject -o Makefile.rocq
make -f Makefile.rocq theories/Extract.vo
cd extraction
cp ../harness/model_main.ml ../harness/machine_main.ml .
ocamlfind ocamlopt -O2 -w -a jvm.mli jvm.ml model_main.ml -o ../harness/model_main.exe.new
ocamlfind ocamlopt -O2 -w -a jvm.mli jvm.ml machine_main.ml -o ../harness/machine_main.exe
mv ../harness/model_main.exe.new ../harness/model_main.exe
echo "built harness/model_main.exe harness/machine_main.exe"

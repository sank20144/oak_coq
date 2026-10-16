#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
theories="$here/../../oak_coq/theories"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
python3 -I "$here/lemmas.py" "$theories" > "$tmp/lemmas.json"
python3 -I -c 'import json,sys; print("\n".join(x["name"] for x in json.load(open(sys.argv[1]))))' "$tmp/lemmas.json" > "$tmp/names.txt"
mkdir "$tmp/tok"
# print proofs in full so lemmas used deep inside still show up
docker run --rm --network none -v "$theories":/src:ro -v "$tmp":/out oak-coq-toolchain bash -lc '
  eval $(opam env); mkdir t && cd /src && cp _CoqProject $(grep "\.v$" _CoqProject) ~/work/t && cd ~/work/t
  coq_makefile -f _CoqProject -o CoqMakefile >/dev/null && make -f CoqMakefile >/dev/null
  mods=$(grep "\.v$" _CoqProject | sed "s/\.v$//" | tr "\n" " ")
  while read -r n; do
    printf "From OC Require Import %s.\nSet Printing Depth 1000000.\nSet Printing Width 200.\nPrint %s.\n" "$mods" "$n" > /tmp/q.v
    coqc -Q . OC.oak_coq.theories /tmp/q.v | grep -oE "[A-Za-z_][A-Za-z0-9_]*" | sort -u > "/out/tok/$n.txt"
  done < /out/names.txt'
python3 -I "$here/graph.py" "$tmp/lemmas.json" "$tmp/tok" "$here/graph.json"

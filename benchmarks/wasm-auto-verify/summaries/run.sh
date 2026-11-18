#!/usr/bin/env bash
# Regression test and benchmark of the function summaries (docs/projects/wasm-binaryen-tooling.md):
# stages equivu and equivc.
#
#   benchmarks/wasm-auto-verify/summaries/run.sh
#
# 1. check-inputs.sh: the WAT files are quoted verbatim in tests/wasm/auto2/SummBench/Defs.lean
#    and the pinned binaries in bin/ match bin/SHA256SUMS.
# 2. `wasm-check equiv` on every pair of expected.tsv (loops with constant trip counts,
#    internal calls): verdict and stage (or a counterexample) as expected.
# 3. `wasm-check pass` on the e-graph corpus optimizer runs (Binaryen -O3 on 60 random
#    functions, -O2 and the peephole pass on opt-in): proved/refuted/unknown and
#    e-graph lift counts as in pass-expected.tsv.
# Prints a table with wall time and peak memory. The certificates (`--lean`) are not checked here:
# docs/projects/wasm-binaryen-tooling.md records how they were checked (as modules built by lake build).
#
# The tool is built by `lake build --wfail wasm-check`; when it is absent the test is skipped
# (exit 0) with a message. Exit status: 0 when every result is the expected one, 1 otherwise.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
bin=${SIL_WASM_CHECK:-$root/.lake/build/bin/wasm-check}
if [[ ! -x $bin ]]; then
  echo "SKIP: $bin not found (build it with lake build wasm-check)"
  exit 0
fi
fail=0
"$here/check-inputs.sh" || fail=1
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
echo "| a | b | export | verdict | stage | ms |"
echo "| --- | --- | --- | --- | --- | --- |"
while IFS=$'\t' read -r a b e want stage; do
  [[ $a == \#* || -z $a ]] && continue
  j=$("$bin" equiv "$here/bin/$a.wasm" "$here/bin/$b.wasm" "$e")
  v=$(sed -E 's/.*"verdict":"([a-z]*)".*/\1/' <<< "$j")
  if [[ $j == *'"kind":"counterexample"'* ]]; then s=counterexample
  else s=$(sed -E 's/.*"stage":"([a-z+]*)".*/\1/' <<< "$(grep -o '"reason":{[^}]*}' <<< "$j")"); fi
  ms=$(sed -E 's/.*"stage":"difftest","ms":([0-9]+).*/\1/' <<< "$j")
  echo "| $a | $b | $e | $v | $s | $ms |"
  if [[ $v != "$want" || $s != "$stage" ]]; then
    echo "FAIL $a $b $e: $v/$s, expected $want/$stage"; fail=1
  fi
done < "$here/expected.tsv"
C="$root/tools/wasm-egraph/corpus"
echo
echo "| run | exports | proved | refuted | unknown | e-graph lifts | wall s | peak KiB |"
echo "| --- | --- | --- | --- | --- | --- | --- | --- |"
while IFS=$'\t' read -r name a b tv want; do
  [[ $name == \#* || -z $name ]] && continue
  /usr/bin/time -f '%e %M' -o "$out/$name.time" "$bin" pass "$C/$a" "$C/$b" --random 200 \
    --egraph-tv "$root/$tv" > "$out/$name.jsonl"
  s=$(tail -1 "$out/$name.jsonl")
  got=$(sed -E 's/.*"exports":([0-9]+),"proved":([0-9]+),"refuted":([0-9]+),"unknown":([0-9]+),"egraphLifts":([0-9]+).*/\1\/\2\/\3\/\4\/\5/' <<< "$s")
  read -r t m < "$out/$name.time"
  echo "| $name | ${got//\// | } | $t | $m |"
  if [[ $got != "$want" ]]; then echo "FAIL $name: $got, expected $want"; fail=1; fi
done < "$here/pass-expected.tsv"
(( fail == 0 )) && echo "summaries/run.sh: ok"
exit $fail

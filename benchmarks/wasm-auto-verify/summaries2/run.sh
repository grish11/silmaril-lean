#!/usr/bin/env bash
# Regression test and benchmark of the summaries with the third simplifier
# and loop contracts (stages equivv and vcequiv; docs/projects/wasm-binaryen-tooling.md).
#
#   benchmarks/wasm-auto-verify/summaries2/run.sh [--certs]
#
# 1. check-inputs.sh: the WAT files are quoted verbatim in their Lean modules and the pinned
#    binaries in bin/ match bin/SHA256SUMS.
# 2. `wasm-check equiv --random 200` on every pair of expected.tsv (loops whose trip count
#    is the input, through the functional contracts of Silmaril.Wasm.Auto2.VCEquiv; memsum4, a loop
#    over a data segment): verdict and stage (or a counterexample) as expected.
# 3. With --certs, each pair's certificate (`--lean`, the default kernel form: modules as decoded
#    terms, validation once, checkAmongV over instK?) is checked as a scratch module of this
#    checkout (Silmaril/Wasm/Auto2/Scratch/CertS2_<n>.lean, removed afterwards) by
#    `lake build --wfail`; its wall time and peak memory are reported.
# Prints a Markdown table. Needs the executable wasm-check (`lake build --wfail
# wasm-check`); skips (exit 0) with a message without it. Exit status: 0 when every result
# is the expected one (and every certificate builds), 1 otherwise.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
root="$(cd "$here/../../.." && pwd)"
bin=${SIL_WASM_CHECK:-$root/.lake/build/bin/wasm-check}
certs=0
for a in "$@"; do
  case $a in
    --certs) certs=1 ;;
    *) echo "usage: $0 [--certs]" >&2; exit 2 ;;
  esac
done
if [[ ! -x $bin ]]; then
  echo "SKIP: $bin not found (build it with lake build wasm-check)"
  exit 0
fi
fail=0
"$here/check-inputs.sh" || fail=1
out=$(mktemp -d)
trap 'rm -rf "$out"; rm -f "$root"/Silmaril/Wasm/Auto2/Scratch/CertS2_*.lean' EXIT
echo "| a | b | export | verdict | stage | tool ms | certificate s | certificate peak MiB |"
echo "| --- | --- | --- | --- | --- | --- | --- | --- |"
n=0
while IFS=$'\t' read -r a b e want stage; do
  [[ $a == \#* || -z $a ]] && continue
  n=$((n + 1))
  j=$("$bin" equiv "$here/bin/$a.wasm" "$here/bin/$b.wasm" "$e" --random 200 --lean "$out/c$n.lean")
  v=$(sed -E 's/.*"verdict":"([a-z]*)".*/\1/' <<< "$j")
  if [[ $j == *'"kind":"counterexample"'* ]]; then s=counterexample
  else s=$(sed -E 's/.*"stage":"([a-z+]*)".*/\1/' <<< "$(grep -o '"reason":{[^}]*}' <<< "$j")"); fi
  ms=$(sed -E 's/.*"stage":"difftest","ms":([0-9]+).*/\1/' <<< "$j")
  ct=""; cm=""
  if (( certs )) && [[ -f $out/c$n.lean ]]; then
    mkdir -p "$root/Silmaril/Wasm/Auto2/Scratch"
    cp "$out/c$n.lean" "$root/Silmaril/Wasm/Auto2/Scratch/CertS2_$n.lean"
    if (cd "$root" && /usr/bin/time -f '%e %M' -o "$out/t$n" lake build --wfail \
        "Silmaril.Wasm.Auto2.Scratch.CertS2_$n" > "$out/b$n.log" 2>&1); then
      read -r ct cm < "$out/t$n"; cm=$((cm / 1024))
    else
      echo "FAIL certificate of $a $b $e (log: $out/b$n.log)"
      fail=1
    fi
    rm -f "$root/Silmaril/Wasm/Auto2/Scratch/CertS2_$n.lean"
  fi
  echo "| ${a##*/} | ${b##*/} | $e | $v | $s | $ms | $ct | $cm |"
  if [[ $v != "$want" || $s != "$stage" ]]; then
    echo "FAIL $a $b $e: $v/$s, expected $want/$stage"; fail=1
  fi
done < "$here/expected.tsv"
rmdir "$root/Silmaril/Wasm/Auto2/Scratch" 2>/dev/null || true
(( fail == 0 )) && echo "summaries2/run.sh: ok"
exit $fail

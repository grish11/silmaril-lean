#!/usr/bin/env bash
# Regression test and benchmark of stage vcinfer (docs/projects/wasm-binaryen-tooling.md): contracts inferred
# from templates.
#
#   benchmarks/wasm-auto-verify/summaries3/run.sh [--certs]
#
# 1. check-inputs.sh (WAT quoted verbatim in Lean, binaries match bin/SHA256SUMS).
# 2. `wasm-check equiv --random 200` on every pair of expected.tsv. Expected `vcinfer`: the
#    verdict is unknown and the report has a `vcinfer` candidate (an InferFun with a side for each
#    export). The tool does not prove these: the certificate does.
# 3. With --certs, each pair's certificate (`--lean`) is checked as a scratch module
#    (`lake build --wfail` of a fresh module); a `vcinfer`
#    pair counts as proved only when its certificate builds. Wall time and peak memory reported.
# Needs the executable wasm-check; skips (exit 0) with a message without it.
# Exit status: 0 when every result is the expected one (and every certificate builds), else 1.
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
trap 'rm -rf "$out"' EXIT
echo "| a | b | export | tool verdict | stage | vcinfer | result | tool ms | certificate s | certificate peak MiB |"
echo "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"
n=0
while IFS=$'\t' read -r a b e want; do
  [[ $a == \#* || -z $a ]] && continue
  n=$((n + 1))
  j=$("$bin" equiv "$here/bin/$a.wasm" "$here/bin/$b.wasm" "$e" --random 200 --lean "$out/c$n.lean")
  v=$(sed -E 's/.*"verdict":"([a-z]*)".*/\1/' <<< "$j")
  if [[ $j == *'"kind":"counterexample"'* ]]; then s=counterexample
  elif [[ $v == proved ]]; then s=$(sed -E 's/.*"stage":"([a-z+]*)".*/\1/' <<< "$(grep -o '"reason":{[^}]*}' <<< "$j")")
  else s=-; fi
  inf=-; [[ $j == *'"vcinfer":{"fun"'* ]] && inf=$(sed -E 's/.*"vcinfer":\{"fun":"([a-z0-9]*)".*/\1/' <<< "$j")
  ms=$(sed -E 's/.*"stage":"difftest","ms":([0-9]+).*/\1/' <<< "$j")
  res=$s
  [[ $v == unknown && $inf != - ]] && res=vcinfer
  [[ $v == unknown && $inf == - ]] && res=unknown
  ct=""; cm=""
  if (( certs )) && [[ -f $out/c$n.lean ]]; then
    if (cd "$root" && /usr/bin/time -f '%e %M' -o "$out/t$n" lake build --wfail \
        "$out/c$n.lean" > "$out/b$n.log" 2>&1); then
      read -r ct cm < "$out/t$n"; cm=$((cm / 1024))
      [[ $res == vcinfer ]] && res="vcinfer (certificate built)"
    else
      echo "FAIL certificate of $a $b $e (log: $out/b$n.log)"
      fail=1
    fi
  fi
  echo "| ${a##*/} | ${b##*/} | $e | $v | $s | $inf | $res | $ms | $ct | $cm |"
  if [[ ${res%% *} != "$want" ]]; then
    echo "FAIL $a $b $e: $res, expected $want"; fail=1
  fi
done < "$here/expected.tsv"
(( fail == 0 )) && echo "summaries3/run.sh: ok"
exit $fail

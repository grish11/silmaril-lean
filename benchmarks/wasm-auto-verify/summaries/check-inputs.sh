#!/usr/bin/env bash
# Check that every WAT file of this directory is quoted verbatim in
# tests/wasm/auto2/SummBench/Defs.lean (the `wat3!` copies the Lean benchmark uses), and that the
# pinned binaries in bin/ match bin/SHA256SUMS.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
defs="$here/../../../tests/wasm/auto2/SummBench/Defs.lean"
fail=0
for f in "$here"/*.wat; do
  if ! python3 -I -c 'import sys; t=open(sys.argv[1]).read().rstrip("\n"); sys.exit(0 if ("r#\"\n"+t+"\n\"#") in open(sys.argv[2]).read() else 1)' "$f" "$defs"; then
    echo "check-inputs: $(basename "$f") differs from its copy in SummBench/Defs.lean"; fail=1
  fi
done
(cd "$here/bin" && sha256sum --quiet -c SHA256SUMS) || { echo "check-inputs: bin/SHA256SUMS mismatch"; fail=1; }
(( fail == 0 )) && echo "check-inputs: ok"
exit $fail

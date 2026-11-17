#!/usr/bin/env bash
# Check the compiler explorer end to end, from the repository root:
#   tools/compiler-explorer/check.sh [OUT]          (OUT defaults to .lake/compiler-explorer)
# 1. build the Lean modules (the API, the C/x86 instance, the examples' restatements);
# 2. regenerate the manifests and fail if they differ from the committed ones;
# 3. run the evidence exporter on every manifest with Lean statements;
# 4. ingest manifests and evidence into a fresh database and print the statuses;
# 5. run the database and view tests.
# Docker is not needed: the builds and listings are committed (fixtures.py build|listings).
set -euo pipefail
cd "$(dirname "$0")/../.."
out="${1:-.lake/compiler-explorer}"
mkdir -p "$out/evidence"
lake build --wfail Silmaril.Compiler.Explorer.Thms Silmaril.Project.CompilesTo.Explorer.Thms \
  CompilesToExamples.Explorer.Builds CompilesToExamples.Straight.Rows CompilesToExamples.Branch.Rows
python3 -I tools/compiler-explorer/fixtures.py manifests > /dev/null
git diff --exit-code -- examples/compiler-explorer/manifests
commit="$(git rev-parse HEAD)"
for m in examples/compiler-explorer/manifests/*.json; do
  if python3 -I -c 'import json,sys; sys.exit(0 if json.load(open(sys.argv[1]))["lean"]["modules"] else 1)' "$m"; then
    EXPLORER_MANIFEST_SHA256="$(sha256sum "$m" | cut -d' ' -f1)" EXPLORER_GIT_COMMIT="$commit" \
      lake env lean --run tools/compiler-explorer/export.lean "$m" "$out/evidence/$(basename "$m")"
  fi
done
rm -f "$out/explorer.sqlite"
python3 -I tools/compiler-explorer/cexplorer.py ingest "$out/explorer.sqlite" examples/compiler-explorer/manifests/*.json > /dev/null
python3 -I tools/compiler-explorer/cexplorer.py evidence "$out/explorer.sqlite" "$out"/evidence/*.json
python3 -I tools/compiler-explorer/cexplorer.py status "$out/explorer.sqlite"
python3 -I tools/compiler-explorer/tests/test_cexplorer.py
node --test tools/compiler-explorer/tests/view.test.mjs

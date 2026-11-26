#!/usr/bin/env bash
# Regenerate Lean-NDJSON fixtures in tests/lean-ndjson with lean4export
# (docs/projects/formal-rows.md, "Lean-NDJSON"). The exporter is the lean4export that the pinned
# Mathlib dependency vendors (.lake/packages/mathlib/lean4export, format version 3.1.0), run with no
# options: no --export-unsafe, no --export-mdata, no --ignore-missing. It writes the named
# declarations and their transitive dependencies.
#   scripts/lean-ndjson/export-fixtures.sh [--check]
# With --check, fail if either export differs from the committed fixture.
set -euo pipefail
cd "$(dirname "$0")/../.."
exporter_dir=.lake/packages/mathlib/lean4export
module=Silmaril.Logic.Consequence.Arithmetic.Derivation.Exported
decls=(
  Silmaril.Consequence.Arithmetic.ND.Exported.zeroAddZero
  Silmaril.Consequence.Arithmetic.ND.Exported.instAddZero
  Silmaril.Consequence.Arithmetic.ND.Exported.eqSymm
  Silmaril.Consequence.Arithmetic.ND.Exported.zeroAdd
  Silmaril.Consequence.Arithmetic.ND.Exported.wrongAxiom
  Silmaril.Consequence.Arithmetic.ND.Examples.zeroAdd
)
(cd "$exporter_dir" && lake build lean4export >/dev/null)
lake build "$module" >/dev/null
exporter="$exporter_dir/.lake/build/bin/lean4export"
fixture_dir=tests/lean-ndjson
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT

publish_fixture() {
  local generated="$1" fixture="$2"
  if [[ "${3:-}" == "--check" ]]; then
    if ! cmp -s "$generated" "$fixture"; then
      echo "error: $fixture is not what lean4export writes now; run $0" >&2
      exit 1
    fi
    echo "$fixture: up to date ($(wc -l < "$fixture") lines)"
  else
    cp "$generated" "$fixture"
    echo "wrote $fixture ($(wc -l < "$fixture") lines, $(wc -c < "$fixture") bytes)"
  fi
}

lake env "$exporter" "$module" -- "${decls[@]}" > "$scratch/pa.ndjson"
publish_fixture "$scratch/pa.ndjson" "$fixture_dir/pa-derivations.ndjson" "${1:-}"

lake env lean --root="$fixture_dir" -o "$scratch/LeanNDJSONFixture.olean" \
  "$fixture_dir/LeanNDJSONFixture.lean"
lake env env LEAN_PATH="$scratch" "$exporter" LeanNDJSONFixture -- \
  LeanNDJSONFixture.Carrier LeanNDJSONFixture.useCarrier \
  LeanNDJSONFixture.identity LeanNDJSONFixture.applyCarrier > "$scratch/mltt.ndjson"
publish_fixture "$scratch/mltt.ndjson" "$fixture_dir/mltt-fragment.ndjson" "${1:-}"

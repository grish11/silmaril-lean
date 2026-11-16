#!/usr/bin/env bash
# Regression test for the logic graph's records files (docs/projects/logic-graph.md): editing a
# file under silmaril/logic-graph/ must rebuild its loader incrementally (the `SilmarilLogicGraphData`
# library `needs` the `logicGraphRecords` input), and the edited records must be what the loaded
# environment exports. It adds a probe record to pending.toml, checks that Lake rebuilds
# Silmaril.LogicGraph.Hets.Defs and that `#silmaril logic_pending` lists the probe, then restores
# the file and checks that the probe is gone again. The working tree is restored on exit.
set -euo pipefail
cd "$(dirname "$0")/../.."
LAKE=${LAKE:-lake}
file=silmaril/logic-graph/pending.toml
backup=$(mktemp); cp "$file" "$backup"
probe=$(mktemp --suffix=.lean)
trap 'cp "$backup" "$file"; rm -f "$backup" "$probe"' EXIT
printf 'import Silmaril.LogicGraph.Hets.Defs\n#silmaril logic_pending\n' > "$probe"
listed() { $LAKE env lean "$probe" 2>&1 | grep -c "pending.incremental-probe" || true; }

$LAKE build --wfail SilmarilLogicGraphData > /dev/null
[ "$(listed)" = 0 ] || { echo "test-incremental: the probe is already loaded" >&2; exit 1; }

printf '\n[[logic_pending]]\nname = "pending.incremental-probe"\ntitle = "Incremental probe"\nnodes = 1\nedges = 0\nstatus = "pending-port"\n' >> "$file"
out=$($LAKE build --wfail SilmarilLogicGraphData 2>&1)
grep -q "Built Silmaril.LogicGraph.Hets.Defs" <<< "$out" || { echo "test-incremental: editing $file did not rebuild its loader" >&2; exit 1; }
[ "$(listed)" = 1 ] || { echo "test-incremental: the edited record is not in the loaded environment" >&2; exit 1; }

cp "$backup" "$file"
out=$($LAKE build --wfail SilmarilLogicGraphData 2>&1)
grep -q "Built Silmaril.LogicGraph.Hets.Defs" <<< "$out" || { echo "test-incremental: restoring $file did not rebuild its loader" >&2; exit 1; }
[ "$(listed)" = 0 ] || { echo "test-incremental: the removed record is still loaded" >&2; exit 1; }
echo "test-incremental: ok"

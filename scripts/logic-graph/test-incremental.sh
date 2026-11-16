#!/usr/bin/env bash
# Regression test for the logic graph's records files (docs/projects/logic-graph.md): editing a
# file under silmaril/logic-graph/ must rebuild its loader incrementally (the `SilmarilLogicGraphData`
# library `needs` the `logicGraphRecords` input), and the edited records must be what the loaded
# environment exports. It adds a probe record to pending.toml, checks that Lake rebuilds
# the loader so that `#silmaril logic_pending` lists the probe, then restores
# the file and checks that the probe is gone again (the loader may then come from the cache). The working tree is restored on exit.
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

# a title unique to this run, so that no artifact cache holds the edited loader
printf '\n[[logic_pending]]\nname = "pending.incremental-probe"\ntitle = "Incremental probe %s"\nnodes = 1\nedges = 0\nstatus = "pending-port"\n' "$(date +%s%N)-$$" >> "$file"
$LAKE build --wfail SilmarilLogicGraphData > /dev/null
[ "$(listed)" = 1 ] || { echo "test-incremental: editing $file did not rebuild its loader (the edited record is not loaded)" >&2; exit 1; }

# Restoring the file brings back content Lake may already hold in its artifact cache (CI), so the
# loader may be restored rather than rebuilt: what must hold is that the probe is gone again.
cp "$backup" "$file"
$LAKE build --wfail SilmarilLogicGraphData > /dev/null
[ "$(listed)" = 0 ] || { echo "test-incremental: restoring $file left the removed record loaded" >&2; exit 1; }
echo "test-incremental: ok"

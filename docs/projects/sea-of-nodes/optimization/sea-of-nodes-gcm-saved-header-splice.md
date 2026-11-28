# Checked placement in a saved loop header

Click's Schedule Early and Schedule Late bound placement by operand availability
and uses (§§2.2–2.3). Section 2.4 chooses the most control-dependent block in
the shallowest loop nest. This implementation reuses those checks for one
live, pure, total binding in the typed single-latch CFG with saved preheader
values. It supports a single adjacent header move in either direction.
[PLDI ’95 paper][paper] · [Cross-block depth ranking][cross-block]

The request gives the original binding identity and a cut in the current
header before removal. For a binding at index `i`, original cut `i - 1`
moves it one position earlier when `i > 0`. A request at cut `i + 2` inserts
it at index `i + 1` after removal. A no-op and a longer displacement are
refused. `HeaderSplice.emit?` resolves the live identity, checks the destination
against the current CFG, and applies the typed adjacent swap to the saved
header. The swap translates the subsequent typed operands, branch guard, and
arguments of each successor slot. A new scan at the translated position must
recover the same operand sites and the same ordinary and incoming Φ uses,
including each edge's source, slot, and argument index. The two bindings'
identities move with the instructions. Entry, exit, and the saved label
family remain the same. [Definitions][defs] · [Placement and order proofs][thms]

`emit?_edgePackets` compares both branch packets in their original order,
even when an edge is untaken. `emit?_routes` transports the existing saved
packet invariant and `emit?_run_eq` preserves each fuel-indexed observation.
The number of block visits agrees because only the header's local schedule
changes. `emit?_denotePart` also identifies the partial denotations.
[Routing and execution proofs][thms]

`HeaderSplice.rank?` compares the unchanged position, one nominated header
splice, and one nominated physical preheader splice. It uses the existing
certified natural-loop depth and dominator ordering across blocks. When the
result stays in the header, a strictly later admitted original cut wins the
local tie. Depth is a property of the block. `selected_minDepth` and
`laterHeader?_iff` describe the ranking over those candidates.
[Ranking proofs][thms]

The fixture moves origin 5 from header index 3 to index 2. Its ordinary
reads remain at cuts 4 and 5, and its exit use remains argument zero of the
false occurrence. It separately refuses a later cut across the first
ordinary read and an earlier cut before a producer. From the emitted
header, the ranking fixture selects the later header at original cut 4
when preheader cut 0 is before a producer. Admitting preheader cut 1 makes
depth 0 beat the depth-1 header. Both ranked executions exhaust at fuel 3
and 4 and return 4 at fuel 5. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Regression
cat >/tmp/gcm-saved-header-splice.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Example
#eval observe
#eval refused
#eval ranking
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-saved-header-splice.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[cross-block]: sea-of-nodes-gcm-cross-block-depth.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/HeaderSplice/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/HeaderSplice/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/HeaderSplice/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/HeaderSplice/Regression.lean

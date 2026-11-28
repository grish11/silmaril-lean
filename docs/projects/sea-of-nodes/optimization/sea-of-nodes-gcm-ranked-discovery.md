# Discover ranked preheader hoists on the current layout

This opt-in driver schedules pure, total bindings in the existing saved
single-latch loop. It uses Click's operand and use bounds and the loop-depth
choice (§§2.2–2.4) through the existing physical-cut ranker. The driver
scans the surviving original identities in current header order.
[PLDI ’95 paper][paper] · [Checked cut search][search] · [Ranked replay][replay]

`hoist?` gives the ranker a zero header crossing budget and admits an origin
when the ranker selects an actual preheader splice. `choose?` takes the first
such result, and `collect` scans again on the exact emitted CFG. The latest
cut and loop depth are still checked for each origin on that CFG. The
scheduler uses inventory order to choose between different origins.
[Definitions][defs]

`hoist_moves` ties the chosen layout to the actual physical emission and the
resolved header index. Each emitted splice erases one identity from the
surviving header inventory. `schedule?` validates the starting control shape
and inventory and uses the initial inventory size as its bound. The
`schedule?_spec` theorem proves that the emitted requests reproduce the
exact checked trace and that no remaining enumerated origin has a
rank-selected hoist. This fixed point concerns the accepted rank results
for the represented profile. The single-latch admission proof strengthens
it to absence of a checked physical preheader splice for any retained
live origin. [Termination and replay proofs][thms] · [Admission proof][admission]

The trace is a #4580 replay certificate. `plan_preserves` transports the
physical-layout invariant, the full saved and surviving identity inventory,
the saved-packet routing relation, and the matched append prefix. These
proofs start from the same three premises as ranked replay. The final CFG
agrees with the input on returns and exhaustion at common fuel and in
partial denotation. [Observation proofs][thms]

The compiled fixture discovers origins 5, 6, and 7 at physical cuts 2, 3,
and 4. Origin 6 starts with no accepted physical cut and becomes eligible at
cut 3 after the actual producer splice. The scan stops with origins 3, 0,
and 4 still in the header. The regression checks both successor packets,
entry, two feedback visits, and the exit tuple. Both CFGs exhaust at fuel
3 and 4 and return 9 at fuel 5. A validated fixed point yields an empty
schedule, and mismatched starting inventory is refused.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Regression
cat >/tmp/gcm-ranked-discovery.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Example
#eval observe
#eval stopCases
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-ranked-discovery.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Discovery.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[search]: sea-of-nodes-gcm-preheader-search.md
[replay]: sea-of-nodes-gcm-ranked-replay.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Sequence/Discovery/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Sequence/Discovery/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Sequence/Discovery/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Sequence/Discovery/Regression.lean
[admission]: sea-of-nodes-gcm-single-latch-admission.md

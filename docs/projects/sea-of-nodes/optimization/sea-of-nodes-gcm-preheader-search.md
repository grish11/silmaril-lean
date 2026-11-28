# Search checked physical preheader cuts

Click's Schedule Early and Schedule Late use operand definitions and exact
uses to constrain placement (§§2.2–2.3). Section 2.4 favors shallower loop nests
and then later control positions. The search here applies those priorities to
one tracked live binding in the typed single-latch loop with a saved preheader
prefix. [PLDI ’95 paper][paper] · [Checked header walk][walk]

`PreheaderSearch.latest?` tries the actual physical cuts from the end of the
current saved prefix through cut zero. It calls `Layout.emit?` at each visited
cut for the same original binding identity. The first success is the latest
accepted cut in the enumerated prefix, and the result includes its typed
emission. `latest?_some`, `latest?_none`, and `latest?_max` certify the bound,
exhaustion, and ordering. On an invariant layout, the existing checked
enumeration covers every cut the emitter admits. [Definitions][defs] ·
[Theorems][thms]

`rank?` passes the discovered cut through the checked header-walk ranker.
`rank?_spec` identifies its preheader alternative with the exact result
of the search. When search is exhausted, cut zero already has a checked
refusal. Both alternatives are computed from the input CFG. The existing
depth policy selects the block, preferring the later header block at equal
depth. A preheader winner is the latest accepted physical cut there, and
a header winner is the latest position visited by the bounded rightward
walk. Optimality is scoped to those candidates. [Ranking proofs][thms]

`rank?_sites` matches operand definitions, ordinary reads, and exact
incoming Φ source, slot, and argument index with the header candidate.
The proofs refuse cuts outside the prefix, cuts before an operand's
physical definition, and preheader reads of a header operand. The latter
would require the header to dominate the entry. [Placement and refusal proofs][thms]

`rank?_hoist` identifies the winning emitted CFG. Under the saved-layout
invariant and matching prefix values, `latest?_packets` proves entry and
feedback prepend one saved result. Both header occurrences retain their
own packets, including the untaken edge. Exit keeps its entire argument
tuple. A header winner uses the walk's exact packet law. `rank?_run_eq`
and `rank?_denotePart` compare both outcomes with the input under the
existing packet assumptions. The same block visits justify common fuel.
[Routing and observation proofs][thms]

The fixture rejects a nomination at cut 0 and admits physical cuts 1 and 2.
The old nomination falls back to header index 3, and the search chooses
cut 2 at depth 0 over the depth-1 header. The two admitted cuts place the new
save in different physical slots. The regression also rejects a cut beyond
the prefix and the preheader placement of a latch-dependent binding. It
checks entry, two feedback visits, the exact exit, and both outgoing packets.
Fuels 3 and 4 exhaust, and fuel 5 returns 4. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Regression
cat >/tmp/gcm-preheader-cut-search.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Example
#eval observe
#eval refused
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-preheader-cut-search.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[walk]: sea-of-nodes-gcm-saved-header-walk.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Regression.lean

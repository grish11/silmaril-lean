# Replay checked GCM choices on the current layout

This driver applies the existing physical preheader search and rightward
header walk to one live binding at a time in the saved single-latch loop.
Click's Schedule Early, Schedule Late, and loop-depth selection motivate the
per-binding checks and ranking (§§2.2–2.4). The caller orders the origins and
supplies a crossing budget for each header walk. [PLDI ’95 paper][paper] ·
[Physical cut search][search]

`Sequence.run` resolves each original identity on the current typed CFG.
It runs the existing ranker, which collects current operand and exact use
sites, checks the physical preheader cuts, and compares them with the
bounded header walk. The trace stores the invocation and its successful
equation. The type of the remaining trace starts at that choice's exact
selected layout, including any newly saved word. A refused rank reports
the failing request and its position. A live request can retain its
current position when ranking selects it. [Definitions][defs] ·
[Replay equations][thms]

`choice_preserves` transports three premises to the selected CFG.

- The physical layout agrees with its canonical append reference.
- The saved packet routes the input to the same underlying base CFG, and
  the saved slots and surviving header origins account for the full inventory.
- The append reference computes the supplied saved packet at the given input.

For a header winner, the checked adjacent edits permute the surviving
identities and preserve the prefix and packet routing. For a preheader
winner, the selected splice adds the evaluated result to the saved packet
and preserves the remaining arguments and exit tuple. `trace_preserves`
composes those laws, so the initial premises supply all later steps.
`trace_run_eq` and `trace_denotePart` compare the final CFG with the
initial saved CFG at common fuel and under partial observation.
[Preservation proofs][thms]

In the lowered fixture, origin 6 reads origin 5. Initially, origin 6 has
no accepted preheader cut. Moving origin 5 to physical cut 2 adds a save
and shifts origin 6's header index from 4 to 3. The new producer definition
is visible at physical cut 3, now the only accepted preheader cut for
origin 6. The two moves preserve the observed exit word 9, including the
false-edge argument, and carry both saved values in entry and feedback.
The mixed fixture moves origin 4 within the header before locating
origin 5 at its new index. Repeating origin 5 after saving it produces
a refusal at the second request. [Example][example] · [Regression][regression]

Local rank applies to each request's represented cuts on its current
CFG. The driver supports caller-ordered requests for the pure, total
single-latch profile. It leaves global sequence choice to the caller.

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Regression
cat >/tmp/gcm-ranked-replay.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Example
#eval observe
#eval mixed
#eval refused
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-ranked-replay.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.PreheaderSearch.Sequence.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[search]: sea-of-nodes-gcm-preheader-search.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Sequence/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Sequence/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Sequence/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/PreheaderSearch/Sequence/Regression.lean

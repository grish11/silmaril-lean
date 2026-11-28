# Dominator-tree synthesis for the emitted (post-hoist) loop CFG

Click's PLDI ’95 §2.1 computes dominance before placement. The existing
[pre-hoist certificate][loop-dominance] builds a bespoke address table
directly for the *source* single-latch loop (`SourceLabel`). Composed
executors such as [`LoopHoist.Corridor.pickAndHoist?`][corridor-hoist] emit a
*different* typed CFG afterward, over `GCM.LoopHoist.Label saved carried
result extra` with a widened header bank, and no numbering or certified
`DominatorTree` existed for that emitted label family.
[PLDI ’95 paper][paper] · [Archived PDF][pdf] · [General synthesis][synthesis]

## What this adds

`Dominance.Emitted.stage` numbers the emitted CFG's two named blocks
(header, exit) past the anonymous entry, exactly mirroring the pre-hoist
`LoopHoist.Dominance.stage`. `Dominance.Emitted.synthesize?` passes that
numbering straight to the existing, fully generic
[`GCM.Dominance.Tree.Synthesis.synthesize?`][synthesis]: this file adds only
the injective numbering that function needs for the emitted label family,
on a successor-closed two-block inventory. It is a direct application of the
existing public instance, not a second dominance algorithm.
[Definitions][defs]

## Scope

This is a reachability/dominance prerequisite only. It does **not** resolve
operand origins in the emitted header (the `Origins`/`originSites` tracking
`GCM.LoopHoist` uses for the *source* loop has no emitted-CFG counterpart
yet), and it does **not** make the pinned Φ read at the exit — or any other
use — movable. Both stay open, matching the recorded
[`ExitSink` coverage gap][exit-sink]: closing it needs an operand-site
resolver for the emitted header, which this module does not attempt.

## Example

The fixture reuses the existing [`LoopHoist.Corridor.Example`][corridor-example]
loop, hoists its second header binding into the preheader
(`Corridor.pickAndHoist? (loop false) 1`), and synthesizes a dominator tree
for the actual emitted CFG. `headerDominatesExit` checks that the header is
reachable and dominates the exit; `entryDominatesHeader` checks the same for
the anonymous entry and the header; `exitDoesNotDominateHeader` checks that
dominance is directional, not an equivalence.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted.Regression
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted.Defs
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted.Example.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted.Regression
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[synthesis]: sea-of-nodes-gcm-synthesized-dominator-tree.md
[loop-dominance]: sea-of-nodes-gcm-loop-dominance.md
[corridor-hoist]: sea-of-nodes/optimization/sea-of-nodes-gcm-corridor-loop-hoist.md
[corridor-example]: sea-of-nodes/optimization/sea-of-nodes-gcm-corridor-loop-hoist.md
[exit-sink]: sea-of-nodes/optimization/sea-of-nodes-gcm-loop-exit-sink.md
[defs]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Dominance/Emitted/Defs.lean
[example]: ../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Dominance/Emitted/Example/Defs.lean
[regression]: ../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Dominance/Emitted/Regression.lean

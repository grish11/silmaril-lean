# Choosing between a header cut and a preheader splice

Click's Schedule Early and Schedule Late use operand definitions and exact
use occurrences to bound the legal blocks (§§2.2–2.3). Section 2.4 takes the
most control-dependent block in the shallowest loop nest. This slice applies
that priority to a pair in the existing pure, total single-latch CFG. The
caller nominates one original binding identity and one physical preheader
cut. The other candidate is the binding's original in-loop header cut.
[PLDI ’95 proceedings][paper] · [Saved-layout replay][layout]

`CrossBlock.analyze?` resolves the surviving identity in the current header.
The saved and immutable operands resolve through the typed physical slot map.
The latch and preceding header results resolve to their local definition
cuts. The retained candidate needs a live use and passes the same structural
availability and use checker. The preheader candidate is the actual
`Layout.emit?` splice. `analyze?_candidates` proves that both admitted cuts
refer to the same binding, operand definitions, ordinary reads, and exact
incoming Φ occurrences. `analyze?_refuses_local` excludes a preheader
alternative if any operand is header-local. [Definitions][defs] · [Theorems][thms]

The ranker synthesizes dominance and certifies the forest on the physical
CFG. It selects the preheader when the splice succeeds and its depth is
strictly smaller. At equal depth it retains the header, the later control
position by dominator address length. `selected_minDepth` proves the ranking
over the admitted pair. The entry is depth zero by the existing natural-loop
theorem. The candidate set is the current header position and the nominated
preheader cut. A nontrivial move within this saved header would need a splice
and routing proof for its saved-label family. Existing intra-header swaps
operate on the source label family. [Theorems][thms]

`analyze?_replay` identifies the exact emitted CFG. Retaining the binding
replays an empty list and keeps the current CFG. Hoisting replays the checked
splice. The new word is prepended to the original entry and feedback packets,
and the exact exit packet is retained. Under the existing packet and prefix
invariants, `analyze?_run_eq` and `analyze?_denotePart` preserve common-fuel
runs and partial denotation. The splice adds a let to the entry and removes
one from the header. The same entry, header, and exit block visits align the
fuel on both sides. With the verified two-save seed, CFG block fuel `b + 3`
corresponds to native backedge budget `b`. [Theorems][thms]

The fixture compares header cut 3 at depth 1 with preheader cut 1 at depth 0.
A later-control-only comparison favors the header, and including depth
selects the preheader. The selected binding has two ordinary reads and
supplies argument zero on the header's false exit occurrence. The regression
checks the entry, two feedbacks, exact exit, exhaustion, and return. A separate
latch-dependent binding retains the legal header cut when the outside splice
is refused. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Regression
cat >/tmp/gcm-cross-depth-cut.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Example
#eval observe
#eval refused
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-cross-depth-cut.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[layout]: sea-of-nodes-gcm-hoist-discovery.md#replaying-a-finite-list-of-physical-placements
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/CrossBlock/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/CrossBlock/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/CrossBlock/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/CrossBlock/Regression.lean

# Checked rightward placement in a saved loop header

Click's Schedule Early and Schedule Late bound placement by operand definitions
and exact uses (§§2.2–2.3). Section 2.4 prefers the most control-dependent
block in the shallowest loop nest. This walk checks one live, pure, total
binding in the existing typed single-latch CFG with a saved preheader prefix.
Its header search goes one position later at a time.
[PLDI ’95 paper][paper] · [Adjacent saved-header splice][splice]

`walk?` takes an original binding identity and a crossing budget. It resolves
the current index `i` on the actual CFG and requests cut `i + 2` before removal.
After the typed splice it resolves the same identity on the emitted CFG and
checks index `i + 1`. Each step retains the successful checker equation, the
next live binding, and the index increment. `step_cut` connects the requested
cut and the translated index. `trace_sites` identifies the initial operand
sites, ordinary reads, and exact incoming Φ source, slot, and argument index
at every visit. [Definitions][defs] · [Theorems][thms]

The trace contains the initial CFG and each accepted CFG. When a step is
refused it records that failure at the final visit. Reaching the crossing
budget stops without testing the next cut. Initial refusal means the layout
or live origin failed its check. `trace_latest` proves the final visit is
latest among those visited, using the binding index in each emitted header.
The proof covers this one-directional chain of checked splices and the
supplied budget.

`rank?` compares that chain with one nominated physical preheader cut on
the input CFG. It applies the existing certified depth policy to the two
blocks, then takes the latest visited position when the choice stays in
the header. The selected header cut is reported in the emitted header's
coordinates. `selected_minDepth` and `selected_latest` formalize the two
parts of the ranking. [Ranking and observation laws][thms]

The walk keeps the entry and exit blocks and their exact transfers. Both
header successor packets agree separately, including the untaken branch.
`trace_run_eq` compares returns and exhaustion at the same block fuel, and
`trace_denotePart` compares partial observations. Cross-block selection
inherits the existing saved-packet assumptions for the preheader splice.
[Observation laws][thms]

The fixture starts from an actual lowered saved loop and moves origin 5
through indices 1, 2, and 3. The next request at pre-removal cut 5 would cross
an ordinary read at cut 4. The exit use stays at argument zero of the false edge.
Entry, two feedback visits, exit, and both outgoing packets agree. Fuel
3 and 4 exhaust, and fuel 5 returns 4. The ranking chooses the latest
header visit when preheader cut 0 is too early for an operand. Admitting
cut 1 chooses the depth-0 preheader over the depth-1 header.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Regression
cat >/tmp/gcm-saved-header-walk.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Example
#eval observe
#eval limited
#eval ranking
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-saved-header-walk.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Walk.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[splice]: sea-of-nodes-gcm-saved-header-splice.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/HeaderSplice/Walk/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/HeaderSplice/Walk/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/HeaderSplice/Walk/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/HeaderSplice/Walk/Regression.lean

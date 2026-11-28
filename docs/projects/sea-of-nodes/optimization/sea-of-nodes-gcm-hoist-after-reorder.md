# Reordering a header before a checked preheader hoist

Click's PLDI ’95 §§2.2–2.4 constrain placement by definitions and uses,
including Φ operands on incoming CFG edges. Section 2.4 notes that one
placement can change the legal position of another. This slice composes
checked intra-header placement with one header-to-preheader move in
the existing typed single-latch loop. [Proceedings][paper] ·
[Archived PDF][pdf] · [Sea of Nodes source map][coverage]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`AfterReorder.schedule?` takes the native loop, a priority list for the
existing header planner, and an original identity to hoist. It returns
a plan with the planner's current-coordinate header requests and the
original hoist identity. `replay?` reconstructs the tracked header
using the explicit sequence API, then resolves the hoist identity
through that header's origin order.
[Definitions][defs] · [Header priorities][priority]

The hoist runs the synthesized corridor on the actual reordered CFG.
It resolves the binding's current operand origins and exact uses,
including Φ source slots and argument indices. The existing emitter
requires the chosen preheader cut zero and captured operands. A request
that misses those gates yields `none`. The hoist adds one pure total
binding to the existing preheader and routes its value as a header
argument on entry and feedback. The header sequence preserves the
canonical exit, which returns its sole block argument. This profile
ends at the single cross-block hoist.
[Definitions][defs] · [Preheader hoist][hoist]

`schedule?_replay` gives equality with the actual emitted CFG.
`replay?_placement` proves the cut is legal on the reordered CFG.
`replay?_routes` proves the saved value and original latch reach the
header on entry and feedback and the exact exit argument is preserved.
The proof uses the existing checked header replacement and hoist
routing laws. Both steps execute the same CFG block visits, so
`replay?_run_eq` gives equality at every fuel. The native backedge
budget still uses CFG fuel `budget + 3`. The partial denotation
agrees, including undefinedness. [Theorem header][thms]

The example moves the comparison from index 2 to the front.
The captured addition, originally at index 1, is now at index 2.
Stale index 1 names the latch-dependent addition. The chooser places
that binding at header cut 0, and the preheader emitter refuses it.
Hoisting the captured addition changes preheader/header binding
counts from `(2, 4)` to `(3, 3)`. The regression observes entry and
both feedback argument pairs, the singleton exit payload, and runs
with zero and two feedbacks. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Example.Defs
cat >/tmp/gcm-hoist-after-reorder-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Example
#eval observe 1 -- some ([(2, 0)], 3, 3, [none, none, some 2])
#eval observe 0 -- none
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-hoist-after-reorder-example.lean

make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[priority]: sea-of-nodes-gcm-header-priority.md
[hoist]: sea-of-nodes-gcm-corridor-loop-hoist.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Regression.lean

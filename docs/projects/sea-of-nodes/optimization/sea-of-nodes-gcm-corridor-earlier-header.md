# Moving one binding to an earlier loop-header cut

Click's PLDI ’95 §§2.2–2.4 constrain code motion by operand definitions and
uses, including reads on the incoming CFG edge of a Φ. The existing
corridor chooser applies those block bounds, checks actual local cuts, and
uses the first legal cut in enumeration order to break ties in one block.
Here the selected cut drives a sequence of checked adjacent swaps in the
pure typed lowering of a single-latch loop. [Proceedings][paper] ·
[Archived PDF][pdf] · [Corridor chooser][corridor]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`Earlier.pickAndMove?` takes one nominated header binding index.
It resolves def/use sites and runs the synthesized chooser on the input
CFG once. It returns the chosen original-CFG cut. With original index
`i` and target cut `t < i`, removal leaves the cut index `t` unchanged.
The emitter swaps at `i - 1`, then moves the binding left until it reaches
`t`. Each swap reads the current typed binding and recomputes its operand,
suffix and edge-argument names. Those intermediate indices belong to the
successive emitted headers. The emitter installs a new CFG only after the
whole sequence succeeds. [Definitions][defs] · [Adjacent swap][adjacent]

The scope is one pure total binding moving earlier within the same header.
The moved operation's operands must all be in scope before each crossing.
The prefix, the relative order of the crossed bindings and the remaining
suffix are kept. A failed local check, a destination in another block,
or reinsertion at the original position yields `none`. Use
`Header.pickAndMove?` for the adjacent-only API and
`Corridor.pickAndHoist?` for preheader placement. [Definitions][defs] ·
[Preheader hoist][hoist]

`pickAndMove?_placement` ties a successful result to the synthesized legal
cut in the original CFG. `pickAndMove?_order` proves the exact new order of
operation symbols and type signatures. The frame proof composes
`Header.swapAt?_eval`, preserving the selected successor and its complete
argument tuple. The shared header replacement laws give entry, bounded
CFG, native backedge-budget and partial denotation agreement. A one-position
target agrees with the existing adjacent emitter. [Theorem header][thms]

In the example, binding 3 moves across two multiplies to cut 1. The
multiplies depend on one another and keep their relative order. The sum
feeds the feedback edge, and the second multiply feeds the exit edge.
The regression checks both transfers, zero and two backedges, and fuel
exhaustion. When the sum instead reads the first multiply, the chooser
selects cut 2. Trying to force cut 1 fails at the second swap.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Example.Defs
cat >/tmp/gcm-earlier-header-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Example
#eval observe false
-- some ((1, 1), ["addi", "addi", "muli", "muli", "ult"], [none, none, some 72])
#eval observe true
-- some ((1, 2), ["addi", "muli", "addi", "muli", "ult"], [none, none, some 132])
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-earlier-header-example.lean

make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[corridor]: sea-of-nodes-gcm-corridor-placement.md
[adjacent]: sea-of-nodes-gcm-corridor-header-motion.md
[hoist]: sea-of-nodes-gcm-corridor-loop-hoist.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Earlier/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Earlier/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Earlier/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Earlier/Regression.lean

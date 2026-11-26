# Moving one binding within the loop header

Click's PLDI ’95 §§2.2–2.4 bound placement by operand definitions and uses,
with each Φ operand read on its incoming CFG edge. The synthesized corridor
uses those block constraints and the repository's local cut checks. It
breaks ties within the same block by the first legal cut in enumeration
order. The adjacent rewrite here realizes one such cut in the existing pure
typed single-latch lowering. [Proceedings][paper] · [Archived PDF][pdf] ·
[Corridor chooser][corridor]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`Header.pickAndMove?` takes a native loop and a zero-based header binding
index. The existing resolver computes typed operand origins and exact
use sites, including the successor slot and argument index. The emitter
consumes the chosen source cut. If the cut follows the removed binding it
decrements the cut by one. The original cuts immediately before and after
the binding both translate to its old index. This emitter accepts exactly
the earlier adjacent insertion index and checks that the moved operands
can drop the crossed binding from their scope. Other placements return
`none`. Preheader cut zero remains available through the existing
`Corridor.pickAndHoist?` API. [Definitions][defs] · [Preheader hoist][hoist]

The splice keeps the prefix, moves the nominated operation ahead of the
crossed operation, and weakens the crossed operation's operands. The suffix
exchanges the two de Bruijn references under every subsequent binding.
It applies the same renaming to the condition and to each edge's operands
in their original slot and argument order. The preheader, exit and block
argument types stay fixed. The scope is one pure total binding and one
adjacent earlier move in the header. General CFG scheduling, longer moves,
repeated moves and effectful speculation are outside this profile.
[Definitions][defs]

`pickAndMove?_placement` ties the emitted move to the synthesized legal cut
and its translated insertion index. `pickAndMove?_frames` proves entry
agreement and equality of each block's successor frame or return. The
`_run_eq`, `_budget` and `_denotePart` theorems preserve every CFG fuel
observation, the native backedge budget at fuel `budget + 3`, and partial
results including undefinedness. [Theorem header][thms]

In the example, binding 2 is a sum of a latch-dependent value and the
captured stride. Its first operand is ready at header cut 1, so the chooser
places it ahead of an independent multiply. The feedback slot transfers
the sum and the exit slot transfers the multiply. The checked examples
include both edge transfers, zero and two backedges, and insufficient fuel.
When the nominated sum instead uses the multiply, the selected cut is
its original index 2 and emission is refused. [Example][example] ·
[Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example.Defs
cat >/tmp/gcm-header-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Example
#eval observe false
-- (some (1, 1), ["addi", "muli", "addi", "ult"], some (["addi", "addi", "muli", "ult"], [none, none, some 12]))
#eval observe true
-- (some (1, 2), ["addi", "muli", "addi", "ult"], none)
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-header-example.lean

make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[corridor]: sea-of-nodes-gcm-corridor-placement.md
[hoist]: sea-of-nodes-gcm-corridor-loop-hoist.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Regression.lean

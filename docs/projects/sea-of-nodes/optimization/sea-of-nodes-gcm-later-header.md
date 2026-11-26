# Moving one binding to an explicit later header cut

Click's PLDI ’95 §§2.2–2.4 constrain placement by definitions and uses.
A Φ operand is read on its incoming CFG edge. This slice applies those
constraints to an explicit cut in the existing pure typed single-latch
header. The automatic corridor chooser continues to rank blocks and
select the first feasible local cut in enumeration order.
[Proceedings][paper] · [Archived PDF][pdf] · [Corridor chooser][corridor]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`Header.Later.moveAt?` takes a zero-based binding index `i` and an
original CFG cut `c`. It accepts only a header insertion with `i + 1 < c`.
Cut `c` translates to insertion index `c - 1` after removal. The
existing source binding resolver supplies the actual operand origins
and exact use sites. The finite CFG cut checker validates the original
cut, including local read order and each Φ source, successor slot and
argument index. There is no caller-supplied dominance evidence.
[Definitions][defs] · [Cut checker][checker]

The emitter starts at the original binding index and repeatedly applies
`Header.swapAt?` to the current typed block. The next binding must be
able to read all of its operands before the moved result becomes
available. Every swap renames the suffix and retains the successor slots
and the order of their arguments. Failure yields `none`. This covers
one pure total binding moving later within one header. The adjacent,
earlier and preheader entry points serve their existing destinations.
[Definitions][defs] · [Adjacent swap][adjacent] · [Earlier motion][earlier]

`moveAt?_placement` proves legality on the input CFG and the cut
translation. `moveAt?_refuses_lateUse` proves refusal across an exact
same-block read. `moveAt?_order` gives the exact emitted order of operation
symbols and type signatures. The frame proof composes the adjacent swap
law and preserves the complete feedback and exit tuples. The shared
header replacement laws give equality at every CFG fuel, at native
backedge budget `budget` with CFG fuel `budget + 3`, and for partial
denotation including undefinedness. [Theorem header][thms]

In the example, binding 0 feeds the backedge. Original cut 3 places it
after two multiplies at insertion index 2, while the automatic chooser
still selects header cut 0. The regression checks the intermediate
and final opcode order, two distinct successor transfers, zero and two
backedges, and fuel exhaustion. When the second multiply instead reads
the moved addition, cut 2 is accepted and cut 3 is refused.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example.Defs
cat >/tmp/gcm-later-header-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Example
#eval rankedCut false -- some (1, 0)
#eval observe false 3 -- some (["muli", "muli", "addi", "ult"], [none, none, some 32])
#eval observe true 2  -- some (["muli", "addi", "muli", "ult"], [none, none, some 20])
#eval observe true 3  -- none
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-later-header-example.lean

make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[corridor]: sea-of-nodes-gcm-corridor-placement.md
[adjacent]: sea-of-nodes-gcm-corridor-header-motion.md
[earlier]: sea-of-nodes-gcm-corridor-earlier-header.md
[checker]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/Dominance/Placement/Thms.lean
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Later/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Later/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Later/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Later/Regression.lean

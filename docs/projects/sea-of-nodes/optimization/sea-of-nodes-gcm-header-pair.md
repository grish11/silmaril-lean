# Applying two checked loop-header placements

Click's PLDI ’95 §§2.2–2.4 constrain placement by definitions and uses,
including Φ operands at their incoming CFG edges. Section 2.4 notes that
placing one instruction can change the latest legal position of another.
This slice realizes that dependency by recomputing the actual sites after
each change to the typed single-latch header. The automatic corridor
continues to use its existing ranking. [Proceedings][paper] ·
[Archived PDF][pdf] · [Corridor chooser][corridor]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`Header.Pair.schedule?` takes two explicit requests. Each supplies a
zero-based binding index and a cut counted in the **current** header before
that binding is removed. The first request uses the native loop's lowering.
The second uses the CFG emitted by the first. Callers specify the second
coordinates in that CFG. For example, a later cut at `c` places the binding
at index `c - 1` after removal. [Definitions][defs]

Each step resolves the typed operands, ordinary uses, and exact Φ
occurrences in its own input CFG. It runs the finite cut checker and calls
the existing earlier or later emitter. The second request must name an
index different from the first binding's translated insertion index.
A failing request or a repeat returns `none` for the pair. A successful
result contains the final CFG. The scope is exactly two distinct pure
total bindings in one header of the existing single-latch loop.
[Definitions][defs] · [Earlier motion][earlier] · [Later motion][later]

`schedule?_steps` exposes the intermediate CFG and the distinctness
condition. `move?_checked` ties each emitted step to the checker on that
step's CFG. `schedule?_refuses_second` proves that a rejected second
request yields no rewritten CFG. The header evaluation equalities
compose, giving exact feedback and exit tuples, equality at every CFG
fuel, native backedge-budget equality at fuel `budget + 3`, and partial
denotation equality including undefinedness. [Theorem header][thms]

In the example, request `(0, 3)` moves the addition after the multiplies
and request `(3, 0)` moves the comparison to the front of the resulting
header. The alternative second request `(0, 2)` is legal on the original
CFG. In the intermediate header, index zero names a multiply read at
cut 1, so in that CFG the request is refused. The regression checks both
successor tuples, zero and two backedges, insufficient fuel, and refusal
to move the first binding again. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example.Defs
cat >/tmp/gcm-header-pair-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Example
#eval observe earlierSecond
#eval observe blockedSecond
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-header-pair-example.lean

make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[corridor]: sea-of-nodes-gcm-corridor-placement.md
[earlier]: sea-of-nodes-gcm-corridor-earlier-header.md
[later]: sea-of-nodes-gcm-later-header.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Pair/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Pair/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Pair/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Pair/Regression.lean

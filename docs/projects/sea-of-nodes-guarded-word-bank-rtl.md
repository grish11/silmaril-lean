# Checked two-word feedback with a runtime guard

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Thms`.
`Guarded.lowerChecked` checks one native `Loop.Graph` and returns a machine
RTL program and a typed λSSA CFG for that graph. Use `Generic.phiView` on
the original graph to inspect the emitted occurrence-indexed Φ view.
The checker reuses the one-word profile's opcode and provenance checks.
The existing bank emitter supplies the RTL blocks and simultaneous
argument transfer. [Checked guard baseline][guards] ·
[Word-bank emitter baseline][rows] · [Paired countdown baseline][paired]

The admitted loop takes two i64 inputs and enters the header with those
two words. The first operation wraps `oldFirst + oldSecond` or
`oldFirst - oldSecond`. An `eq` or `ne` against a fixed i64 limit
selects feedback with `(updated, oldFirst)` or exit with `oldSecond`.
The return and copy positions are fixed in this profile.

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL (Profile)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def equalSeven : Profile := ⟨.add, 7, .eq⟩

#eval (lowerChecked (graph equalSeven)).map fun (rtl, ssa) =>
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 10 0 [5, 2] mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model (pair 5 2)) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)
-- some (some [5], some 5)
```

`lowerChecked_typed` certifies both targets. `activation_agrees` pairs
the four actual RTL header steps with evaluation of the λSSA header.
`incoming_alignment` identifies the actual entry and feedback occurrences
in either presentation order, and `feedback_slot_transfer_iff` reads the
entire latched tuple. `returns_iff` equates finite observations with the
same returned word and complete memory. Reflection consumes the finite
machine run and needs no termination assumption. [Theorems][thms]

On input `(5, 2)` the loop transfers `(7, 5)` and then exits with `5`.
A sequential copy would feed back `(7, 7)`, which the exact header proof
rules out. The matcher also refuses that same-typed rewiring. Input
`(6, 2)` exits immediately with `2`. [Regression][regression]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.RowRegression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Phi.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Regression
```

[guards]: https://github.com/hiloopai/silmaril-lean/pull/3679
[rows]: https://github.com/hiloopai/silmaril-lean/pull/3608
[paired]: https://github.com/hiloopai/silmaril-lean/pull/3631
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Thms.lean
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Regression.lean

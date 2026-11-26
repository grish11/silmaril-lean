# Guarded feedback rows in RTL and explicit Φ

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Thms`.
`checkPlan` admits a typed i64 bank at a supplied width. Entry and copy
indices are zero-based and checked against the full bank. Each computation
reads two old bank slots and writes a fresh temporary. Destinations are
distinct. The guard names one computed producer and its destination.
The checker requires them to agree. The guard compares that producer to
a fixed i64 limit with `eq` or `ne`. Exit projects one old bank slot.
[Guarded pair][pair] · [Row compiler][row] · [Explicit Φ baseline][phi]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Thms
import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Fuel.Thms

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (model word)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing (WordTuple words)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (inputEnv)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA

def crossed : Spec where
  entry := [0, 1, 2]
  copies := [0, 1, 0]
  updates := [⟨.sub, 1, 0, 1⟩, ⟨.add, 0, 0, 1⟩]
  guardOrigin := .output 1 0
  guardDestination := 0
  comparison := .eq
  limit := 7
  exitSlot := 2

def sampleInput : WordTuple 3 := .cons (5 : Word) (.cons (2 : Word) (.cons (20 : Word) .nil))

#eval (lowerChecked 3 crossed).map fun (rtl, ssa) =>
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let machine := (rtl.runMain 12 0 (words sampleInput) mem).returnedValues?
  let typed := (Generic.Fuel.run model (inputEnv model sampleInput) 2 ssa).bind fun (_, packet) =>
    (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
  (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)
-- some (some [5], some 5)
```

The first activation feeds back `(7, 3, 5)`. The guard's addition reads
old slot 1 even though the subtraction replaces it. Slot 2 copies old
slot 0. The next guard exits and reads slot 2. Changing the guard to
`.output 0 0` is refused because producer 0 writes slot 1. [Regression][regression]

`lowerChecked_typed` certifies the two outputs.
`activation_agrees` runs the actual emitted RTL and λSSA headers and
proves the same guard choice, complete feedback tuple or exit projection,
and unchanged memory. `feedback_slot_transfer_iff` identifies the exact
feedback packet in either predecessor order. The shared proofs cover a
single header activation at arbitrary bank width. The runnable example
also exercises a complete return. [Theorem header][thms]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.RowRegression
```

[pair]: https://github.com/hiloopai/silmaril-lean/pull/3707
[row]: https://github.com/hiloopai/silmaril-lean/pull/3608
[phi]: https://github.com/hiloopai/silmaril-lean/pull/3631
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Regression.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Thms.lean

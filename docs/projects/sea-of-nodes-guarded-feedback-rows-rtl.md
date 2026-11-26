# Guarded feedback rows in RTL and explicit Φ

Import `Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms`.
`checkPlan` admits a typed i64 bank at a supplied width. Entry and copy
indices are zero-based and checked against the full bank. Each computation
reads two old bank slots and writes a fresh temporary. Destinations are
distinct. The guard names one computed producer and its destination.
The checker requires them to agree. The guard compares that producer to
a fixed i64 limit with `eq` or `ne`. Exit projects one old bank slot.
[Guarded pair][pair] · [Row compiler][row] · [Explicit Φ baseline][phi]

```lean
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms

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
  comparison := .ne
  limit := 14
  exitSlot := 2

def sampleInput : WordTuple 3 := .cons (5 : Word) (.cons (2 : Word) (.cons (20 : Word) .nil))

#eval do
  let plan ← checkPlan 3 crossed
  let (rtl, ssa) ← lowerChecked 3 crossed
  let mem := Memory.ofList 4 [29, 71, 53, 11]
  let observe (backedges : Nat) :=
    let machine := (rtl.runMain (plan.rtlFuel backedges) 0 (words sampleInput) mem).returnedValues?
    let typed := (Generic.Fuel.run model (inputEnv model sampleInput) (backedges + 1) ssa).bind fun (_, packet) =>
      (Generic.Fuel.decodeArgs model [word] packet).map fun fields => Silmaril.SSA.RVSDG.Tuple.get fields .head
    (machine.map (List.map BitVec.toNat), typed.map BitVec.toNat)
  pure (observe 1, observe 2)
-- some ((none, none), some [7], some 7)
```

The first two activations feed back `(7, 3, 5)` and `(10, 4, 7)`.
The guard's addition reads old slot 1 even though the subtraction
replaces it, and slot 2 copies old slot 0. The next comparison sees 14
and exit projects the old slot 2, which is 7. Changing the guard origin
to `.output 0 0` is refused because producer 0 writes slot 1.
[Activation regression][regression] · [Whole-loop regression][fuel-regression]

`activation_agrees` proves the guard choice and complete feedback tuple
or exit projection. `incoming_alignment` identifies the actual entry
and feedback branches in either predecessor order. The two orders
recover the same branch terms of the emitted CFG. [Activation theorems][thms]

For a row with `k` computations, each RTL activation uses `k + 3`
steps for the computations, two guard producers, and the branch.
A return after `b` backedges needs exactly `(k + 3) * (b + 1) + 2`
RTL fuel including entry and return, and `b + 1` λSSA visits.
Here the first return needs 17 RTL steps and 3 λSSA visits.
`runMain_fuel_iff` gives the threshold at arbitrary RTL fuel.
`bounded_returns_iff` and `bounded_absence_iff` compare observation at
the matched budgets. `returns_iff` relates the checked targets' finite
returns with the entire final memory equal to the initial memory.
The proofs cover the current pure single-header i64 bank profile.
[Whole-loop theorems][fuel-thms]

```sh
lake build --wfail +Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Regression \
  +Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Regression
```

[pair]: https://github.com/hiloopai/silmaril-lean/pull/3707
[row]: https://github.com/hiloopai/silmaril-lean/pull/3608
[phi]: https://github.com/hiloopai/silmaril-lean/pull/3631
[regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Regression.lean
[thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Thms.lean
[fuel-thms]: ../../Silmaril/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/Thms.lean
[fuel-regression]: ../../Silmaril/Proofs/Machine/SeaOfNodes/Loop/RTL/Routing/Guarded/Rows/Fuel/Regression.lean

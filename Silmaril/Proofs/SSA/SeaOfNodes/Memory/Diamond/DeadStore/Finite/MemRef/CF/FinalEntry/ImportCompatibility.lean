module

public import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.ImportCompatibility

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open DeadStore.Entry.Composition.Static
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {entry retained : Memory.Graph args} {store : PrefixStore args} {version : Nat}
variable {arm : Occurrence preds → Memory.Graph args} {candidate : Candidate args preds}
variable {suffix : Memory.Graph (.word :: args)} {input : Tuple (Val cells) args} {programs : Programs cells args preds}

-- The old executable equation still holds by reduction.
example : lower preds fits entry version arm candidate suffix input = (do
    let (selected, kept) ← Final.cut version entry
    let edited ← Finite.check preds selected arm candidate input
    some ⟨input, lowerBank preds fits cells (some entry) arm suffix,
      lowerBank preds fits cells (some kept) (fun i => edited[i.val]) suffix⟩) := rfl

example (emitted : lower preds fits entry version arm candidate suffix input = some programs) :
    ∃ (store : PrefixStore args) (retained : Memory.Graph args) (edited : Bank args preds),
      Final.cut version entry = some (store, retained) ∧
      Finite.check preds store arm candidate input = some edited ∧
      programs = ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some retained) (fun i => edited[i.val]) suffix⟩ :=
  Proofs.lower_replay (args := args) (cells := cells) (sites := sites) (preds := preds)
    (fits := fits) (entry := entry) (version := version) (arm := arm) (candidate := candidate)
    (suffix := suffix) (input := input) (programs := programs) (emitted := emitted)

example (emitted : lower preds fits entry version arm candidate suffix input = some programs)
    (accepted : Final.cut version entry = some (store, retained))
    (arrival : Occurrence preds) (initial : Buffer cells) :
    DeletesStores 1 (operations entry) (operations retained) ∧
      let exported := observe retained programs.input initial
      let originalBuffer := Buffer.mk (store.table.denote programs.input exported.2.cell).2
      observe entry programs.input initial = (exported.1, originalBuffer) ∧
        entryTransition programs.original programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, originalBuffer) ∧
        entryTransition programs.optimized programs.input arrival initial = (.inl ⟨.arm arrival, .nil⟩, exported.2) :=
  Proofs.lower_entry (entry := entry) (retained := retained) (store := store) (version := version)
    (emitted := emitted) (accepted := accepted) (arrival := arrival) (initial := initial)

example (emitted : lower preds fits entry version arm candidate suffix input = some programs)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    let packet := (arm arrival).denote input (entry.denote input initial.cell).2
    let result := suffix.denote (.cons packet.1 input) packet.2
    let expected := if fuel < 3 then none else some (result.1, Buffer.mk result.2)
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.original programs.input arrival fuel initial = expected ∧
      run programs.optimized programs.input arrival fuel initial = expected :=
  Proofs.lower_observations (input := input) (emitted := emitted)
    (arrival := arrival) (fuel := fuel) (initial := initial)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.ImportCompatibility

module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {entry : Memory.Graph args} {input : Tuple (Val cells) args}
variable {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {first second : Request args preds} {result : Result cells args preds}

/-- Replay each nomination on its exact typed table. The second original
CFG and input match the intermediate artifact when the second check succeeds. -/
theorem lower_replay (emitted : lower preds fits entry arm suffix input first second = some result) :
    lowerWithEntry preds fits entry first.version arm first.candidate suffix input first.facts = some result.first ∧
    lowerWithEntry preds fits result.first.edit.retained second.version arm second.candidate suffix input second.facts =
      result.second ∧
    match result.second with
    | none => True
    | some next =>
      next.programs.original = result.first.programs.optimized ∧ next.programs.input = result.first.programs.input :=
  Proofs.lower_replay emitted

/-- The final actual CFG preserves the selected occurrence, complete join
packet and finite return of the original at every common CF budget. -/
theorem lower_observations (emitted : lower preds fits entry arm suffix input first second = some result)
    (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := result.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial :=
  Proofs.lower_observations emitted arrival fuel initial

/-- The reported number of Stores is deleted. The final entry preserves
retained operation order, the entry word and every ordered Load readback. -/
theorem lower_retained (emitted : lower preds fits entry arm suffix input first second = some result)
    (index : Nat) (initial : Buffer cells) :
    let checkedInput := result.programs.input
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe entry checkedInput initial).1 = (observe result.retained checkedInput initial).1 ∧
      probe entry = probe result.retained :=
  Proofs.lower_retained emitted index initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence

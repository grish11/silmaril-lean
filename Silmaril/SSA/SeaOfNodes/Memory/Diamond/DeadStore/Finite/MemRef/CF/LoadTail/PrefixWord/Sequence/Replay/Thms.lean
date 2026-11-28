module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {input : Tuple (Val cells) args} {entry : Memory.Graph args}
variable {requests : List (Request args preds)}

/-- The emitted trace certifies each admission at the saved input and the
exact structural link between its source and the preceding artifact. -/
theorem lower_trace :
    Trace fits arm suffix input entry (lowerBank preds fits cells (some entry) arm suffix) requests
      (lower preds fits entry arm suffix input requests) :=
  Proofs.lower_trace

/-- The result preserves the original input and CFG and reports the
unconsumed suffix of the supplied plan. -/
theorem lower_accounting :
    let result := lower preds fits entry arm suffix input requests
    result.programs.input = input ∧ result.programs.original = lowerBank preds fits cells (some entry) arm suffix ∧
      result.remaining = requests.drop result.deleted :=
  Proofs.lower_accounting

/-- At every common CF budget the emitted endpoints agree on the selected
occurrence, complete join packet, return word and full final buffer. -/
theorem lower_observations (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower preds fits entry arm suffix input requests).programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      run programs.optimized programs.input arrival fuel initial = run programs.original programs.input arrival fuel initial :=
  Proofs.lower_observations arrival fuel initial

/-- The admitted prefix deletes exactly one Store per step, preserves
retained operation order, and keeps all emitted entry word readbacks. -/
theorem lower_retained (index : Nat) (initial : Buffer cells) :
    let result := lower preds fits entry arm suffix input requests
    let checkedInput := result.programs.input
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe entry checkedInput initial).1 = (observe result.retained checkedInput initial).1 ∧
      probe entry = probe result.retained :=
  Proofs.lower_retained index initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay

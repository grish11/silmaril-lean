module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore (throughLoad)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers.Repeat (DeletesStores operations storeCount)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args}
variable {suffix : Memory.Graph (.word :: args)} {input : Tuple (Val cells) args} {entry : Memory.Graph args}

/-- A success identifies an actual surviving Store version, its inferred
entry and arm evidence, and the existing emitter’s accepted result. -/
theorem find_checked {request : Request args preds} {stage : Emission cells args preds}
    (found : find fits arm suffix input entry = some (request, stage)) :
    request.version ∈ storeVersions entry ∧
      inferEntry request.version entry = some request.facts ∧
      inferCandidate preds request.facts.observed arm = some request.candidate ∧
      lowerWithEntry preds fits entry request.version arm request.candidate suffix input request.facts = some stage :=
  Proofs.find_checked found

/-- Exhaustion means that every actual Store version refused. -/
theorem find_eq_none_iff :
    find fits arm suffix input entry = none ↔
      ∀ version ∈ storeVersions entry, tryVersion fits arm suffix input entry version = none :=
  List.findSome?_eq_none_iff

/-- The discovered plan replays to exactly the returned artifacts,
with every discovered request admitted. -/
theorem lower_replayed :
    let result := lower preds fits entry arm suffix input
    Replay.lower preds fits entry arm suffix input result.requests = result.replay ∧
      result.replay.remaining = [] :=
  Proofs.lower_replayed

/-- Every surviving Store fails under the inference used by this
trailing-Load search on the final table. -/
theorem lower_exhausted :
    let retained := (lower preds fits entry arm suffix input).replay.retained
    ∀ version ∈ storeVersions retained, tryVersion fits arm suffix input retained version = none :=
  Proofs.lower_exhausted

/-- The discovered emitted CFGs agree on the selected occurrence,
complete join packet, return word and full buffer at every common budget. -/
theorem lower_observations (arrival : Occurrence preds) (fuel : Nat) (initial : Buffer cells) :
    let programs := (lower preds fits entry arm suffix input).replay.programs
    let before := entryTransition programs.original programs.input arrival initial
    let after := entryTransition programs.optimized programs.input arrival initial
    before.1 = .inl ⟨.arm arrival, .nil⟩ ∧ after.1 = .inl ⟨.arm arrival, .nil⟩ ∧
      armTransition programs.optimized programs.input arrival after.2 =
        armTransition programs.original programs.input arrival before.2 ∧
      CF.run programs.optimized programs.input arrival fuel initial =
        CF.run programs.original programs.input arrival fuel initial :=
  Proofs.lower_observations arrival fuel initial

/-- Each admitted step deletes exactly one Store and keeps the retained
entry operation order, Return word and Load readbacks. -/
theorem lower_retained (index : Nat) (initial : Buffer cells) :
    let result := (lower preds fits entry arm suffix input).replay
    let checkedInput := result.programs.input
    let probe := fun (graph : Memory.Graph args) => (throughLoad graph index).map fun block =>
      (observe block checkedInput initial).1
    DeletesStores result.deleted (operations entry) (operations result.retained) ∧
      (observe entry checkedInput initial).1 = (observe result.retained checkedInput initial).1 ∧
      probe entry = probe result.retained :=
  Proofs.lower_retained index initial

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search

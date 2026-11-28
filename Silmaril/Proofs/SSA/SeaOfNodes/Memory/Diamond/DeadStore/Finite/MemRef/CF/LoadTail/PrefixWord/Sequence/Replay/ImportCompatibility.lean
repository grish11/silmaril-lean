module

import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Correctness

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.ImportCompatibility

open RVSDG (Tuple)
open Quads.CFG (Predecessors)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {entry : Memory.Graph args} {input : Tuple (Val cells) args}
variable {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {first second : Request args preds} {result : Result cells args preds}

example : lower preds fits entry arm suffix input first second = (do
    let stage ← lowerWithEntry preds fits entry first.version arm first.candidate suffix input first.facts
    let next := lowerWithEntry preds fits stage.edit.retained second.version arm second.candidate suffix input second.facts
    some ⟨stage, next⟩) := rfl

example (emitted : lower preds fits entry arm suffix input first second = some result) :
    lowerWithEntry preds fits entry first.version arm first.candidate suffix input first.facts = some result.first ∧
    lowerWithEntry preds fits result.first.edit.retained second.version arm second.candidate suffix input second.facts =
      result.second ∧
    match result.second with
    | none => True
    | some next =>
      next.programs.original = result.first.programs.optimized ∧ next.programs.input = result.first.programs.input :=
  Proofs.lower_replay (args := args) (cells := cells) (sites := sites) (preds := preds) (fits := fits)
    (entry := entry) (arm := arm) (suffix := suffix) (input := input) (first := first) (second := second)
    (result := result) (emitted := emitted)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.ImportCompatibility

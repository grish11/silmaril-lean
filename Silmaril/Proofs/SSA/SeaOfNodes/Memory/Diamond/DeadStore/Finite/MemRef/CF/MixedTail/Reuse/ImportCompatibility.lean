module

import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Correctness

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.ImportCompatibility

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore.Search.Selection (storeVersions)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {arm : Occurrence preds → Memory.Graph args} {suffix : Memory.Graph (.word :: args)}
variable {entry : Memory.Graph args} {input : Tuple (Val cells) args} {result : Result cells args preds}

example : lower fits arm suffix input entry =
    (storeVersions entry).findSome? (tryVersion fits arm suffix input entry) := rfl

example (accepted : lower fits arm suffix input entry = some result) :
    result.version ∈ storeVersions entry :=
  (Proofs.lower_checked (args := args) (cells := cells) (sites := sites) (preds := preds)
    (input := input) (fits := fits) (arm := arm) (suffix := suffix) (entry := entry) (result := result)
    (accepted := accepted)).1

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.ImportCompatibility

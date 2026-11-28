module

import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Correctness

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.ImportCompatibility

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}
variable {fits : Fits preds} {entry : Memory.Graph args} {version : Nat}
variable {arm : Occurrence preds → Memory.Graph args} {candidate : Candidate args preds}
variable {suffix : Memory.Graph (.word :: args)} {input : Tuple (Val cells) args} {facts : Certificate args}

example : lower preds fits entry version arm candidate suffix input facts = (do
    let edit ← cut facts version entry
    if facts.check input && checkArms preds edit.address arm candidate input then
      some ⟨input, lowerBank preds fits cells (some entry) arm suffix,
        lowerBank preds fits cells (some edit.retained) arm suffix⟩
    else none) := rfl

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.ImportCompatibility

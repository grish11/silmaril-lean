module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Defs

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search

open RVSDG (Tuple)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells : Nat}

/-- Discover an overwrite within the original activation table, then
use the existing checked loop rewrite. -/
def rewrite (graph : Graph args) (removeVersion : Nat) (facts : Certificate args)
    (input : Tuple (Val cells) args) : Option (Graph args) := do
  let candidate ← Memory.DeadStore.Search.discover graph.body removeVersion facts
  Loop.DeadStore.rewrite graph candidate facts input

end Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search

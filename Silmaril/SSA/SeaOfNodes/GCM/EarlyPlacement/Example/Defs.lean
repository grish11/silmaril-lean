module

public import Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Example.Defs

/-! # Schedule Early and Schedule Late on the same typed diamond -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Example

open LatePlacement.Example (Label block blocks tree? number parallelUses bothArms)
open LatePlacement (lateBound?)

/-- Resolved definitions in three nested blocks, with a definition after the
local binding in the left arm. -/
def nestedDefs : List (Point Label) := [⟨none, 0⟩, ⟨block .left, 1⟩, ⟨block .fork, 0⟩]

/-- Display the bounds for the parallel left reads, legality of the two left
cuts, and whether discovery succeeds after adding the right incoming read. -/
def observe : Option (Nat × Nat × Bool × Bool × Bool) := do
  let tree ← tree?
  let early ← earlyBound? tree.1 nestedDefs
  let late ← lateBound? tree.1 blocks parallelUses
  return (number early, number late,
    checkPlacement tree.1 nestedDefs parallelUses ⟨block .left, 0⟩,
    checkPlacement tree.1 nestedDefs parallelUses ⟨block .left, 1⟩,
    (discoverPlacement tree.1 blocks nestedDefs bothArms).isSome)

end Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Example

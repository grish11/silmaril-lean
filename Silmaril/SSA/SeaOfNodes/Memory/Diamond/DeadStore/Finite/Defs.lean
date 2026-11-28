module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.CFG.Defs
public import Init.Data.Vector.OfFn

/-! Check the common entry Store on every occurrence in a finite predecessor bank. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite

open RVSDG (Tuple)
open Quads.CFG (Predecessors)

variable {args : List ValueSort} {cells sites : Nat}

/-- The position of a Region input is its identity, even when its source
block appears in several positions. -/
abbrev Occurrence (preds : Predecessors sites) := Fin (preds.rest.length + 1)

abbrev Candidate (args : List ValueSort) (preds : Predecessors sites) :=
  Occurrence preds → ArmOverwrite args

abbrev Bank (args : List ValueSort) (preds : Predecessors sites) :=
  Vector (Memory.Graph args) (preds.rest.length + 1)

/-- Each occurrence supplies its original ordered path and independent
overwrite evidence. All checks use the same scalar valuation. -/
def check (preds : Predecessors sites) (store : PrefixStore args)
    (arm : Occurrence preds → Memory.Graph args) (candidate : Candidate args preds)
    (input : Tuple (Val cells) args) : Option (Bank args preds) :=
  Vector.ofFnM fun occurrence => rewriteArm store (arm occurrence) (candidate occurrence) input

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite

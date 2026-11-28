module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Defs

/-! Delete a final entry Store before the checked finite switch. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open DeadStore.Entry.Composition.Static

variable {args : List ValueSort} {cells sites : Nat}

/-- Check every arm and emit a supplied entry cut. The entry cut's own
checker supplies its typed replay relation. -/
def lowerCut (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args)
    (edit : Option (PrefixStore args × Memory.Graph args))
    (arm : Occurrence preds → Memory.Graph args) (candidate : Candidate args preds)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args) : Option (Programs cells args preds) := do
  let (store, retained) ← edit
  let edited ← Finite.check preds store arm candidate input
  some ⟨input, lowerBank preds fits cells (some entry) arm suffix,
    lowerBank preds fits cells (some retained) (fun i => edited[i.val]) suffix⟩

/-- Preserve the actual typed entry prefix. The final Store has original
address and value ports, and every incoming occurrence must certify an overwrite. -/
def lower (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args) (version : Nat)
    (arm : Occurrence preds → Memory.Graph args) (candidate : Candidate args preds)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args) : Option (Programs cells args preds) :=
  lowerCut preds fits entry (Final.cut version entry) arm candidate suffix input

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry

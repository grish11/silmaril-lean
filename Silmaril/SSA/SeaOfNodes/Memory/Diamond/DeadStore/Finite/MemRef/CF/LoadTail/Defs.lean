module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Defs

/-! Preserve a certified trailing Load chain in the finite MemRef switch entry. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open DeadStore.Entry.Composition.Static
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells sites : Nat}

/-- Check the suffix certificate at the actual invocation. Keep the full
typed prefix, Load chain and Return wire when removing the final Store. -/
def cut (facts : Certificate args) (version : Nat) (entry : Memory.Graph args)
    (input : Tuple (Val cells) args) : Option (PrefixStore args × Memory.Graph args) :=
  if facts.check input then Final.cutWith (Final.LoadTail.checkTail facts) version entry else none

/-- The same typed input validates both the entry facts and every arm. -/
def lower (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args) (version : Nat)
    (arm : Occurrence preds → Memory.Graph args) (candidate : Candidate args preds)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args)
    (facts : Certificate args) : Option (Programs cells args preds) :=
  FinalEntry.lowerCut preds fits entry (cut facts version entry input) arm candidate suffix input

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail

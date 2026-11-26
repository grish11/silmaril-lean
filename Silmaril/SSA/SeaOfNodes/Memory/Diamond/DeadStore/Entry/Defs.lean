module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs

/-! Delete the first of two Stores in a native diamond entry table. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry

open RVSDG (Tuple)
open Memory.DeadStore.Search.Selection (storeVersions)
open Memory.DeadStore.Search.Selection.Readers renaming discover → discoverReaders

variable {args : List ValueSort} {cells : Nat}

/-- Require the second Store to overwrite the first on its original address
wire. The existing checker validates the intervening Loads at this input. -/
def rewrite (entry : Memory.Graph args) (input : Tuple (Val cells) args) : Option (Memory.Graph args) :=
  if (storeVersions entry).length = 2 then do
    let facts ← discoverReaders entry 1
    Memory.DeadStore.rewrite entry ⟨1, 2⟩ facts input
  else none

/-- Emit both artifacts with the same diamond and checked scalar input. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    Option (Discovery.MemRef.CF.Programs cells args) :=
  (rewrite entry input).map fun edited =>
    ⟨input, Discovery.MemRef.CF.lowerDiamond cells graph (some entry),
      Discovery.MemRef.CF.lowerDiamond cells graph (some edited)⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry

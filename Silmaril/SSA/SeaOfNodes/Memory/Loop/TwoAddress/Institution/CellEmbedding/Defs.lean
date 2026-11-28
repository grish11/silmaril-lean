module

public import Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Defs

/-! Extend the cell count at a typed valuation and encode the full extended result. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open CarriedAddress.Institution.Backend (runtimeResult)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature} {small large : Nat}

def embedModel (model : EntryModel P) (e : CellEmbedding.Embedding model.cells large) : EntryModel P :=
  ⟨large, CellEmbedding.input e model.input⟩

/-- Decode the source result and encode its word and entire framed target heap. -/
def embedOutput (e : CellEmbedding.Embedding small large) (frame : Heap large) :
    Tuple (WireVal small) (Threaded wordPorts) → Tuple (WireVal large) (Threaded wordPorts) :=
  fun out => runtimeResult large (CellEmbedding.result e frame ((runtimeResult small).symm out))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

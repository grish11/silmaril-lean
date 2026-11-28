module

public import Silmaril.SSA.SeaOfNodes.Memory.CellEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Defs

/-! Extend both live address lanes and the initialized heap of a loop header. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress

def Header.embed {small large : Nat} (e : CellEmbedding.Embedding small large)
    (frame : Heap large) (header : Header small) : Header large :=
  ⟨e header.first, e header.second, CellEmbedding.extend e frame header.heap⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress

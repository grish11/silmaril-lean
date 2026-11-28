module

public import Silmaril.SSA.SeaOfNodes.Memory.CellRelabel.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Defs

/-! Relabel both live address lanes and the complete heap in a header. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress

def Header.relabel {cells : Nat} (σ : CellRelabel.Permutation cells) (header : Header cells) : Header cells :=
  ⟨σ header.first, σ header.second, CellRelabel.heap σ header.heap⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress

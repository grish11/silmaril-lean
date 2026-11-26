module

public import Silmaril.Machine.MulticoreVM.Swaps.Thms
public import Silmaril.Machine.MulticoreVM.Toy.Thms
import Silmaril.Proofs.Machine.MulticoreVM.ToySwaps

public section

namespace Silmaril.Machine.MulticoreVM.Toy

/-- Two distinct cores ready to emit satisfy the local diamond at this configuration. -/
theorem emit_localDiamond (cfg : Config) {a b : ThreadId} (distinct : a ≠ b)
    {x y : Nat} {p q : List Instr}
    (atA : cfg a = some ⟨x, .emit :: p⟩) (atB : cfg b = some ⟨y, .emit :: q⟩) :
    LocalDiamond step cfg ⟨a, none⟩ ⟨b, none⟩ :=
  Proofs.Machine.MulticoreVM.emit_localDiamond cfg distinct atA atB

end Silmaril.Machine.MulticoreVM.Toy

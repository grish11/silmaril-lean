module

public import Silmaril.SSA.SeaOfNodes.Memory.CellRelabel.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.Backend.Instances.Defs

/-! Relabel valuations and complete observations at a fixed cell count. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open RVSDG (Tuple)
open RVSDG.OrderedRuntime.Structured (Threaded)
open CarriedAddress.Institution.Backend (runtimeResult)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature} {cells : Nat}

/-- Move address-valued captures within the same typed entry signature. -/
def relabelModel (model : EntryModel P) (σ : CellRelabel.Permutation model.cells) : EntryModel P :=
  ⟨model.cells, CellRelabel.input σ model.input⟩

/-- Transport the whole runtime result via the shared word and heap codec. -/
def relabelOutput (σ : CellRelabel.Permutation cells) :
    Equiv.Perm (Tuple (WireVal cells) (Threaded wordPorts)) :=
  (runtimeResult cells).symm.trans ((CellRelabel.result σ).trans (runtimeResult cells))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

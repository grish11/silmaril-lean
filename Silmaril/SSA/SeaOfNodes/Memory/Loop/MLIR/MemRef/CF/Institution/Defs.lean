module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs

/-! Observe emitted MemRef CFGs over the native memory-loop models. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Loop.Institution (Equation)

variable {P : EntrySignature}

/-- Observe the complete word/heap result whenever the emitted CFG
returns at some budget. The buffer's cell function is the native heap. -/
noncomputable def observe (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    Part (Word × Heap model.cells) where
  Dom := ∃ result : Word × Heap model.cells, ∃ budget,
    CF.run graph model.input budget ⟨initial⟩ = some (result.1, ⟨result.2⟩)
  get found := Classical.choose found

/-- Compare the emitted CFGs on every initial heap at the native typed valuation. -/
def Holds (e : Equation P) (model : EntryModel P) : Prop :=
  ∀ initial, observe e.lhs model initial = observe e.rhs model initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution

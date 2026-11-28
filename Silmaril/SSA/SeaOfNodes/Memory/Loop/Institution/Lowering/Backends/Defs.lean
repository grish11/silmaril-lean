module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs

/-! Completion equations on emitted coloured memory loops. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open RVSDG.NestedTheta.Petri (Finishes)

variable {P : EntrySignature}

/-- At each initial heap, the two emitted θ graphs admit the same finite
coloured completions of the returned word and entire heap. -/
def petriHolds (e : Equation P) (model : EntryModel P) : Prop :=
  ∀ (initial : Heap model.cells) (word : Word) (final : Heap model.cells),
    Finishes (thetaRuntime model.cells) e.lhs.lowerTheta (Memory.encodeInput initial model.input)
        (Memory.encodeResult word final) ↔
      Finishes (thetaRuntime model.cells) e.rhs.lowerTheta (Memory.encodeInput initial model.input)
        (Memory.encodeResult word final)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends

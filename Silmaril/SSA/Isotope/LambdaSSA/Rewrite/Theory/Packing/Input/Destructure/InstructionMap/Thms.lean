module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Input.Destructure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Flat.InstructionMap.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructureInstructionMap

/-! # Primitive relabelling through exact input decoding -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region

universe u v w

theorem packInputsDestructure_mapInstr {τ : Type w} {Φ : Type u} {Ψ : Type v}
    (f : Φ → Ψ) (Γ : VCtx τ) (r : Region Φ) :
    (r.packInputsDestructure Γ).mapInstr f = (r.mapInstr f).packInputsDestructure Γ :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.InputDestructure.packInputsDestructure_map f Γ r

end Silmaril.Isotope.LambdaSSA.Region

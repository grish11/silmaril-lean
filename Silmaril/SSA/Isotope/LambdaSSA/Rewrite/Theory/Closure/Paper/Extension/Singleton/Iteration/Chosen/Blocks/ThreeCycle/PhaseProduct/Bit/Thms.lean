module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.PhaseProduct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductBit

/-! # The native projection on Bit is outside the constructor grammar -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.PhaseProduct

open Semantics.Interaction.Typed (AtomValues)

universe u v
variable {κ : Type u} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)]

/-- No native branch-value return expresses the payload projection at Bit. -/
theorem bit_payload_not_constructor :
    ¬ ConstructorReturn (payload (Φ := Φ) (Ty.coprod (Ty.unit : Ty κ) Ty.unit)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductBit.no_constructor

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.PhaseProduct

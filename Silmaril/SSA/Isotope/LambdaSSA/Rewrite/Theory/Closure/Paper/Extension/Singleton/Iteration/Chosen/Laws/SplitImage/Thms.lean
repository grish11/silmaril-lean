module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SplitImageUniformity

/-! # Uniformity when recurrence stays in a split state's image -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A split state inclusion admits uniformity when the target's recurrent
output is unchanged by retracting and re-including it. Both equations
are in the actual computation quotient. -/
theorem uniformity_of_split_image (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    {A B D : TypeCategory Seed} (h : A ⟶ D) (back : D ⟶ A)
    (section_id : h ≫ back = 𝟙 A) (f : A ⟶ B ⨿ A) (g : D ⟶ B ⨿ D)
    (comm : f ≫ coprod.map (𝟙 B) h = h ≫ g)
    (image : g ≫ coprod.map (𝟙 B) (back ≫ h) = g) :
    iterateChosen Seed f = h ≫ iterateChosen Seed g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SplitImageUniformity.uniformity_of_split_image
    Seed h back section_id f g comm image

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

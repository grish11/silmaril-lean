module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryUniformity

/-! # Pure uniformity modulo abort equivalence -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open Silmaril.Thesis.LambdaIter.Syn (SynCat)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

variable (pe : ε)
local notation "modelSig" => signature (τ := τ) (Φ := Φ) pe

/-- A pure state change whose square commutes after projection also transports
iteration after projection. All operations inside the projection are those of
the exact syntactic category. -/
theorem repairedProjection_pure_uniformity {X D : ValueCat modelSig} {B : SynCat modelSig}
    (f : (values modelSig).obj X ⟶ B ⨿ (values modelSig).obj X)
    (g : (values modelSig).obj D ⟶ B ⨿ (values modelSig).obj D)
    (h : X ⟶ D)
    (comm : (repairedProjection pe).map (f ≫ coprod.map (𝟙 B) ((values modelSig).map h)) =
      (repairedProjection pe).map (((values modelSig).map h) ≫ g)) :
    (repairedProjection pe).map (CategoryTheory.iterate f) =
      (repairedProjection pe).map (((values modelSig).map h) ≫ CategoryTheory.iterate g) :=
  UniformityProofs.repairedProjection_pure_uniformity pe f g h comm

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

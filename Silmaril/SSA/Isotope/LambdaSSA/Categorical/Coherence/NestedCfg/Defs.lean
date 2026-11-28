module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs

/-! # Local functionality of the exact region graph -/

@[expose] public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

/-- The exact graph of a written region is functional at these value and
label contexts. Two witnesses may have different internal typing choices. -/
def RegionDenotes.Functional (Γ : VCtx (Ty κ)) (r : Region Φ) (L : LCtx (Ty κ)) : Prop :=
  ∀ ⦃t t' : r.HasType Γ L⦄ ⦃f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)⦄,
    RegionDenotes J M t f → RegionDenotes J M t' g → f = g

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical

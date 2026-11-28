module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Defs

/-! # Restrict a proof-relevant model to exact typing -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂ u w

variable {V : Type u₁} [Category.{v₁} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type u} [TypeFormers τ] [Subtyping τ]

/-- Use the type former comparisons of the proof-relevant model at the exact tier. -/
@[reducible] def exactTypeModel (M : LetIter.ProofRelevant.Semantics.Categorical.TypeModel τ V) :
    LetIter.Semantics.Categorical.TypeModel τ V where
  obj := M.obj
  productIso := M.productIso
  unitIso := M.unitIso
  coprodIso := M.coprodIso
  emptyIsInitial := M.emptyIsInitial

/-- The same primitive arrows interpret exact typing and proof-relevant typing. -/
@[reducible] def exactInstructionModel {C : Type u₂} [Category.{v₂} C]
    (J : V ⥤ C) (M : LetIter.ProofRelevant.Semantics.Categorical.TypeModel τ V)
    {Φ : Type w} [HasTy Φ τ] [LetIter.ProofRelevant.Semantics.Categorical.InstructionModel J M Φ] :
    LetIter.Semantics.Categorical.InstructionModel J (exactTypeModel M) Φ where
  denote := LetIter.ProofRelevant.Semantics.Categorical.InstructionModel.denote

end Silmaril.Isotope.LetParIter.Categorical

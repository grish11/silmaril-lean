module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Thms

/-! # Tensor data on the LetIter computation quotient -/

@[expose] public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

/-- Tensor objects and structural isomorphisms are projected from the exact category.
For whiskering, choose a representative and project the exact tensor action. -/
@[instance_reducible]
noncomputable def repairedTensorData : MonoidalCategoryStruct Q where
  tensorObj X Y := (P).obj (X.as ⊗ Y.as)
  whiskerLeft X {Y Z} f :=
    (P).map (X.as ◁ (P).preimage (X := Y.as) (Y := Z.as) f)
  whiskerRight {X Y} f Z :=
    (P).map (((P).preimage (X := X.as) (Y := Y.as) f) ▷ Z.as)
  tensorUnit := (P).obj (𝟙_ (SynCat S))
  associator X Y Z := (P).mapIso (α_ X.as Y.as Z.as)
  leftUnitor X := (P).mapIso (λ_ X.as)
  rightUnitor X := (P).mapIso (ρ_ X.as)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

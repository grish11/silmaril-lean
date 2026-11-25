module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Tensor.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryTensor

/-! # The repaired premonoidal computation category and its projection -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open scoped MonoidalCategory
open PremonoidalCategory (IsCentral)
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

/-- The exact syntax tensor laws descend across the repaired computation projection. -/
noncomputable instance repairedPremonoidal : PremonoidalCategory Q where
  toMonoidalCategoryStruct := repairedTensorData pe
  tensorHom_def _ _ := rfl
  whiskerLeft_id := by exact RepairedTensorProofs.repairedWhiskerLeft_id pe
  whiskerLeft_comp := by exact RepairedTensorProofs.repairedWhiskerLeft_comp pe
  id_whiskerRight := by exact RepairedTensorProofs.repairedWhiskerRight_id pe
  comp_whiskerRight := by exact RepairedTensorProofs.repairedWhiskerRight_comp pe
  associator_central := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
    exact RepairedTensorProofs.repairedProjection_central pe (PremonoidalCategory.associator_central X Y Z)
  leftUnitor_central := by
    rintro ⟨X⟩
    exact RepairedTensorProofs.repairedProjection_central pe (PremonoidalCategory.leftUnitor_central X)
  rightUnitor_central := by
    rintro ⟨X⟩
    exact RepairedTensorProofs.repairedProjection_central pe (PremonoidalCategory.rightUnitor_central X)
  associator_naturality_left := by exact RepairedTensorProofs.repairedAssociator_naturality_left pe
  associator_naturality_middle := by exact RepairedTensorProofs.repairedAssociator_naturality_middle pe
  associator_naturality_right := by exact RepairedTensorProofs.repairedAssociator_naturality_right pe
  leftUnitor_naturality := by exact RepairedTensorProofs.repairedLeftUnitor_naturality pe
  rightUnitor_naturality := by exact RepairedTensorProofs.repairedRightUnitor_naturality pe
  pentagon := by exact RepairedTensorProofs.repairedPentagon pe
  triangle := by exact RepairedTensorProofs.repairedTriangle pe

/-- Projection commutes with the fixed-object tensor on the left. -/
theorem repairedWhiskerLeft_map (R : SynCat S) {X Y : SynCat S} (f : X ⟶ Y) :
    (P).obj R ◁ (P).map f = (P).map (R ◁ f) :=
  RepairedTensorProofs.repairedWhiskerLeft_map pe R f

/-- Projection commutes with the fixed-object tensor on the right. -/
theorem repairedWhiskerRight_map (R : SynCat S) {X Y : SynCat S} (f : X ⟶ Y) :
    (P).map f ▷ (P).obj R = (P).map (f ▷ R) :=
  RepairedTensorProofs.repairedWhiskerRight_map pe R f

/-- Projection sends exact central arrows to central arrows of the quotient. -/
theorem repairedProjection_central {X Y : SynCat S} {f : X ⟶ Y}
    (hf : IsCentral f) : IsCentral ((P).map f) :=
  RepairedTensorProofs.repairedProjection_central pe hf

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

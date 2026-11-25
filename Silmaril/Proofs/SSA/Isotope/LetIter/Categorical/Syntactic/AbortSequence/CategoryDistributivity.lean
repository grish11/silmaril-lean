module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Coproducts.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Freyd.Thms

/-! # Projection of the canonical left distributor -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedDistributiveProofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "cmp" => repairedProjectionCoprodIso pe

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem repairedProjection_leftDistributor (X Y Z : SynCat S) :
    (cmp (X ⊗ Y) (X ⊗ Z)).hom ≫ DistributiveTensor.leftHom ((P).obj X) ((P).obj Y) ((P).obj Z) =
      (P).map (DistributiveTensor.leftHom X Y Z) ≫ (P).obj X ◁ (cmp Y Z).hom := by
  apply repairedProjection_coprod_hom_ext pe
  · rw [← Category.assoc, repairedProjection_coprodIso_inl]
    have branch :
        (coprod.inl : (P).obj (X ⊗ Y) ⟶
          (P).obj (X ⊗ Y) ⨿ (P).obj (X ⊗ Z)) ≫
          DistributiveTensor.leftHom ((P).obj X) ((P).obj Y) ((P).obj Z) =
        (P).obj X ◁ (coprod.inl : (P).obj Y ⟶ (P).obj Y ⨿ (P).obj Z) :=
      DistributiveTensor.inl_leftHom ((P).obj X) ((P).obj Y) ((P).obj Z)
    rw [branch, ← repairedProjection_coprodIso_inl pe Y Z, PremonoidalCategory.whiskerLeft_comp,
      repairedWhiskerLeft_map, ← Category.assoc, ← (P).map_comp, DistributiveTensor.inl_leftHom]
  · rw [← Category.assoc, repairedProjection_coprodIso_inr]
    have branch :
        (coprod.inr : (P).obj (X ⊗ Z) ⟶
          (P).obj (X ⊗ Y) ⨿ (P).obj (X ⊗ Z)) ≫
          DistributiveTensor.leftHom ((P).obj X) ((P).obj Y) ((P).obj Z) =
        (P).obj X ◁ (coprod.inr : (P).obj Z ⟶ (P).obj Y ⨿ (P).obj Z) :=
      DistributiveTensor.inr_leftHom ((P).obj X) ((P).obj Y) ((P).obj Z)
    rw [branch, ← repairedProjection_coprodIso_inr pe Y Z, PremonoidalCategory.whiskerLeft_comp,
      repairedWhiskerLeft_map, ← Category.assoc, ← (P).map_comp, DistributiveTensor.inr_leftHom]

theorem repairedLeftDistributor_isIso : ∀ X Y Z : Q,
    IsIso (DistributiveTensor.leftHom X Y Z) := by
  rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  let e := cmp (X ⊗ Y) (X ⊗ Z)
  let d := DistributiveTensor.leftIso X Y Z
  let t := PremonoidalCategory.whiskerLeftIso ((P).obj X) (cmp Y Z)
  let projection := e.symm.trans (((P).mapIso d).trans t)
  change IsIso (DistributiveTensor.leftHom ((P).obj X) ((P).obj Y) ((P).obj Z))
  have hom : projection.hom = DistributiveTensor.leftHom ((P).obj X) ((P).obj Y) ((P).obj Z) := by
    apply (cancel_epi e.hom).mp
    change e.hom ≫ e.inv ≫ (P).map (DistributiveTensor.leftHom X Y Z) ≫ (P).obj X ◁ (cmp Y Z).hom = _
    rw [Iso.hom_inv_id_assoc]
    exact (repairedProjection_leftDistributor pe X Y Z).symm
  rw [← hom]
  infer_instance

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedDistributiveProofs

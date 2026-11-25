module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Freyd.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryFreyd

/-! # The symmetric Freyd structure of the LetIter computation quotient -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "I" => values S
local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe

/-- The premonoidal computation quotient is symmetric. -/
noncomputable instance repairedSymmetric : SymmetricPremonoidalCategory Q where
  braiding := repairedBraiding pe
  naturality_left := by exact RepairedFreydProofs.braiding_naturality_left pe
  naturality_right := by exact RepairedFreydProofs.braiding_naturality_right pe
  hexagon_forward := by exact RepairedFreydProofs.braiding_hexagon_forward pe
  hexagon_reverse := by exact RepairedFreydProofs.braiding_hexagon_reverse pe
  braiding_central := by
    rintro ⟨X⟩ ⟨Y⟩
    exact repairedProjection_central pe (BraidedPremonoidalCategory.braiding_central X Y)
  symmetry := by exact RepairedFreydProofs.braiding_symmetry pe

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The projected Cartesian value functor satisfies Freyd coherence on the quotient. -/
noncomputable instance repairedFreyd : FreydCategory (Jq) where
  unitIso := Iso.refl _
  tensorIso _ _ := Iso.refl _
  obj_bijective := ⟨by
    rintro ⟨X⟩ ⟨Y⟩ eq
    exact congrArg (fun z => (⟨z⟩ : ValueCat S)) (congrArg CategoryTheory.Quotient.as eq),
    by rintro ⟨X⟩; exact ⟨⟨X⟩, rfl⟩⟩
  tensor_naturality_left f Z := by
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      RepairedFreydProofs.values_whiskerRight pe f Z
  tensor_naturality_right X {_ _} f := by
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp] using
      RepairedFreydProofs.values_whiskerLeft pe X f
  associativity X Y Z := by
    change (P).map (α_ X.obj Y.obj Z.obj).hom ≫ (P).obj X.obj ◁ (𝟙 _) ≫ 𝟙 _ =
      (𝟙 _ ▷ (P).obj Z.obj) ≫ 𝟙 _ ≫ (P).map ((I).map (α_ X Y Z).hom)
    simp only [PremonoidalCategory.whiskerLeft_id, PremonoidalCategory.id_whiskerRight,
      Category.comp_id, Category.id_comp]
    exact Category.comp_id _
  left_unitality X := by
    change (𝟙 _ ▷ (P).obj X.obj) ≫ 𝟙 _ ≫ (P).map ((I).map (λ_ X).hom) = (P).map (λ_ X.obj).hom
    simp only [PremonoidalCategory.id_whiskerRight, Category.id_comp]
    rfl
  right_unitality X := by
    change ((P).obj X.obj ◁ 𝟙 _) ≫ 𝟙 _ ≫ (P).map ((I).map (ρ_ X).hom) = (P).map (ρ_ X.obj).hom
    simp only [PremonoidalCategory.whiskerLeft_id, Category.id_comp]
    rfl
  map_central f := repairedProjection_central pe (FreydCategory.image_central (I) f)
  braiding X Y := by
    change 𝟙 _ ≫ (P).map ((I).map (BraidedCategory.braiding X Y).hom) =
      (P).map (BraidedPremonoidalCategory.braiding X.obj Y.obj).hom ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    rfl

instance repairedCentralUnit : FreydCategory.CentralUnit (Jq) :=
  FreydCategory.CentralUnit.of_unitIso_eqToIso _ rfl rfl

/-- The value and computation tensors share their objects with identity comparison. -/
theorem repairedValues_sharedTensor (X Y : ValueCat S) :
    ∃ e : (Jq).obj X ⊗ (Jq).obj Y = (Jq).obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := Jq) X Y = eqToIso e :=
  ⟨rfl, rfl⟩

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

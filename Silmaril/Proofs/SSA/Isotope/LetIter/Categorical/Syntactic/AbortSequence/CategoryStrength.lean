module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Distributivity.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Iteration.Thms

/-! # Projection of inverse distributivity and iteration strength -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedStrengthProofs

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (values)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "cmp" => repairedProjectionCoprodIso pe

local notation "leftInv" => DistributivePremonoidalCategory.leftInv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem repairedProjection_leftInv (X Y Z : SynCat S) :
    (P).obj X ◁ (cmp Y Z).hom ≫ leftInv ((P).obj X) ((P).obj Y) ((P).obj Z) =
      (P).map (leftInv X Y Z) ≫ (cmp (X ⊗ Y) (X ⊗ Z)).hom := by
  let d := DistributiveTensor.leftIso X Y Z
  let e := DistributiveTensor.leftIso ((P).obj X) ((P).obj Y) ((P).obj Z)
  have forward : (cmp (X ⊗ Y) (X ⊗ Z)).hom ≫ e.hom =
      (P).map d.hom ≫ (P).obj X ◁ (cmp Y Z).hom :=
    repairedProjection_leftDistributor pe X Y Z
  apply (cancel_mono e.hom).mp
  change ((P).obj X ◁ (cmp Y Z).hom ≫ e.inv) ≫ e.hom =
    ((P).map d.inv ≫ (cmp (X ⊗ Y) (X ⊗ Z)).hom) ≫ e.hom
  rw [Category.assoc, e.inv_hom_id, Category.comp_id, Category.assoc, forward,
    ← Category.assoc, ← (P).map_comp, d.inv_hom_id]
  rw [(P).map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem repairedIteration_strength {X Y : Q} (Z : Q) (f : X ⟶ Y ⨿ X) :
    CategoryTheory.iterate ((Z ◁ f) ≫ leftInv Z Y X) = Z ◁ CategoryTheory.iterate f := by
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  rcases Z with ⟨Z⟩
  obtain ⟨g, hg⟩ := (P).map_surjective (X := X) (Y := Y ⨿ X) (f ≫ (cmp Y X).inv)
  have body : (P).map g ≫ (cmp Y X).hom = f := by
    rw [hg, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← body]
  change CategoryTheory.iterate
      (((P).obj Z ◁ ((P).map g ≫ (cmp Y X).hom)) ≫ leftInv ((P).obj Z) ((P).obj Y) ((P).obj X)) =
    (P).obj Z ◁ CategoryTheory.iterate ((P).map g ≫ (cmp Y X).hom)
  have transport :
      ((P).obj Z ◁ ((P).map g ≫ (cmp Y X).hom)) ≫ leftInv ((P).obj Z) ((P).obj Y) ((P).obj X) =
      (P).map ((Z ◁ g) ≫ leftInv Z Y X) ≫ (cmp (Z ⊗ Y) (Z ⊗ X)).hom := by
    rw [PremonoidalCategory.whiskerLeft_comp, Category.assoc, repairedProjection_leftInv,
      repairedWhiskerLeft_map, ← Category.assoc, ← (P).map_comp]
  rw [transport, repairedIteration_map, StrongElgotFreydCategory.strength (values S),
    repairedIteration_map, repairedWhiskerLeft_map]

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedStrengthProofs

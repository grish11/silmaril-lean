module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Freyd.Defs

/-! # Braiding and value tensor compatibility in the LetIter quotient -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedFreydProofs

open CategoryTheory
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)
open Silmaril.Thesis.LambdaIter.Syn.SynCat (ValueCat values tensorRight_value tensorLeft_value)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "I" => values S
local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem braiding_naturality_left : ∀ {X Y : Q} (f : X ⟶ Y) (Z : Q),
    f ▷ Z ≫ (repairedBraiding pe Y Z).hom = (repairedBraiding pe X Z).hom ≫ Z ◁ f := by
  rintro ⟨X⟩ ⟨Y⟩ f ⟨Z⟩
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := X) (Y := Y) f
  change (P).map f ▷ (P).obj Z ≫ (P).map (β_ Y Z).hom =
    (P).map (β_ X Z).hom ≫ (P).obj Z ◁ (P).map f
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) (BraidedPremonoidalCategory.naturality_left f Z)

theorem braiding_naturality_right : ∀ (X : Q) {Y Z : Q} (f : Y ⟶ Z),
    X ◁ f ≫ (repairedBraiding pe X Z).hom = (repairedBraiding pe X Y).hom ≫ f ▷ X := by
  rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := Y) (Y := Z) f
  change (P).obj X ◁ (P).map f ≫ (P).map (β_ X Z).hom =
    (P).map (β_ X Y).hom ≫ (P).map f ▷ (P).obj X
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) (BraidedPremonoidalCategory.naturality_right X f)

theorem braiding_hexagon_forward : ∀ X Y Z : Q,
    (α_ X Y Z).hom ≫ (repairedBraiding pe X (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
      (repairedBraiding pe X Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (repairedBraiding pe X Z).hom := by
  rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  change (P).map (α_ X Y Z).hom ≫ (P).map (β_ X (Y ⊗ Z)).hom ≫ (P).map (α_ Y Z X).hom =
    (P).map (β_ X Y).hom ▷ (P).obj Z ≫ (P).map (α_ Y X Z).hom ≫ (P).obj Y ◁ (P).map (β_ X Z).hom
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) (BraidedPremonoidalCategory.hexagon_forward X Y Z)

theorem braiding_hexagon_reverse : ∀ X Y Z : Q,
    (α_ X Y Z).inv ≫ (repairedBraiding pe (X ⊗ Y) Z).hom ≫ (α_ Z X Y).inv =
      X ◁ (repairedBraiding pe Y Z).hom ≫ (α_ X Z Y).inv ≫ (repairedBraiding pe X Z).hom ▷ Y := by
  rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  change (P).map (α_ X Y Z).inv ≫ (P).map (β_ (X ⊗ Y) Z).hom ≫ (P).map (α_ Z X Y).inv =
    (P).obj X ◁ (P).map (β_ Y Z).hom ≫ (P).map (α_ X Z Y).inv ≫ (P).map (β_ X Z).hom ▷ (P).obj Y
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) (BraidedPremonoidalCategory.hexagon_reverse X Y Z)

theorem braiding_symmetry : ∀ X Y : Q,
    (repairedBraiding pe X Y).hom ≫ (repairedBraiding pe Y X).hom = 𝟙 (X ⊗ Y) := by
  rintro ⟨X⟩ ⟨Y⟩
  change (P).map (β_ X Y).hom ≫ (P).map (β_ Y X).hom = 𝟙 ((P).obj (X ⊗ Y))
  rw [← (P).map_comp, SymmetricPremonoidalCategory.symmetry]
  exact (P).map_id (X ⊗ Y)

theorem values_whiskerRight {X Y : ValueCat S} (f : X ⟶ Y) (Z : ValueCat S) :
    (Jq).map f ▷ (Jq).obj Z = (Jq).map (f ▷ Z) := by
  change (P).map ((I).map f) ▷ (P).obj Z.obj = (P).map ((I).map (f ▷ Z))
  rw [repairedWhiskerRight_map]
  exact congrArg (fun a => (P).map a) (tensorRight_value (R := Z) f)

theorem values_whiskerLeft (X : ValueCat S) {Y Z : ValueCat S} (f : Y ⟶ Z) :
    (Jq).obj X ◁ (Jq).map f = (Jq).map (X ◁ f) := by
  change (P).obj X.obj ◁ (P).map ((I).map f) = (P).map ((I).map (X ◁ f))
  rw [repairedWhiskerLeft_map]
  exact congrArg (fun a => (P).map a) (tensorLeft_value (R := X) f)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedFreydProofs

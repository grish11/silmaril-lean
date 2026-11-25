module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Tensor.Defs

/-! # Premonoidal laws of the LetIter computation quotient -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedTensorProofs

open CategoryTheory
open scoped MonoidalCategory
open PremonoidalCategory (IsCentral leftTensor rightTensor)
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe

attribute [local instance] repairedTensorData

theorem repairedWhiskerLeft_map (R : SynCat S) {X Y : SynCat S} (f : X ⟶ Y) :
    (P).obj R ◁ ((P).map f) = (P).map (R ◁ f) := by
  apply (repairedProjection_map_eq_iff pe _ _).mpr
  exact repairedHomClass_tensorLeft_congr pe R
    ((repairedProjection_map_eq_iff pe _ _).mp ((P).map_preimage ((P).map f)))

theorem repairedWhiskerRight_map (R : SynCat S) {X Y : SynCat S} (f : X ⟶ Y) :
    (P).map f ▷ (P).obj R = (P).map (f ▷ R) := by
  apply (repairedProjection_map_eq_iff pe _ _).mpr
  exact repairedHomClass_tensorRight_congr pe R
    ((repairedProjection_map_eq_iff pe _ _).mp ((P).map_preimage ((P).map f)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem repairedProjection_central {X Y : SynCat S} {f : X ⟶ Y}
    (hf : IsCentral f) : IsCentral ((P).map f) := by
  constructor
  · rintro ⟨A⟩ ⟨B⟩ g
    obtain ⟨g, rfl⟩ := (P).map_surjective (X := A) (Y := B) g
    change leftTensor ((P).map f) ((P).map g) = rightTensor ((P).map f) ((P).map g)
    simpa only [leftTensor, rightTensor, Functor.map_comp, ← repairedWhiskerLeft_map,
      ← repairedWhiskerRight_map] using congrArg (fun h => (P).map h) (hf.1 g)
  · rintro ⟨A⟩ ⟨B⟩ g
    obtain ⟨g, rfl⟩ := (P).map_surjective (X := A) (Y := B) g
    change leftTensor ((P).map g) ((P).map f) = rightTensor ((P).map g) ((P).map f)
    simpa only [leftTensor, rightTensor, Functor.map_comp, ← repairedWhiskerLeft_map,
      ← repairedWhiskerRight_map] using congrArg (fun h => (P).map h) (hf.2 g)

theorem repairedWhiskerLeft_comp (R : Q) {X Y Z : Q} (f : X ⟶ Y) (g : Y ⟶ Z) :
    R ◁ (f ≫ g) = R ◁ f ≫ R ◁ g := by
  rcases R with ⟨R⟩
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  rcases Z with ⟨Z⟩
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := X) (Y := Y) f
  obtain ⟨g, rfl⟩ := (P).map_surjective (X := Y) (Y := Z) g
  change (P).obj R ◁ ((P).map f ≫ (P).map g) =
    (P).obj R ◁ (P).map f ≫ (P).obj R ◁ (P).map g
  rw [← (P).map_comp, repairedWhiskerLeft_map, repairedWhiskerLeft_map,
    repairedWhiskerLeft_map, ← (P).map_comp, PremonoidalCategory.whiskerLeft_comp]

theorem repairedWhiskerRight_comp {X Y Z : Q} (f : X ⟶ Y) (g : Y ⟶ Z) (R : Q) :
    (f ≫ g) ▷ R = f ▷ R ≫ g ▷ R := by
  rcases R with ⟨R⟩
  rcases X with ⟨X⟩
  rcases Y with ⟨Y⟩
  rcases Z with ⟨Z⟩
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := X) (Y := Y) f
  obtain ⟨g, rfl⟩ := (P).map_surjective (X := Y) (Y := Z) g
  change ((P).map f ≫ (P).map g) ▷ (P).obj R =
    (P).map f ▷ (P).obj R ≫ (P).map g ▷ (P).obj R
  rw [← (P).map_comp, repairedWhiskerRight_map, repairedWhiskerRight_map,
    repairedWhiskerRight_map, ← (P).map_comp, PremonoidalCategory.comp_whiskerRight]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem repairedWhiskerLeft_id : ∀ X Y : Q, X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  rintro ⟨X⟩ ⟨Y⟩
  change (P).obj X ◁ 𝟙 ((P).obj Y) = 𝟙 ((P).obj (X ⊗ Y))
  rw [← (P).map_id Y, repairedWhiskerLeft_map, PremonoidalCategory.whiskerLeft_id]
  exact (P).map_id (X ⊗ Y)

theorem repairedWhiskerRight_id : ∀ X Y : Q, 𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
  rintro ⟨X⟩ ⟨Y⟩
  change 𝟙 ((P).obj X) ▷ (P).obj Y = 𝟙 ((P).obj (X ⊗ Y))
  rw [← (P).map_id X, repairedWhiskerRight_map, PremonoidalCategory.id_whiskerRight]
  exact (P).map_id (X ⊗ Y)

theorem repairedAssociator_naturality_left : ∀ {X Y : Q} (f : X ⟶ Y) (Z W : Q),
    ((f ▷ Z) ▷ W) ≫ (α_ Y Z W).hom = (α_ X Z W).hom ≫ f ▷ (Z ⊗ W) := by
  rintro ⟨X⟩ ⟨Y⟩ f ⟨Z⟩ ⟨W⟩
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := X) (Y := Y) f
  change (((P).map f ▷ (P).obj Z) ▷ (P).obj W) ≫ (P).map (α_ Y Z W).hom =
    (P).map (α_ X Z W).hom ≫ (P).map f ▷ (P).obj (Z ⊗ W)
  simpa only [Functor.map_comp, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) (PremonoidalCategory.associator_naturality_left f Z W)

theorem repairedAssociator_naturality_middle : ∀ (X : Q) {Y Z : Q} (f : Y ⟶ Z) (W : Q),
    ((X ◁ f) ▷ W) ≫ (α_ X Z W).hom = (α_ X Y W).hom ≫ X ◁ (f ▷ W) := by
  rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f ⟨W⟩
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := Y) (Y := Z) f
  change (((P).obj X ◁ (P).map f) ▷ (P).obj W) ≫ (P).map (α_ X Z W).hom =
    (P).map (α_ X Y W).hom ≫ (P).obj X ◁ ((P).map f ▷ (P).obj W)
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) (PremonoidalCategory.associator_naturality_middle X f W)

theorem repairedAssociator_naturality_right : ∀ (X Y : Q) {Z W : Q} (f : Z ⟶ W),
    ((X ⊗ Y) ◁ f) ≫ (α_ X Y W).hom = (α_ X Y Z).hom ≫ X ◁ (Y ◁ f) := by
  rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨W⟩ f
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := Z) (Y := W) f
  change ((P).obj (X ⊗ Y) ◁ (P).map f) ≫ (P).map (α_ X Y W).hom =
    (P).map (α_ X Y Z).hom ≫ (P).obj X ◁ ((P).obj Y ◁ (P).map f)
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map] using
    congrArg (fun a => (P).map a) (PremonoidalCategory.associator_naturality_right X Y f)

theorem repairedLeftUnitor_naturality : ∀ {X Y : Q} (f : X ⟶ Y),
    𝟙_ Q ◁ f ≫ (λ_ Y).hom = (λ_ X).hom ≫ f := by
  rintro ⟨X⟩ ⟨Y⟩ f
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := X) (Y := Y) f
  change ((P).obj (𝟙_ (SynCat S)) ◁ (P).map f) ≫ (P).map (λ_ Y).hom =
    (P).map (λ_ X).hom ≫ (P).map f
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map] using
    congrArg (fun a => (P).map a) (PremonoidalCategory.leftUnitor_naturality f)

theorem repairedRightUnitor_naturality : ∀ {X Y : Q} (f : X ⟶ Y),
    f ▷ 𝟙_ Q ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f := by
  rintro ⟨X⟩ ⟨Y⟩ f
  obtain ⟨f, rfl⟩ := (P).map_surjective (X := X) (Y := Y) f
  change ((P).map f ▷ (P).obj (𝟙_ (SynCat S))) ≫ (P).map (ρ_ Y).hom =
    (P).map (ρ_ X).hom ≫ (P).map f
  simpa only [Functor.map_comp, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) (PremonoidalCategory.rightUnitor_naturality f)

theorem repairedPentagon : ∀ W X Y Z : Q, MonoidalCategory.Pentagon W X Y Z := by
  rintro ⟨W⟩ ⟨X⟩ ⟨Y⟩ ⟨Z⟩
  change ((P).map (α_ W X Y).hom ▷ (P).obj Z) ≫ (P).map (α_ W (X ⊗ Y) Z).hom ≫
      (P).obj W ◁ (P).map (α_ X Y Z).hom =
    (P).map (α_ (W ⊗ X) Y Z).hom ≫ (P).map (α_ W X (Y ⊗ Z)).hom
  have law := PremonoidalCategory.pentagon W X Y Z
  unfold MonoidalCategory.Pentagon at law
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) law

theorem repairedTriangle : ∀ X Y : Q, (α_ X (𝟙_ Q) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y := by
  rintro ⟨X⟩ ⟨Y⟩
  change (P).map (α_ X (𝟙_ (SynCat S)) Y).hom ≫ (P).obj X ◁ (P).map (λ_ Y).hom =
    (P).map (ρ_ X).hom ▷ (P).obj Y
  simpa only [Functor.map_comp, ← repairedWhiskerLeft_map, ← repairedWhiskerRight_map] using
    congrArg (fun a => (P).map a) (PremonoidalCategory.triangle X Y)

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.RepairedTensorProofs

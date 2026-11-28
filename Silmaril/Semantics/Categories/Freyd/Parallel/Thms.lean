module

public import Silmaril.Semantics.Categories.Freyd.Parallel.Defs
import Silmaril.Proofs.Semantics.Categories.Freyd.Parallel.Coherence

/-! # Shared-context laws for ordered Freyd parallel -/

public section

namespace CategoryTheory.FreydCategory.OrderedParallel

open CartesianMonoidalCategory
open scoped MonoidalCategory

universe u v u' v'

variable {V : Type u} {C : Type v} [Category.{u'} V] [Category.{v'} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [∀ X Y : C, Preorder (X ⟶ Y)]
  {J : V ⥤ C} [FreydCategory J] (P : OrderedParallel J)

/-- Whisker agreement supplies the normal identity comparison. -/
theorem tensor_id (X A : V) :
    P.tensor (𝟙 (J.obj X)) (𝟙 (J.obj A)) = 𝟙 (J.obj (X ⊗ A)) := by
  simp only [P.whiskerLeft, PremonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

/-- Two pure arrows use the existing value product. -/
theorem tensor_maps {X Y A B : V} (f : X ⟶ Y) (g : A ⟶ B) :
    P.tensor (J.map f) (J.map g) = J.map (f ⊗ₘ g) :=
  tensor_maps_proof P f g

/-- Shared-context parallel is monotone when precomposition by the pure diagonal is monotone. -/
theorem par_mono {R A B : V}
    (pre_mono : Monotone (fun k : J.obj (R ⊗ R) ⟶ J.obj (A ⊗ B) =>
      J.map (lift (𝟙 R) (𝟙 R)) ≫ k))
    {f f' : J.obj R ⟶ J.obj A} {g g' : J.obj R ⟶ J.obj B} (hf : f ≤ f') (hg : g ≤ g') :
    P.par f g ≤ P.par f' g' :=
  pre_mono (P.tensor_mono hf hg)

/-- A pure input map reindexes both branches. -/
theorem par_reindex {R S A B : V} (k : S ⟶ R) (f : J.obj R ⟶ J.obj A)
    (g : J.obj R ⟶ J.obj B) :
    J.map k ≫ P.par f g = P.par (J.map k ≫ f) (J.map k ≫ g) :=
  par_reindex_proof P k f g

/-- A pure product map acts separately on the two results. -/
theorem par_postmap {R A B X Y : V} (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B)
    (k : A ⟶ X) (l : B ⟶ Y) :
    P.par f g ≫ J.map (k ⊗ₘ l) = P.par (f ≫ J.map k) (g ≫ J.map l) :=
  par_postmap_proof P f g k l

/-- Shared-context parallel of pure branches is their Cartesian pairing. -/
theorem par_maps {R A B : V} (f : R ⟶ A) (g : R ⟶ B) :
    P.par (J.map f) (J.map g) = J.map (lift f g) :=
  par_maps_proof P f g

/-- Swapping the value tuple exchanges the branches. -/
theorem par_swap {R A B : V} (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B) :
    P.par f g ≫ J.map (BraidedCategory.braiding A B).hom = P.par g f :=
  par_swap_proof P f g

/-- Three branches with the same input share it independently of result bracketing. -/
theorem par_assoc {R A B D : V} (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B)
    (h : J.obj R ⟶ J.obj D) :
    P.par (P.par f g) h ≫ J.map (α_ A B D).hom = P.par f (P.par g h) :=
  par_assoc_proof P f g h

/-- A pure unit on the left can be projected away. -/
theorem par_unit_left {R A : V} (f : J.obj R ⟶ J.obj A) :
    P.par (J.map (toUnit R)) f ≫ J.map (λ_ A).hom = f :=
  par_unit_left_proof P f

/-- A pure unit on the right can be projected away. -/
theorem par_unit_right {R A : V} (f : J.obj R ⟶ J.obj A) :
    P.par f (J.map (toUnit R)) ≫ J.map (ρ_ A).hom = f :=
  par_unit_right_proof P f

end CategoryTheory.FreydCategory.OrderedParallel

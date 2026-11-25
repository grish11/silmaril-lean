module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Defs
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Laws

/-! # Tensoring exact λiter computations in either fixed argument -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory

variable {S : Sig.{u}}

/-- Tensoring on the left preserves the computation identity. -/
@[simp] theorem tensorLeft_id (R A : SynCat S) :
    tensorLeft R (𝟙 A) = 𝟙 (productObj R A) :=
  tensorLeft_id_proof R A

/-- Tensoring on the left preserves sequential composition of computations. -/
theorem tensorLeft_comp (R : SynCat S) {A B C : SynCat S} (f : A ⟶ B) (g : B ⟶ C) :
    tensorLeft R (f ≫ g) = tensorLeft R f ≫ tensorLeft R g :=
  tensorLeft_comp_proof R f g

/-- A computation tensored on the left retains its pure representative property. -/
theorem tensorLeft_isPureMor (R : SynCat S) {A B : SynCat S} {f : A ⟶ B}
    (hf : IsPureMor f) : IsPureMor (tensorLeft R f) :=
  tensorLeft_isPureMor_proof R hf

/-- On a pure pair, the computation acts on its second component. -/
theorem tensorLeft_pair {X R A B : SynCat S} {a : X ⟶ R} {b : X ⟶ A}
    (ha : IsPureMor a) (hb : IsPureMor b) (f : A ⟶ B) :
    pairArrows a b ≫ tensorLeft R f = pairArrows a (b ≫ f) :=
  tensorLeft_pair_proof ha hb f

/-- Tensoring on the right preserves the computation identity. -/
@[simp] theorem tensorRight_id (R A : SynCat S) :
    tensorRight R (𝟙 A) = 𝟙 (productObj A R) := by
  simp [tensorRight]

/-- Tensoring on the right preserves sequential composition of computations. -/
theorem tensorRight_comp (R : SynCat S) {A B C : SynCat S} (f : A ⟶ B) (g : B ⟶ C) :
    tensorRight R (f ≫ g) = tensorRight R f ≫ tensorRight R g := by
  simp [tensorRight, tensorLeft_comp, Category.assoc]

/-- Tensoring on the right preserves the pure representative property. -/
theorem tensorRight_isPureMor (R : SynCat S) {A B : SynCat S} {f : A ⟶ B}
    (hf : IsPureMor f) : IsPureMor (tensorRight R f) :=
  IsPureMor.comp (valueSwap A R).hom.property
    (IsPureMor.comp (tensorLeft_isPureMor R hf) (valueSwap B R).inv.property)

/-- Swapping a product in the opposite direction gives the inverse. -/
theorem tensorSwap_inv (A R : SynCat S) : (tensorSwap A R).inv = (tensorSwap R A).hom :=
  by rfl

/-- Swap is natural in an arbitrary computation on the first component. -/
theorem tensorSwap_naturality_left {A B : SynCat S} (f : A ⟶ B) (R : SynCat S) :
    tensorRight R f ≫ (tensorSwap B R).hom = (tensorSwap A R).hom ≫ tensorLeft R f := by
  simp [tensorRight, Category.assoc]

/-- Swap is natural in an arbitrary computation on the second component. -/
theorem tensorSwap_naturality_right (R : SynCat S) {A B : SynCat S} (f : A ⟶ B) :
    tensorLeft R f ≫ (tensorSwap R B).hom = (tensorSwap R A).hom ≫ tensorRight R f := by
  rw [tensorRight, ← tensorSwap_inv A R, ← tensorSwap_inv B R]
  simp

/-- Left tensoring commutes with the inclusion of the Cartesian value category. -/
theorem tensorLeft_value {R A B : ValueCat S} (f : A ⟶ B) :
    tensorLeft R.obj f.hom = (MonoidalCategoryStruct.whiskerLeft R f).hom :=
  tensorLeft_value_proof f

/-- Right tensoring commutes with the inclusion of the Cartesian value category. -/
theorem tensorRight_value {R A B : ValueCat S} (f : A ⟶ B) :
    tensorRight R.obj f.hom = (MonoidalCategoryStruct.whiskerRight f R).hom :=
  tensorRight_value_proof f

/-- The endofunctor of the syntactic computation category given by tensoring on the left. -/
@[expose] def tensorLeftFunctor (R : SynCat S) : SynCat S ⥤ SynCat S where
  obj := productObj R
  map := tensorLeft R
  map_id := tensorLeft_id R
  map_comp := tensorLeft_comp R

/-- The endofunctor of the syntactic computation category given by tensoring on the right. -/
def tensorRightFunctor (R : SynCat S) : SynCat S ⥤ SynCat S where
  obj A := productObj A R
  map := tensorRight R
  map_id := tensorRight_id R
  map_comp := tensorRight_comp R

/-- Dropping the retained first slot commutes with any computation on the second. -/
theorem tensorLeft_second (R : SynCat S) {A B : SynCat S} (f : A ⟶ B) :
    tensorLeft R f ≫ second R B = second R A ≫ f :=
  tensorLeft_second_proof R f

/-- Dropping the retained second slot commutes with any computation on the first. -/
theorem tensorRight_first (R : SynCat S) {A B : SynCat S} (f : A ⟶ B) :
    tensorRight R f ≫ first B R = first A R ≫ f :=
  tensorRight_first_proof R f

/-- The left unitor is the projection to the non-unit component. -/
theorem tensorLeftUnitor_hom (A : SynCat S) :
    (tensorLeftUnitor A).hom = second (tensorUnit S) A :=
  congrArg (fun g => g.hom) (CartesianMonoidalCategory.leftUnitor_hom (⟨A⟩ : ValueCat S))

/-- The right unitor is the projection to the non-unit component. -/
theorem tensorRightUnitor_hom (A : SynCat S) :
    (tensorRightUnitor A).hom = first A (tensorUnit S) :=
  congrArg (fun g => g.hom) (CartesianMonoidalCategory.rightUnitor_hom (⟨A⟩ : ValueCat S))

/-- The left unitor is natural for every computation arrow. -/
theorem tensorLeftUnitor_naturality {A B : SynCat S} (f : A ⟶ B) :
    tensorLeft (tensorUnit S) f ≫ (tensorLeftUnitor B).hom = (tensorLeftUnitor A).hom ≫ f := by
  rw [tensorLeftUnitor_hom, tensorLeftUnitor_hom, tensorLeft_second]

/-- The right unitor is natural for every computation arrow. -/
theorem tensorRightUnitor_naturality {A B : SynCat S} (f : A ⟶ B) :
    tensorRight (tensorUnit S) f ≫ (tensorRightUnitor B).hom = (tensorRightUnitor A).hom ≫ f := by
  rw [tensorRightUnitor_hom, tensorRightUnitor_hom, tensorRight_first]

end Silmaril.Thesis.LambdaIter.Syn.SynCat

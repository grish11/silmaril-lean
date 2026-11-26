module

public import Silmaril.SSA.MLIR.Signature.FixedSorts.ChosenGenerators.Defs
import Silmaril.Proofs.SSA.MLIR.Signature.FixedSorts.ChosenGenerators.Laws

public section

namespace Silmaril.MLIR.Institution.Signature.FixedSorts

open CategoryTheory CategoryTheory.Limits

variable {withRegions : Bool} {Ty : Type} (C S : FixedSorts withRegions Ty)

/-- A renaming is extended by identity on the generators. -/
theorem chosenGeneratorsMonad_map {A B : FixedSorts withRegions Ty} (f : A ⟶ B) :
    (chosenGeneratorsMonad C).map f = coprod.map (𝟙 C) f :=
  rfl

/-- The unit inserts the original signature into the right summand. -/
theorem chosenGeneratorsMonad_unit : (chosenGeneratorsMonad C).η.app S = coprod.inr :=
  Proofs.MLIR.Signature.ChosenGenerators.unit_app C S

/-- The natural hom equivalence restricts a chosen-map-preserving renaming to the
original signature. -/
theorem chosenGenerators_homEquiv_apply (X : Under C)
    (f : (Under.costar C).obj S ⟶ X) :
    (chosenGeneratorsAdjunction C).homEquiv S X f = coprod.inr ≫ f.right :=
  Proofs.MLIR.Signature.ChosenGenerators.homEquiv_apply C S X f

/-- The inverse of the hom equivalence combines the chosen map and the given renaming. -/
theorem chosenGenerators_homEquiv_symm_right (X : Under C) (f : S ⟶ X.right) :
    (((chosenGeneratorsAdjunction C).homEquiv S X).symm f).right = coprod.desc X.hom f :=
  Proofs.MLIR.Signature.ChosenGenerators.homEquiv_symm_right C S X f

/-- Multiplication identifies the two generator copies and retains original labels. -/
theorem chosenGeneratorsMonad_mul :
    (chosenGeneratorsMonad C).μ.app S = coprod.desc coprod.inl (𝟙 (C ⨿ S)) :=
  Proofs.MLIR.Signature.ChosenGenerators.mul_app C S

end Silmaril.MLIR.Institution.Signature.FixedSorts

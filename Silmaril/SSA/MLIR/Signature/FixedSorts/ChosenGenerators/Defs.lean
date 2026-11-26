module

public import Silmaril.SSA.MLIR.Signature.FixedSorts.Thms
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Monad.Adjunction

/-! The free chosen-generator map on fixed-sort signatures. -/

@[expose] public noncomputable section

namespace Silmaril.MLIR.Institution.Signature.FixedSorts

open CategoryTheory

variable {withRegions : Bool} {Ty : Type}

/-- Freely adjoin a chosen map from the fixed generator signature `C` by forming
the coproduct with `C`. An object under `C` is a signature equipped with a
profile-preserving renaming from `C`. -/
def chosenGeneratorsAdjunction (C : FixedSorts withRegions Ty) :
    Under.costar C ⊣ Under.forget C :=
  Under.costarAdjForget C

/-- The induced monad on signatures and identity-sort renamings, with the
sort type and region flag both fixed. -/
def chosenGeneratorsMonad (C : FixedSorts withRegions Ty) :
    Monad (FixedSorts withRegions Ty) :=
  (chosenGeneratorsAdjunction C).toMonad

end Silmaril.MLIR.Institution.Signature.FixedSorts

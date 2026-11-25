module

public import Silmaril.Semantics.Calco2019.ExceptionGuardThms
public import Silmaril.Semantics.Calco2019.ResumptionGuardThms

/-! # Suspension in coinductive resumptions over a guarded monad -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

/-- The parameter monads `T(- + H W)` inherit guards and preserve them under parameter maps. -/
def parametrizedGuards {T : CategoryTheory.Monad C} (G : MonadGuardedness P T)
    (H : C ⥤ C) : (parametrized P T H).Guards P where
  guard W := guardednessOf G (H.obj W)
  preserves k := change_preservesOf G (H.map k)

variable (P) (T : CategoryTheory.Monad C) (H : C ⥤ C)
  (R : FinalResumptions (parametrized P T H))

/-- Suspend once, then return the value supplied by the operation. -/
noncomputable def liftStepFor (X : C) : H.obj X ⟶ R.obj X :=
  H.map (R.unit X) ≫ raise P T (H.obj (R.obj X)) X ≫ R.roll X

end Silmaril.Calco2019.Exception

module

public import Silmaril.Semantics.Calco2019.ExceptionGuardThms
import Silmaril.Proofs.Semantics.Calco2019.ExceptionUniformity

/-! # Uniformity for the exception monad of Example 22 -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

/-- A pure state change commutes with the chosen iteration at a fixed exception parameter. -/
theorem uniformity (T : GuardedElgotMonad P) (E : C) :
    (fixpoints T E).Uniform (Kleisli.Adjunction.toKleisli ((family P T.monad).obj E)) :=
  Proofs.exception_uniformity T E

end Silmaril.Calco2019.Exception

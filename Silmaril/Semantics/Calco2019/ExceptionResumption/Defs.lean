module

public import Silmaril.Semantics.Calco2019.ExceptionElgot
public import Silmaril.Semantics.Calco2019.ResumptionConway
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Suspension.Defs

/-! # Canonical embeddings into exception resumptions, CALCO 2019 Lemma 27 -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P) (H : C ⥤ C)
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

/-- Regard a base computation as a resumption with no suspensions. -/
noncomputable def liftBase (X : C) : T.monad.obj X ⟶ R.obj X :=
  T.monad.map (P.inl (Y := H.obj (R.obj X))) ≫ R.roll X

/-- Suspend once, then return the value supplied by the operation. -/
noncomputable def liftStep (X : C) : H.obj X ⟶ R.obj X :=
  liftStepFor P T.monad H R X

end Silmaril.Calco2019.Exception

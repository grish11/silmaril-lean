module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Suspension.Defs
import Silmaril.Proofs.Semantics.Calco2019.ExceptionSuspension

/-! # CALCO 2019 Lemma 27(1), without a chosen base iteration -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (P : Coproducts C)
  (T : CategoryTheory.Monad C) (H : C ⥤ C)
  (R : FinalResumptions (parametrized P T H))

@[reassoc, simp]
theorem liftStepFor_out (X : C) :
    liftStepFor P T H R X ≫ R.out X = H.map (R.unit X) ≫ raise P T (H.obj (R.obj X)) X :=
  Proofs.step_outFor P T H R X

/-- The canonical suspension transformation requires no guard or iteration to construct. -/
@[expose]
noncomputable def suspensionFor : H ⟶ (R.monad P).toFunctor where
  app := liftStepFor P T H R
  naturality _ _ f := by exact Proofs.step_natFor P T H R f

@[simp]
theorem suspensionFor_app (X : C) : (suspensionFor P T H R).app X = liftStepFor P T H R X :=
  rfl

/-- A suspension is guarded in its entire output as soon as the base monad is guarded. -/
theorem suspensionFor_guarded [HasInitial C] (G : MonadGuardedness P T) :
    MonadGuardedness.GuardedNatTrans P ((parametrizedGuards G H).resumptionGuardedness R)
      (suspensionFor P T H R) :=
  Proofs.suspension_guardFor P T H R G

end Silmaril.Calco2019.Exception

module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Suspension.Thms

/-! # CALCO 2019, Lemma 27(1) for a guarded base monad -/

public section

universe u v

namespace Silmaril.Papers.Calco2019

open CategoryTheory CategoryTheory.Limits Silmaril.Calco2019

/-- The suspension generator into the coinductive resumption monad is id-guarded. -/
theorem lemma27_suspension_guarded {C : Type u} [Category.{v} C] [HasInitial C]
    (P : Coproducts C) (T : CategoryTheory.Monad C) (G : MonadGuardedness P T) (H : C ⥤ C)
    (R : FinalResumptions (Exception.parametrized P T H)) :
    MonadGuardedness.GuardedNatTrans P ((Exception.parametrizedGuards G H).resumptionGuardedness R)
      (Exception.suspensionFor P T H R) :=
  Exception.suspensionFor_guarded P T H R G

end Silmaril.Papers.Calco2019

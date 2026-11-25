module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Thms
public import Silmaril.Semantics.Calco2019.GuardedTransformations

/-! # The interpretation body of CALCO 2019 Theorem 28 -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T S : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)
  (ξ : GuardedElgotMonadHom P T S) (σ : GuardedTransformation H S)

local notation "Q" => S.monad
local notation "K" => P.kleisli Q

/-- After observing a resumption, interpret base effects with `ξ`, operations with
`σ`, and put the operation's continuation in the recursive summand. -/
noncomputable def mediatorBody (X : C) :
    Kleisli.mk Q (R.obj X) ⟶ (K).sum (Kleisli.mk Q X) (Kleisli.mk Q (R.obj X)) :=
  kleisliArrow (R.out X ≫ ξ.hom.app (P.sum X (H.obj (R.obj X)))) ≫
    (K).desc (K).inl (kleisliArrow (σ.val.app (R.obj X)) ≫ (K).inr)

end Silmaril.Calco2019.Exception

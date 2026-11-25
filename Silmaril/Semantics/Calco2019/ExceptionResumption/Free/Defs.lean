module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Thms
public import Silmaril.Semantics.Calco2019.GuardedTransformations

/-! # Generators of the exception resumption free extension -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasInitial C] {P : Coproducts C}
  {T : GuardedElgotMonad P} {H : C ⥤ C}
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

/-- The guarded suspension transformation in the bimodule of Definition 2. -/
noncomputable def resumptionGenerator :
    (guardedBimodule P).Hom H ((parametrizedElgot T H).resumptionElgotMonad R) :=
  ⟨suspension T H R, suspension_guarded T H R⟩

end Silmaril.Calco2019.Exception

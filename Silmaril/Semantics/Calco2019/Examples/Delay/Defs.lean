module

public import Mathlib.Data.Seq.Computation
public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Specializations

/-! # The identity resumption instance in CALCO 2019, §1.3 -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Delay

open CategoryTheory CategoryTheory.Endofunctor

/-- With both the base monad and the operation functor identity, the layer is `X ⊕ W`. -/
noncomputable abbrev family : ParametrizedGuardedElgotMonad typeCoproducts.{u} :=
  Exception.parametrizedElgot (guardedIdentity typeCoproducts) (𝟭 (Type u))

/-- Observing a Capretta computation either returns a result or exposes one delay. -/
def coalgebra (X : Type u) : Coalgebra (family.toParametrizedMonad.parameter X) :=
  ⟨Computation X, TypeCat.ofHom Computation.destruct⟩

end Silmaril.Calco2019.Examples.Delay

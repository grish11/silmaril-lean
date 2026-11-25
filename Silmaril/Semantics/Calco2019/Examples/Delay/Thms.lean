module

public import Silmaril.Semantics.Calco2019.Examples.Delay.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.Delay

/-! # Capretta delay as the identity-based coinductive resumption -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Delay

open CategoryTheory CategoryTheory.Limits

/-- `Computation X` is final for the functor `X ⊕ -`. -/
noncomputable def terminal (X : Type u) : IsTerminal (coalgebra X) :=
  Proofs.terminal X

/-- The concrete witnesses used by the CALCO resumption construction. -/
@[expose] noncomputable def resumptions : FinalResumptions family.{u}.toParametrizedMonad where
  coalgebra := coalgebra
  final := terminal

/-- The chosen resumption carrier is the existing raw delay type. -/
theorem obj_eq (X : Type u) : resumptions.obj X = Computation X := rfl

/-- Each observation of the resumption preserves one explicit delay. -/
theorem out_eq (X : Type u) : resumptions.out X = TypeCat.ofHom Computation.destruct := rfl

theorem unit_eq (X : Type u) (x : X) : resumptions.unit X x = Computation.pure x :=
  Proofs.unit_eq X x

theorem extend_eq {X Y : Type u} (f : X → Computation Y) (c : Computation X) :
    resumptions.extend typeCoproducts (TypeCat.ofHom f) c = Computation.bind c f :=
  Proofs.extend_eq f c

/-- The delay resumption is free on the identity operation in guarded Elgot monads. -/
theorem free :
    (guardedBimodule typeCoproducts.{u}).IsFreeObject
      (Exception.resumptionGenerator (H := 𝟭 (Type u)) resumptions.{u}) :=
  Exception.resumption_freeObject (𝟭 (Type u)) resumptions.{u}

end Silmaril.Calco2019.Examples.Delay

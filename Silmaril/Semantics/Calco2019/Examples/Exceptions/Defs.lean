module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms
public import Silmaril.Semantics.Calco2019.Parametrized
public import Silmaril.Semantics.ElgotMonads.Thms

/-! # The exception-transformer instance of CALCO 2019 Example 22 -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Exceptions

/-- The left summand returns a value and the right summand is the parameter effect. -/
def resultSum (E X : Type u) : Except E X ≃ X ⊕ E where
  toFun
    | .ok x => .inl x
    | .error e => .inr e
  invFun
    | .inl x => .ok x
    | .inr e => .error e
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl

/-- Example 22 with the identity parameter functor and a total Elgot base on types.
The carrier of its fibre over `E` is `m (Except E X)`. -/
noncomputable def fibre (m : Type u → Type u) [Monad m] [LawfulMonad m]
    [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] (E : Type u) :
    GuardedElgotMonad typeCoproducts.{u} :=
  ofLawfulMonad (ExceptT E m)

end Silmaril.Calco2019.Examples.Exceptions

module

public import Silmaril.Semantics.Calco2019.CompleteElgot.Thms
public import Silmaril.Semantics.ElgotMonads.Thms
public import Mathlib.Data.Quot

/-! # Vacuous and nondeterministic guardedness in CALCO 2019 -/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.SetModels

open CategoryTheory

/-- Example 10(1) is the propositional truncation monad with the least guard. -/
noncomputable def truncGuard : MonadGuardedness typeCoproducts.{u} (ofTypeMonad Trunc) :=
  Guardedness.least _

/-- The unique computation into the sum of two inhabited types, for Example 10(1). -/
def truncChoice : Unit → Trunc (Unit ⊕ Unit) := fun _ => Trunc.mk (.inl ())

/-- Guardedness in Example 10(2) on the nonempty powerset. -/
def HasDirectReturn {X Y Z : Type u} (f : X → SetM (Y ⊕ Z)) : Prop :=
  ∀ x, ∃ y, Sum.inl y ∈ (f x).run

/-- The nonempty powerset of a type. -/
abbrev NonemptyPowerset (Y : Type u) := {p : SetM Y // p.run.Nonempty}

/-- The powerset Elgot monad of Example 20(2), using the inherited type coproducts. -/
noncomputable def powersetElgot : GuardedElgotMonad typeCoproducts.{u} :=
  ofLawfulMonad SetM

end Silmaril.Calco2019.Examples.SetModels

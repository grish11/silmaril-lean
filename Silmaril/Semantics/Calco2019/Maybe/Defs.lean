module

public import Silmaril.Semantics.Calco2019.ExceptionThms
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-! # The Maybe monad and divergence in §1.3 -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] (P : Coproducts C)

/-- The Maybe monad is the identity monad with a single exception. -/
abbrev monad (E : C) : CategoryTheory.Monad C :=
  (Exception.family P (CategoryTheory.Monad.id C)).obj E

variable {P} (T : GuardedElgotMonad P) (total : T.IsElgot)

/-- Divergence at a given input and result object, as the solution of a pure self-loop. -/
noncomputable def divergence (X Y : C) : X ⟶ T.monad.obj Y :=
  let f : Kleisli.mk T.monad X ⟶
      (P.kleisli T.monad).sum (Kleisli.mk T.monad Y) (Kleisli.mk T.monad X) := (P.kleisli T.monad).inr
  (T.iteration.iterate f (total f)).of

/-- The case split on the Maybe carrier interprets a return by the target unit
and the unique exception by divergence. -/
noncomputable def interpret (E Y : C) : P.sum Y E ⟶ T.monad.obj Y :=
  P.desc (T.monad.η.app Y) (divergence T total E Y)

end Silmaril.Calco2019.Maybe

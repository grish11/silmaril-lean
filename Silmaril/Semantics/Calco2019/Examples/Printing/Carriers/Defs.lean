module

public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.Data.Stream.Init
public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs
public import Silmaril.Semantics.Calco2019.ExceptionThms
public import Silmaril.Semantics.Calco2019.Examples.Printing.Defs
public import Silmaril.Semantics.Calco2019.InductiveResumption.Defs

/-! # Finite-word and productive-printing carriers

The first two carrier identifications in §1.2 of Levy and Goncharov,
*Coinductive Resumption Monads: Guarded Iterative and Guarded Elgot*,
doi:10.4230/LIPIcs.CALCO.2019.13.
-/

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.Carriers

open CategoryTheory CategoryTheory.Endofunctor CategoryTheory.MonoidalCategory

/-- The identity-base resumption family with the printing signature `A × -`. -/
abbrev family (A : Type u) : ParametrizedMonad (Type u) :=
  Exception.parametrized typeCoproducts (CategoryTheory.Monad.id (Type u)) (tensorLeft A)

/-- The paper's functor `X + A × -` at a fixed return type `X`. -/
abbrev layer (A X : Type u) : Type u ⥤ Type u := (family A).parameter X

variable {A X : Type u}

/-- Return immediately, or prepend the next letter to a finite run. -/
def roll : X ⊕ (A × (List A × X)) → List A × X
  | .inl x => ([], x)
  | .inr (a, w, x) => (a :: w, x)

/-- Observe a return or the first printed letter of a productive trace. -/
def observe : Trace A X → X ⊕ (A × Trace A X)
  | .inl ([], x) => .inl x
  | .inl (a :: w, x) => .inr (a, .inl (w, x))
  | .inr s => .inr (Stream'.head s, .inr (Stream'.tail s))

/-- The finite-word carrier with its canonical algebra structure. -/
def algebra (A X : Type u) : Algebra (layer A X) :=
  ⟨List A × X, TypeCat.ofHom roll⟩

/-- The productive-printing carrier with its canonical coalgebra structure. -/
def coalgebra (A X : Type u) : Coalgebra (layer A X) :=
  ⟨Trace A X, TypeCat.ofHom observe⟩

end Silmaril.Calco2019.Examples.Printing.Carriers

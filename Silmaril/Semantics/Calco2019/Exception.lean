module

public import Silmaril.Semantics.Calco2019.KleisliTriple
public import Silmaril.Semantics.Calco2019.Resumption

/-! # The underlying exception monads of Example 22 -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory

variable {C : Type u} [Category.{v} C]
  (P : Coproducts C) (T : CategoryTheory.Monad C)

/-- Inject an exception into the result of a computation. -/
def raise (E X : C) : E ⟶ T.obj (P.sum X E) :=
  P.inr ≫ T.η.app (P.sum X E)

/-- Return normally in the exception monad. -/
def unit (E X : C) : X ⟶ T.obj (P.sum X E) :=
  P.inl ≫ T.η.app (P.sum X E)

/-- Sequence a continuation on normal returns and propagate exceptions. -/
def extend {E X Y : C} (f : X ⟶ T.obj (P.sum Y E)) :
    T.obj (P.sum X E) ⟶ T.obj (P.sum Y E) :=
  (KleisliTriple.ofMonad T).extend (P.desc f (raise P T E Y))

/-- Change the exception object by a map while preserving normal returns. -/
def changeException {E F : C} (h : E ⟶ F) (X : C) :
    T.obj (P.sum X E) ⟶ T.obj (P.sum X F) :=
  T.map (P.map (𝟙 X) h)

end Silmaril.Calco2019.Exception

module

public import Silmaril.Semantics.Calco2019.Exception
import Silmaril.Proofs.Semantics.Calco2019.Exception

/-! # The exception-parameter monad underlying Example 22 -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory

variable {C : Type u} [Category.{v} C]
  (P : Coproducts C) (T : CategoryTheory.Monad C)

theorem unit_extend {E X Y : C} (f : X ⟶ T.obj (P.sum Y E)) :
    unit P T E X ≫ extend P T f = f :=
  Proofs.exception_unit_extend P T f

theorem extend_unit (E X : C) : extend P T (unit P T E X) = 𝟙 (T.obj (P.sum X E)) :=
  Proofs.exception_extend_unit P T E X

theorem extend_comp {E X Y Z : C} (f : X ⟶ T.obj (P.sum Y E)) (g : Y ⟶ T.obj (P.sum Z E)) :
    extend P T f ≫ extend P T g = extend P T (f ≫ extend P T g) :=
  Proofs.exception_extend_comp P T f g

theorem change_unit {E F : C} (h : E ⟶ F) (X : C) :
    unit P T E X ≫ changeException P T h X = unit P T F X :=
  Proofs.changeException_unit P T h X

theorem change_extend {E F X Y : C} (h : E ⟶ F) (f : X ⟶ T.obj (P.sum Y E)) :
    extend P T f ≫ changeException P T h Y =
      changeException P T h X ≫ extend P T (f ≫ changeException P T h Y) :=
  Proofs.changeException_extend P T h f

theorem change_id (E X : C) : changeException P T (𝟙 E) X = 𝟙 _ :=
  Proofs.changeException_id P T E X

theorem change_comp {E F G : C} (h : E ⟶ F) (k : F ⟶ G) (X : C) :
    changeException P T (h ≫ k) X = changeException P T h X ≫ changeException P T k X :=
  Proofs.changeException_comp P T h k X

/-- The monad at a fixed exception parameter. -/
@[expose]
def triple (E : C) : KleisliTriple C where
  obj X := T.obj (P.sum X E)
  unit := unit P T E
  extend f := extend P T f
  unit_extend := unit_extend P T
  extend_unit := extend_unit P T E
  extend_comp := extend_comp P T

/-- The monad map induced by a change of exception parameter. -/
@[expose]
def change {E F : C} (h : E ⟶ F) : (triple P T E).Hom (triple P T F) where
  app := changeException P T h
  unit := change_unit P T h
  extend := change_extend P T h

/-- The monad-valued functor `E ↦ T (- + E)`. -/
@[expose]
def family : ParametrizedMonad C where
  obj E := (triple P T E).monad
  map h := (change P T h).toMonadHom
  map_id E := MonadHom.ext (funext (change_id P T E))
  map_comp h k := MonadHom.ext (funext (change_comp P T h k))

/-- The functor action changes normal returns and leaves the exception object fixed. -/
theorem family_map (E : C) {X Y : C} (f : X ⟶ Y) :
    ((family P T).obj E).map f = T.map (P.map f (𝟙 E)) :=
  Proofs.exception_map P T f

theorem family_extend (E : C) {X Y : C} (f : X ⟶ T.obj (P.sum Y E)) :
    ((family P T).obj E).map f ≫ ((family P T).obj E).μ.app Y = extend P T f :=
  (triple P T E).monad_extend f

/-- The parametrized monad `X # W = T (X + H W)` before equipping it with guarded iteration. -/
@[expose]
def parametrized (H : C ⥤ C) : ParametrizedMonad C :=
  H ⋙ family P T

end Silmaril.Calco2019.Exception

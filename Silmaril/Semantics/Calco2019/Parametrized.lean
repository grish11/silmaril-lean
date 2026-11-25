module

public import Silmaril.Semantics.Calco2019.Resumption

/-! # Parametrized guarded Elgot monads (CALCO 2019, Article 13, Definition 21) -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

namespace GuardedElgotMonadHom

variable {T S U : GuardedElgotMonad P}

@[ext]
theorem ext {f g : GuardedElgotMonadHom P T S} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

protected def id (T : GuardedElgotMonad P) : GuardedElgotMonadHom P T T where
  hom := 𝟙 T.monad
  guarded := by
    intro X Y Z f h
    simpa using h
  iteration := by
    intro X Y f hf
    simp

protected def comp (f : GuardedElgotMonadHom P T S) (g : GuardedElgotMonadHom P S U) :
    GuardedElgotMonadHom P T U where
  hom := f.hom ≫ g.hom
  guarded := by
    intro X Y Z h hh
    simpa [Category.assoc] using g.guarded _ (f.guarded h hh)
  iteration := by
    intro X Y h hh
    have e := congrArg (fun k => k ≫ g.hom.app Y) (f.iteration h hh)
    simpa [Category.assoc] using e.trans (g.iteration _ (f.guarded h hh))

end GuardedElgotMonadHom

instance : Category (GuardedElgotMonad P) where
  Hom := GuardedElgotMonadHom P
  id := GuardedElgotMonadHom.id
  comp := GuardedElgotMonadHom.comp
  id_comp f := GuardedElgotMonadHom.ext (Category.id_comp f.hom)
  comp_id f := GuardedElgotMonadHom.ext (Category.comp_id f.hom)
  assoc f g h := GuardedElgotMonadHom.ext (Category.assoc f.hom g.hom h.hom)

/-- The monad underlying a guarded Elgot monad. -/
abbrev GuardedElgotMonad.forget (P : Coproducts C) : GuardedElgotMonad P ⥤ CategoryTheory.Monad C where
  obj T := T.monad
  map m := m.hom

/-- Definition 21. Functorial variation of guarded Elgot monads in a parameter. -/
abbrev ParametrizedGuardedElgotMonad (P : Coproducts C) := C ⥤ GuardedElgotMonad P

abbrev ParametrizedGuardedElgotMonad.toParametrizedMonad (M : ParametrizedGuardedElgotMonad P) :
    ParametrizedMonad C :=
  M ⋙ GuardedElgotMonad.forget P

namespace ParametrizedGuardedElgotMonad

variable (M : ParametrizedGuardedElgotMonad P)

/-- Parameter maps preserve the unit at each result object. -/
@[reassoc]
theorem parameter_unit {W W' : C} (j : W ⟶ W') (X : C) :
    (M.obj W).monad.η.app X ≫ (M.toParametrizedMonad.parameter X).map j =
      (M.obj W').monad.η.app X :=
  (M.map j).hom.app_η X

/-- Parameter maps preserve the chosen fixpoint of every guarded loop. -/
@[reassoc]
theorem parameter_iteration {W W' X Y : C} (j : W ⟶ W')
    (f : X ⟶ (M.obj W).monad.obj (P.sum Y X))
    (hf : (M.obj W).guard.guarded (Y := Kleisli.mk (M.obj W).monad Y)
      (Z := Kleisli.mk (M.obj W).monad X) (kleisliArrow f)) :
    ((M.obj W).iteration.iterate (kleisliArrow f) hf).of ≫
        (M.toParametrizedMonad.parameter Y).map j =
      ((M.obj W').iteration.iterate
        (kleisliArrow (f ≫ (M.toParametrizedMonad.parameter (P.sum Y X)).map j))
        ((M.map j).guarded f hf)).of :=
  (M.map j).iteration f hf

end ParametrizedGuardedElgotMonad

end Silmaril.Calco2019

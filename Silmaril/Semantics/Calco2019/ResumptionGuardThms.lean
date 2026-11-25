module

public import Silmaril.Semantics.Calco2019.ResumptionGuard
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

/-! # Guardedness and the resumption fixpoint equation -/

public section

universe u v

namespace Silmaril.Calco2019.ParametrizedMonad.Guards

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C} {M : ParametrizedMonad C}
  (G : M.Guards P) (R : FinalResumptions M)

/-- The first-observation guard inherits all three guard laws from the parameter family. -/
@[expose]
def resumptionGuardedness : MonadGuardedness P (R.monad P) where
  guarded f := G.observedGuard R f
  trivial f := by exact Proofs.observedGuard_trivial G R f
  parallel hf hg := by exact Proofs.observedGuard_parallel G R hf hg
  compose h hf hg := by exact Proofs.observedGuard_compose G R h hf hg

end Silmaril.Calco2019.ParametrizedMonad.Guards

namespace Silmaril.Calco2019.ParametrizedGuardedElgotMonad

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)

/-- The inherited guardedness of the resumption monad, with the axioms of Definition 6. -/
@[expose]
def resumptionGuardedness : MonadGuardedness P (R.monad P) :=
  M.toGuards.resumptionGuardedness R

theorem resumptionGuardedness_iff {X Y Z : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y Z) :
    (M.resumptionGuardedness R).guarded f ↔
      M.ResumptionGuard R (Y := Y.of) (Z := Z.of) f.of :=
  Iff.rfl

theorem resumptionGuardedness_total (h : ∀ W : C, (M.obj W).IsElgot)
    {X Y Z : Kleisli (R.monad P)} (f : X ⟶ (P.kleisli (R.monad P)).sum Y Z) :
    (M.resumptionGuardedness R).guarded f :=
  (M.resumptionGuardedness_iff R f).mpr
    (h (R.obj (P.sum Y.of Z.of))
      (Y := Kleisli.mk (M.obj _).monad Y.of) (Z := Kleisli.mk (M.obj _).monad Z.of)
      (kleisliArrow (f.of ≫ R.out (P.sum Y.of Z.of))))

/-- The observation equation characterizes the two-stage iteration uniquely. -/
theorem iterateResumption_characterization {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    R.IsSolution P (M.diamond R f hf) (M.iterateResumption R f hf) ∧
      ∀ g, R.IsSolution P (M.diamond R f hf) g → g = M.iterateResumption R f hf :=
  ⟨R.solve_spec P _, fun g hg => R.solve_unique P _ g hg⟩

/-- The two-stage iteration solves the original recursive equation in the resumption monad. -/
theorem iterateResumption_fixpoint {X Y : C} (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    f ≫ R.extend P (P.desc (R.unit Y) (M.iterateResumption R f hf)) =
      M.iterateResumption R f hf :=
  Proofs.iterateResumption_fixpoint M R f hf

/-- A pure change of state commuting with guarded bodies also commutes with their solutions. -/
theorem iterateResumption_uniform {X Y Z : C}
    (f : X ⟶ R.obj (P.sum Y X)) (g : Z ⟶ R.obj (P.sum Y Z)) (h : Z ⟶ X)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f)
    (hg : M.ResumptionGuard R (Y := Y) (Z := Z) g)
    (comm : h ≫ f = g ≫ (R.monad P).map (P.map (𝟙 Y) h)) :
    h ≫ M.iterateResumption R f hf = M.iterateResumption R g hg :=
  Proofs.iterateResumption_uniform M R f g h hf hg comm

/-- Postprocessing returns preserves guardedness of the loop body. -/
theorem naturalityBody_guarded {X Y Z : C} (f : X ⟶ R.obj (P.sum Y X)) (g : Y ⟶ R.obj Z)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    M.ResumptionGuard R (Y := Z) (Z := X) (M.naturalityBody R f g) :=
  Proofs.naturalityBody_guarded M R f g hf

/-- Postprocessing the body's return commutes with solving the guarded resumption loop. -/
theorem iterateResumption_naturality {X Y Z : C} (f : X ⟶ R.obj (P.sum Y X)) (g : Y ⟶ R.obj Z)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    M.iterateResumption R (M.naturalityBody R f g) (M.naturalityBody_guarded R f g hf) =
      M.iterateResumption R f hf ≫ R.extend P g :=
  Proofs.iterateResumption_naturality M R f g hf (M.naturalityBody_guarded R f g hf)

theorem observed_fixpoint {X Y : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y X) (hf : M.observedGuard R (Y := Y) (Z := X) f) :
    Guardedness.IsFixpoint f (kleisliArrow (M.iterateResumption R f.of hf)) :=
  Proofs.observedFixpoint M R f hf

/-- The characterized resumption solutions, packaged as guarded Kleisli fixpoints. -/
@[expose]
def resumptionFixpoints : (M.resumptionGuardedness R).Fixpoints where
  iterate f hf := kleisliArrow (M.iterateResumption R f.of ((M.resumptionGuardedness_iff R f).mp hf))
  fixpoint f hf := M.observed_fixpoint R f ((M.resumptionGuardedness_iff R f).mp hf)

theorem resumptionFixpoints_of {X Y : Kleisli (R.monad P)}
    (f : X ⟶ (P.kleisli (R.monad P)).sum Y X) (hf : (M.resumptionGuardedness R).guarded f) :
    ((M.resumptionFixpoints R).iterate f hf).of =
      M.iterateResumption R f.of ((M.resumptionGuardedness_iff R f).mp hf) :=
  rfl

end Silmaril.Calco2019.ParametrizedGuardedElgotMonad

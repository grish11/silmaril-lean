module

public import Silmaril.Semantics.Calco2019.ExceptionResumption.Free.Thms
import Silmaril.Proofs.Semantics.Calco2019.ResumptionSpecializations

/-! # Guarded iterative and total resumption monads (CALCO 2019, §1.3) -/

public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

/-- Unique guarded solutions at each parameter give unique guarded solutions
in the final-coalgebra resumption monad. -/
theorem ParametrizedGuardedElgotMonad.resumptionGuardedness_iterative
    (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)
    (h : ∀ W : C, (M.obj W).guard.Iterative) : (M.resumptionGuardedness R).Iterative :=
  Proofs.resumption_iterative M R h

/-- For a total Elgot monad every natural transformation into its functor
is admissible as an operation interpretation. -/
theorem GuardedElgotMonad.IsElgot.guardedNatTrans [HasInitial C]
    {S : GuardedElgotMonad P} (h : S.IsElgot) {H : C ⥤ C} (σ : H ⟶ (S.monad : C ⥤ C)) :
    S.guard.GuardedNatTrans P σ :=
  fun X => h (Y := Kleisli.mk S.monad (⊥_ C)) (Z := Kleisli.mk S.monad X) _

/-- A guard-preserving monad map into a guarded iterative target preserves its
chosen solutions. -/
noncomputable def GuardedElgotMonadHom.ofGuardPreserving {T S : GuardedElgotMonad P}
    (m : T.monad ⟶ S.monad) (hm : MonadGuardedness.Preserves P T.guard S.guard m)
    (hS : S.guard.Iterative) : GuardedElgotMonadHom P T S where
  hom := m
  guarded := hm
  iteration := Proofs.iterative_map_iteration m hm hS

@[simp]
theorem GuardedElgotMonadHom.ofGuardPreserving_hom {T S : GuardedElgotMonad P}
    (m : T.monad ⟶ S.monad) (hm : MonadGuardedness.Preserves P T.guard S.guard m)
    (hS : S.guard.Iterative) :
    (GuardedElgotMonadHom.ofGuardPreserving m hm hS).hom = m := by
  unfold GuardedElgotMonadHom.ofGuardPreserving
  rfl

namespace Exception

variable (T : GuardedElgotMonad P) (H : C ⥤ C)
  (R : FinalResumptions (parametrizedElgot T H).toParametrizedMonad)

/-- The exception construction preserves uniqueness of guarded solutions. -/
theorem fibre_iterative (E : C) (h : T.guard.Iterative) : (fibre T E).guard.Iterative :=
  Proofs.exception_iterative T E h

/-- Coinductive exception resumptions over a guarded iterative base are
guarded iterative. Their free-extension property then restricts to guarded
iterative monads. -/
theorem resumption_iterative (h : T.guard.Iterative) :
    ((parametrizedElgot T H).resumptionElgotMonad R).guard.Iterative :=
  (parametrizedElgot T H).resumptionGuardedness_iterative R (fun W => fibre_iterative T (H.obj W) h)

/-- Coinductive exception resumptions over a total Elgot base are total.
Their free-extension property then admits arbitrary natural generators into
total Elgot target monads. -/
theorem resumption_isElgot (h : T.IsElgot) :
    ((parametrizedElgot T H).resumptionElgotMonad R).IsElgot := by
  apply (parametrizedElgot T H).resumptionElgotMonad_isElgot R
  intro W X Y Z f
  exact h (Y := Kleisli.mk T.monad (P.sum Y.of (H.obj W))) (Z := Kleisli.mk T.monad Z.of)
    (kleisliArrow (f.of ≫ T.monad.map (rearrange P (H.obj W))))

/-- Specializing the free extension to the vacuously guarded identity gives
the free guarded Elgot monad on the endofunctor. -/
theorem resumption_freeObject [HasInitial C]
    (R₀ : FinalResumptions (parametrizedElgot (guardedIdentity P) H).toParametrizedMonad) :
    (guardedBimodule P).IsFreeObject (resumptionGenerator R₀) :=
  Proofs.resumption_freeObject R₀

end Exception
end Silmaril.Calco2019

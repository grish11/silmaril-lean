module

public import Silmaril.SSA.MLIR.SCF.LetIter.Defs

/-! Typing, observation and ambient substitution for the region view. -/

public section

universe u v w

namespace Silmaril.MLIR.SCF.LetIter

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless

variable {Φ : Type u} {n m l : Nat}

/-- Observing every continuation and observing full answers induce the same
equivalence on positional LetIter, including terms that loop or invoke primitives. -/
theorem continuationObs_iff_answerObs (t t' : Tm Empty Φ n) :
    ContinuationObs.{u, v, w} t t' ↔ Tm.Obs.{u, v, w, 0} t t' := by
  refine ⟨fun h => ?_, fun h k => h.let₁ (.refl k)⟩
  exact (obs_letEta t).symm.trans ((h (.bv 0)).trans (obs_letEta t'))

/-- The native form preserves the exact region types. -/
theorem RegionLoop.WellTyped.lower {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    {p : RegionLoop Φ n} {Γ : Ctx Empty τ} {β : BoundCtx τ n} {state payload result : τ}
    (h : p.WellTyped Γ β state payload result) : HasType Φ Γ β p.lower result :=
  .let₁ (.iter h.init (.case h.condition (.inl .newest) (.inr h.afterRegion.underBinder))) h.parent

namespace RegionLoop

@[simp] theorem rename_id (p : RegionLoop Φ n) : p.rename (fun i => i) = p := by
  cases p
  simp [rename]

theorem rename_comp (p : RegionLoop Φ n) (f : Fin n → Fin m) (g : Fin m → Fin l) :
    (p.rename f).rename g = p.rename (g ∘ f) := by
  cases p
  simp [rename, Tm.rename_comp, Function.comp_def, Tm.up_comp]

@[simp] theorem bsubst_id (p : RegionLoop Φ n) : p.bsubst .bv = p := by
  cases p
  simp [bsubst, Tm.upSub_bv (fun i : Fin n => i)]

theorem bsubst_comp (p : RegionLoop Φ n) (f : Fin n → Tm Empty Φ m) (g : Fin m → Tm Empty Φ l) :
    (p.bsubst f).bsubst g = p.bsubst (fun i => (f i).bsubst g) := by
  cases p
  simp [bsubst, Tm.bsubst_comp, Tm.upSub_comp]

@[simp] theorem lower_rename (p : RegionLoop Φ n) (f : Fin n → Fin m) :
    (p.rename f).lower = p.lower.rename f := by
  simp [lower, iterBody, rename, Tm.rename]
  rfl

@[simp] theorem lower_bsubst (p : RegionLoop Φ n) (f : Fin n → Tm Empty Φ m) :
    (p.bsubst f).lower = p.lower.bsubst f := by
  simp [lower, iterBody, bsubst, Tm.bsubst]
  rfl

end RegionLoop
end Silmaril.MLIR.SCF.LetIter

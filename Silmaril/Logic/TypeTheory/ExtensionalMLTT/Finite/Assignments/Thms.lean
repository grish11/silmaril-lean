module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Assignments.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments

public section

/-!
# Same-budget finite-support typed assignment for every bounded target rule

Assignments carry actual bounded target typings for every source lookup.
Every closed bounded rule preserves those assignments at the same `levels`,
with actual target context well-formedness at that budget. Cofinite avoidance
sets include the assignment support, target declarations and support-image
free names. Every member of each binder family retains the same level bound.

Actual arguments instantiate cofinite families through this theorem. Neither
the lookup typings nor preservation of the whole calculus is assumed as a
global certificate. Theories remain empty; name contexts may be nonempty.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Bounded lookup-image typings erase to the existing actual assignment predicate. -/
theorem ECtx.AssignmentB.forget {levels : ℕ} {σ : String → ETm 0} {Γ Δ : ECtx}
    (e : ECtx.AssignmentB levels σ Γ Δ) : ECtx.Assignment σ Γ Δ :=
  fun h => (e h).forget

/-- Enlarge the budget of every actual lookup-image typing. -/
theorem ECtx.AssignmentB.weakenLevels {levels more : ℕ} {σ : String → ETm 0} {Γ Δ : ECtx}
    (e : ECtx.AssignmentB levels σ Γ Δ) (hle : levels ≤ more) :
    ECtx.AssignmentB more σ Γ Δ := fun h => (e h).weakenLevels hle

/-- Actual variables give the identity assignment at the target's existing budget. -/
theorem ECtx.AssignmentB.identity {levels : ℕ} {Γ : ECtx}
    (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star) : ECtx.AssignmentB levels ETm.fv Γ Γ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments.assignment_identity hΓ

/-- Extend an actual assignment under a fresh matching declaration at the same budget. -/
theorem ECtx.AssignmentB.cons {levels : ℕ} {σ : String → ETm 0} {Γ Δ : ECtx}
    {y : String} {A : ETm 0} (e : ECtx.AssignmentB levels σ Γ Δ)
    (hy : σ y = .fv y) (hyΔ : y ∉ Δ.dv)
    (hctx : ECtx.JEqB levels ∅ (Δ.cons y (A.fmap σ)) .unit .star .star) :
    ECtx.AssignmentB levels σ (Γ.cons y A) (Δ.cons y (A.fmap σ)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments.lookup_subst_cons e hy hyΔ hctx

/-- All 34 closed bounded rules preserve actual finite-support typed assignments. -/
theorem ECtx.JEqB.assign {levels : ℕ} {Γ Δ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ A a b) (σ : String → ETm 0) (K : Finset String)
    (hσ : ETm.Supported σ K) (e : ECtx.AssignmentB levels σ Γ Δ)
    (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star) :
    ECtx.JEqB levels ∅ Δ (A.fmap σ) (a.fmap σ) (b.fmap σ) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments.substitution σ K hσ h Δ e hΔ

/-- An actual typed argument supplies the newest declaration's assignment image. -/
theorem ECtx.AssignmentB.update {levels : ℕ} {σ : String → ETm 0} {Γ Δ : ECtx}
    {y : String} {A v : ETm 0} (e : ECtx.AssignmentB levels σ Γ Δ)
    (hyΓ : y ∉ Γ.typeFvs) (hyA : y ∉ A.fvs)
    (hv : ECtx.JEqB levels ∅ Δ (A.fmap σ) v v) :
    ECtx.AssignmentB levels (Function.update σ y v) (Γ.cons y A) Δ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments.assignment_update e hyΓ hyA hv

/-- Every cofinite binder family instantiates at an actual argument without raising levels. -/
theorem ECtx.JEqB.instantiate {levels : ℕ} {Γ : ECtx} {A v : ETm 0} {B b b' : ETm 1}
    {L : Finset String} (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star)
    (hv : ECtx.JEqB levels ∅ Γ A v v)
    (h : ∀ y ∉ L, ECtx.JEqB levels ∅ (Γ.cons y A) (B.open y) (b.open y) (b'.open y)) :
    ECtx.JEqB levels ∅ Γ (B.lst v) (b.lst v) (b'.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments.instantiate hΓ hv h

/-- Convert the newest declaration by an actual type equality at the same rule budget. -/
theorem ECtx.JEqB.changeLast {levels n : ℕ} {Γ : ECtx} {x : String} {A A' T t u : ETm 0}
    (hΓ : ECtx.JEqB levels ∅ Γ .unit .star .star) (hx : x ∉ Γ.dv) (hn : n < levels)
    (hAA' : ECtx.JEqB levels ∅ Γ (.univ n) A A') (h : ECtx.JEqB levels ∅ (Γ.cons x A) T t u) :
    ECtx.JEqB levels ∅ (Γ.cons x A') T t u :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedAssignments.changeLast hΓ hx hn hAA' h

end Silmaril.Logic.TypeTheory.ExtensionalMLTT

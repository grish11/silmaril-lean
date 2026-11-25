module

public import Silmaril.SSA.Isotope.Institution.Thms

/-! # A region view of a positional LetIter loop

The four regions use native LetIter expressions. A condition return uses a sum tag to
encode the branch and carries the same payload interface on both branches. The before
state is visible in the before region only. The after region receives the condition
payload and yields the next before state. The parent continuation receives the payload
of the false condition. All four regions may use the ambient positional variables.
-/

@[expose] public section

universe u v

namespace Silmaril.MLIR.SCF.LetIter

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm HasType)

/-- Two answers agree under every native call-by-value continuation. The continuation
receives the returned value in slot zero, alongside the same ambient variables. -/
def ContinuationObs.{i, a, s} {Φ : Type i} {n : Nat} (t t' : Tm Empty Φ n) : Prop :=
  ∀ k : Tm Empty Φ (n + 1), Tm.Obs.{i, a, s, 0} (.let₁ t k) (.let₁ t' k)

/-- A single structured loop boundary whose bodies are native positional LetIter terms. -/
structure RegionLoop (Φ : Type u) (n : Nat) where
  /-- Initial before state. -/
  init : Tm Empty Φ n
  /-- Condition computation with the current before state in slot zero.
  A left tag exits and a right tag enters the after region. -/
  condition : Tm Empty Φ (n + 1)
  /-- The computation up to the yield, with the condition payload in slot zero. -/
  afterRegion : Tm Empty Φ (n + 1)
  /-- The code after the loop, with the false condition payload in slot zero. -/
  parent : Tm Empty Φ (n + 1)

namespace RegionLoop

variable {Φ : Type u} {n m : Nat}

/-- The typing interface of this slice of SCF. The before state and
condition payload can have different types. Both condition arms pass the same payload type. -/
structure WellTyped {τ : Type v} [TypeFormers τ] [HasTy Φ τ]
    (p : RegionLoop Φ n) (Γ : Ctx Empty τ) (β : BoundCtx τ n)
    (state payload result : τ) : Prop where
  init : HasType Φ Γ β p.init state
  condition : HasType Φ Γ (.snoc β state) p.condition (coprod payload payload)
  afterRegion : HasType Φ Γ (.snoc β payload) p.afterRegion state
  parent : HasType Φ Γ (.snoc β payload) p.parent result

/-- The after region skips the saved before-state slot. Iteration returns a left
payload and uses a right payload as its next state. -/
def iterBody (p : RegionLoop Φ n) : Tm Empty Φ (n + 1) :=
  .case p.condition (.inl (.bv 0)) (.inr p.afterRegion.underBinder)

/-- Compile the boundary to a native iteration followed by a call-by-value continuation. -/
def lower (p : RegionLoop Φ n) : Tm Empty Φ n :=
  .let₁ (.iter p.init p.iterBody) p.parent

/-- Capture-avoiding substitution of the ambient positional variables. -/
def bsubst (f : Fin n → Tm Empty Φ m) (p : RegionLoop Φ n) : RegionLoop Φ m where
  init := p.init.bsubst f
  condition := p.condition.bsubst (Tm.upSub f)
  afterRegion := p.afterRegion.bsubst (Tm.upSub f)
  parent := p.parent.bsubst (Tm.upSub f)

/-- Rename the ambient positional variables. -/
def rename (f : Fin n → Fin m) (p : RegionLoop Φ n) : RegionLoop Φ m where
  init := p.init.rename f
  condition := p.condition.rename (Tm.up f)
  afterRegion := p.afterRegion.rename (Tm.up f)
  parent := p.parent.rename (Tm.up f)

end RegionLoop
end Silmaril.MLIR.SCF.LetIter

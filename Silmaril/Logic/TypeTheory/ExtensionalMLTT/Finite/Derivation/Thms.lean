module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedDerivation

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Erasure retains the exact rules of the existing target calculus. -/
theorem ECtx.JEqB.forget {levels : ℕ} {H : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) : ECtx.JEqH H Γ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedDerivation.forget h

/-- Enlarge the common rule budget and substitute actual bounded hypothesis proofs. -/
theorem ECtx.JEqB.transform {levels more : ℕ} {H H' : Set EJdg}
    {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) (hle : levels ≤ more)
    (hh : ∀ j ∈ H, ECtx.JEqB more H' j.Γ j.A j.a j.b) :
    ECtx.JEqB more H' Γ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedDerivation.transport hle hh h

/-- Every cofinite branch remains within the same enlarged level budget. -/
theorem ECtx.JEqB.weakenLevels {levels more : ℕ} {H : Set EJdg}
    {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqB levels H Γ A a b) (hle : levels ≤ more) :
    ECtx.JEqB more H Γ A a b := h.transform hle (fun _ hj => .hyp hj)

/-- Substitute bounded derivations for hypothesis leaves throughout every rule. -/
theorem ECtx.JEqB.bind {levels : ℕ} {H H' : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b)
    (hh : ∀ j ∈ H, ECtx.JEqB levels H' j.Γ j.A j.a j.b) :
    ECtx.JEqB levels H' Γ A a b := h.transform (Nat.le_refl _) hh

/-- Enlarging the hypothesis theory preserves actual bounded derivability. -/
theorem ECtx.JEqB.mono {levels : ℕ} {H H' : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) (hh : H ⊆ H') : ECtx.JEqB levels H' Γ A a b :=
  h.bind (fun _ hj => .hyp (hh hj))

/-- Compatibility name for monotone inclusion of the common rule budget. -/
theorem ECtx.JEqB.include {levels more : ℕ} (hlevels : levels ≤ more)
    {H : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels H Γ A a b) : ECtx.JEqB more H Γ A a b :=
  h.weakenLevels hlevels

end Silmaril.Logic.TypeTheory.ExtensionalMLTT

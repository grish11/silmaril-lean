module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.BoundedDerivation
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.FiniteSoundness

@[expose] public section

/-! # Finite-universe soundness of every extensional MLTT rule -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.SetTheory

universe u

/-- Every bounded proof is a proof in the original extensional calculus. -/
theorem Ctx.JEqB.forget {levels : RuleBudget} {H : Set Jdg} {Γ : Ctx} {A a b : Tm 0}
    (h : Ctx.JEqB levels H Γ A a b) : Ctx.JEqH H Γ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.forget h

/-- Substitute bounded proofs for theory hypotheses. -/
theorem Ctx.JEqB.bind {levels : RuleBudget} {H H' : Set Jdg}
    (hh : ∀ j ∈ H, Ctx.JEqB levels H' j.Γ j.A j.a j.b)
    {Γ : Ctx} {A a b : Tm 0} (h : Ctx.JEqB levels H Γ A a b) :
    Ctx.JEqB levels H' Γ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.transport (le_refl levels) hh h

/-- Increasing the hypothesis theory preserves bounded derivability. -/
theorem Ctx.JEqB.mono {levels : RuleBudget} {H H' : Set Jdg} (hh : H ⊆ H')
    {Γ : Ctx} {A a b : Tm 0} (h : Ctx.JEqB levels H Γ A a b) :
    Ctx.JEqB levels H' Γ A a b :=
  h.bind fun _ hj => .hyp (hh hj)

/-- Include a bounded proof without increasing the levels of any rule parameter. -/
theorem Ctx.JEqB.include {levels more : RuleBudget} (hlevels : levels ≤ more)
    {H : Set Jdg} {Γ : Ctx} {A a b : Tm 0}
    (h : Ctx.JEqB levels H Γ A a b) : Ctx.JEqB more H Γ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.transport hlevels (fun _ hj => .hyp hj) h

/-- All rules preserve validity in a supplied finite tower, under valid hypotheses. -/
theorem Ctx.JEqB.sound {levels : ℕ} (T : FiniteTower.{u} levels)
    {H : Set Jdg} (hH : ∀ j ∈ H, j.ValidIn T.U) {Γ : Ctx} {A a b : Tm 0}
    (h : Ctx.JEqB levels H Γ A a b) : (⟨Γ, A, a, b⟩ : Jdg).ValidIn T.U :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.finite_sound T hH h

/-- A supplied finite tower excludes a closed inhabitant of Empty. -/
theorem Ctx.JEqB.consistent {levels : ℕ} (T : FiniteTower.{u} levels) {a : Tm 0} :
    ¬ Ctx.JEqB levels ∅ .nil .empty a a :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.finite_consistent T

/-- Consistency at a fixed count from the typeclass supplying its finite set model. -/
theorem Ctx.JEqB.consistent_of_tower (levels : ℕ) [HasFiniteTower.{u} levels] {a : Tm 0} :
    ¬ Ctx.JEqB levels ∅ .nil .empty a a :=
  Ctx.JEqB.consistent (HasFiniteTower.tower levels)

/-- One available universe: its concrete model lives in the next Lean carrier. -/
theorem Ctx.JEqB.consistent_one {a : Tm 0} : ¬ Ctx.JEqB 1 ∅ .nil .empty a a :=
  Ctx.JEqB.consistent FiniteTower.one.{0}

/-- Two available universes, using the concrete two-step set hierarchy. -/
theorem Ctx.JEqB.consistent_two {a : Tm 0} : ¬ Ctx.JEqB 2 ∅ .nil .empty a a :=
  Ctx.JEqB.consistent FiniteTower.two.{0}

/-- Three available universes, using the concrete three-step set hierarchy. -/
theorem Ctx.JEqB.consistent_three {a : Tm 0} : ¬ Ctx.JEqB 3 ∅ .nil .empty a a :=
  Ctx.JEqB.consistent FiniteTower.three.{0}

/-- The one-universe system has an inhabited closed data type. -/
theorem Ctx.JEqB.zero_one : Ctx.JEqB 1 ∅ .nil .nats .zero .zero :=
  .zero .nil_ok

/-- The lowest universe has a type in the two-universe system. -/
theorem Ctx.JEqB.univ_zero_two : Ctx.JEqB 2 ∅ .nil (.univ 1) (.univ 0) (.univ 0) :=
  .univ (by decide) .nil_ok

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

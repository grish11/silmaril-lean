module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Substitution
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Substitution
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Weakening
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.TypeInstantiation

@[expose] public section

/-! Type-family abstraction and instantiation via beta, with an explicit next-universe budget. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg}

theorem Ctx.JEqB.type_family_formation {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0}
    (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) :
    Γ.JEqB levels H (.univ (n + 1)) (.pi A (.univ n)) (.pi A (.univ n)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.type_family_formation hn hΓ hA

theorem Ctx.JEqB.abstract_type {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star) (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x)) :
    Γ.JEqB levels H (.pi A (.univ n)) (.abs A B) (.abs A B) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.abstract_type hn hΓ hA hB

theorem Ctx.JEqB.type_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a : Tm 0} {B : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star) (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H (.univ n) (.app (.abs A B) a) (B.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.type_beta hn hΓ hA hB ha

/-- This beta-derived rule uses Uₙ : Uₙ₊₁; it is not same-bound structural substitution. -/
theorem Ctx.JEqB.instantiate_type {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a : Tm 0} {B : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star) (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_type hn hΓ hA hB ha

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

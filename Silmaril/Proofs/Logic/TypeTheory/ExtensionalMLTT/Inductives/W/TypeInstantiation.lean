module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Substitution
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg}

private theorem universe_family {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0}
    (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (x : String) (hx : x ∉ Γ.dv) :
    (Γ.cons x A).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open x) ((.univ n : Tm 1).open x) := by
  have hctx : (Γ.cons x A).JEqB levels H .unit .star .star :=
    .cons_ok (by budget_omega) hΓ hx hA
  simpa only [Tm.open] using Ctx.JEqB.univ hn hctx

theorem type_family_formation {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0}
    (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) :
    Γ.JEqB levels H (.univ (n + 1)) (.pi A (.univ n)) (.pi A (.univ n)) :=
  .pi (L := Γ.dv) hn (.cumul hn (Nat.le_succ n) hA) (universe_family hn hΓ hA)

/-- An object abstraction of a small type family; the family universe itself is typable. -/
theorem abstract_type {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star) (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x)) :
    Γ.JEqB levels H (.pi A (.univ n)) (.abs A B) (.abs A B) := by
  have hA' : Γ.JEqB levels H (.univ (n + 1)) A A :=
    .cumul hn (Nat.le_succ n) hA
  apply Ctx.JEqB.abs (n := n + 1) (L := L ∪ Γ.dv) hn hA'
  · intro x hx
    exact universe_family hn hΓ hA x (fun h => hx (Finset.mem_union_right _ h))
  · intro x hx
    simpa only [Tm.open] using hB x (fun h => hx (Finset.mem_union_left _ h))

/-- Actual object computation for instantiation of a small type family. -/
theorem type_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a : Tm 0} {B : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star) (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H (.univ n) (.app (.abs A B) a) (B.lst a) := by
  have hA' : Γ.JEqB levels H (.univ (n + 1)) A A :=
    .cumul hn (Nat.le_succ n) hA
  have hU : ∀ x ∉ L ∪ Γ.dv, (Γ.cons x A).JEqB levels H (.univ (n + 1))
      ((.univ n : Tm 1).open x) ((.univ n : Tm 1).open x) := by
    intro x hx
    exact universe_family hn hΓ hA x (fun h => hx (Finset.mem_union_right _ h))
  have hb : ∀ x ∉ L ∪ Γ.dv, (Γ.cons x A).JEqB levels H ((.univ n : Tm 1).open x)
      (B.open x) (B.open x) := by
    intro x hx
    simpa only [Tm.open] using hB x (fun h => hx (Finset.mem_union_left _ h))
  simpa only [Tm.lst] using Ctx.JEqB.beta_app hn hA' hU hb ha

/-- Type-family instantiation derived by beta; this route uses one additional universe. -/
theorem instantiate_type {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a : Tm 0} {B : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star) (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) :=
  .trans (type_beta hn hΓ hA hB ha).symm (type_beta hn hΓ hA hB ha)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

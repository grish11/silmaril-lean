module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Substitution
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Weakening

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A B b : Tm 0}

theorem constant_family_of_hypotheses {H : Set Jdg} (hh : HypothesisTransport levels H H) (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hB : Γ.JEqB levels H (.univ n) B B) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB levels H (.univ n) (B.wk0.open x) (B.wk0.open x) := by
  intro x hx
  simpa only [Tm.closed_wk0_open] using Ctx.JEqB.weaken_of_hypotheses hh hB (Ctx.LookupLE.fresh_cons hx A) (.cons_ok hn hΓ hx hA)

theorem arrow_formation_of_hypotheses {H : Set Jdg} (hh : HypothesisTransport levels H H) (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hB : Γ.JEqB levels H (.univ n) B B) :
    Γ.JEqB levels H (.univ n) (.arr A B) (.arr A B) :=
  .pi hn hA (constant_family_of_hypotheses hh hn hΓ hA hB)

theorem constant_abstraction_of_hypotheses {H : Set Jdg} (hh : HypothesisTransport levels H H) (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hB : Γ.JEqB levels H (.univ n) B B)
    (hb : Γ.JEqB levels H B b b) :
    Γ.JEqB levels H (.arr A B) (.abs A b.wk0) (.abs A b.wk0) := by
  apply Ctx.JEqB.abs hn hA (constant_family_of_hypotheses hh hn hΓ hA hB)
  intro x hx
  simpa only [Tm.closed_wk0_open] using Ctx.JEqB.weaken_of_hypotheses hh hb (Ctx.LookupLE.fresh_cons hx A) (.cons_ok hn hΓ hx hA)


theorem constant_family (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hB : Γ.JEqB levels ∅ (.univ n) B B) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.wk0.open x) (B.wk0.open x) :=
  constant_family_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hB

theorem arrow_formation (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hB : Γ.JEqB levels ∅ (.univ n) B B) :
    Γ.JEqB levels ∅ (.univ n) (.arr A B) (.arr A B) :=
  arrow_formation_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hB

theorem constant_abstraction (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hB : Γ.JEqB levels ∅ (.univ n) B B)
    (hb : Γ.JEqB levels ∅ B b b) :
    Γ.JEqB levels ∅ (.arr A B) (.abs A b.wk0) (.abs A b.wk0) :=
  constant_abstraction_of_hypotheses (HypothesisTransport.empty levels ∅) hn hΓ hA hB hb

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

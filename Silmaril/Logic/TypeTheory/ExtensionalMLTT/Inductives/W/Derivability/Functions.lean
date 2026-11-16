module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Substitution
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Weakening
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.FunctionTyping

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A B b : Tm 0}

theorem Ctx.JEqB.constant_family_of_hypotheses {H : Set Jdg} (hh : HypothesisTransport levels H H) (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hB : Γ.JEqB levels H (.univ n) B B) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB levels H (.univ n) (B.wk0.open x) (B.wk0.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constant_family_of_hypotheses hh hn hΓ hA hB

theorem Ctx.JEqB.arrow_formation_of_hypotheses {H : Set Jdg} (hh : HypothesisTransport levels H H) (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hB : Γ.JEqB levels H (.univ n) B B) :
    Γ.JEqB levels H (.univ n) (.arr A B) (.arr A B) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.arrow_formation_of_hypotheses hh hn hΓ hA hB

theorem Ctx.JEqB.constant_abstraction_of_hypotheses {H : Set Jdg} (hh : HypothesisTransport levels H H) (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hB : Γ.JEqB levels H (.univ n) B B)
    (hb : Γ.JEqB levels H B b b) :
    Γ.JEqB levels H (.arr A B) (.abs A b.wk0) (.abs A b.wk0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constant_abstraction_of_hypotheses hh hn hΓ hA hB hb

theorem Ctx.JEqB.constant_family (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hB : Γ.JEqB levels ∅ (.univ n) B B) :
    ∀ x ∉ Γ.dv, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.wk0.open x) (B.wk0.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constant_family hn hΓ hA hB

theorem Ctx.JEqB.arrow_formation (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hB : Γ.JEqB levels ∅ (.univ n) B B) :
    Γ.JEqB levels ∅ (.univ n) (.arr A B) (.arr A B) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.arrow_formation hn hΓ hA hB

theorem Ctx.JEqB.constant_abstraction (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hB : Γ.JEqB levels ∅ (.univ n) B B)
    (hb : Γ.JEqB levels ∅ B b b) :
    Γ.JEqB levels ∅ (.arr A B) (.abs A b.wk0) (.abs A b.wk0) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constant_abstraction hn hΓ hA hB hb

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

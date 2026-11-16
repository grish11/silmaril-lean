module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Head.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.HeadTyping

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem Ctx.JEqB.headStep_typing_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I : Tm 0} {B g : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (g.open x) (g.open x)) :
    Γ.JEqB levels H (Tm.wStepType A B I.wk0)
      (Tm.headStep A B I g) (Tm.headStep A B I g) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.headStep_typing_of_hypotheses hh hn hΓ hA hI hB hg

theorem Ctx.JEqB.head_typing_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I t : Tm 0} {B g : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (g.open x) (g.open x))
    (ht : Γ.JEqB levels H (.wtype A B) t t) :
    Γ.JEqB levels H I (Tm.head A B I g t) (Tm.head A B I g t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.head_typing_of_hypotheses hh hn hΓ hA hI hB hg ht

theorem Ctx.JEqB.headStep_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I : Tm 0} {B g : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ I (g.open x) (g.open x)) :
    Γ.JEqB levels ∅ (Tm.wStepType A B I.wk0)
      (Tm.headStep A B I g) (Tm.headStep A B I g) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.headStep_typing hn hΓ hA hI hB hg

theorem Ctx.JEqB.head_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I t : Tm 0} {B g : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ I (g.open x) (g.open x))
    (ht : Γ.JEqB levels ∅ (.wtype A B) t t) :
    Γ.JEqB levels ∅ I (Tm.head A B I g t) (Tm.head A B I g t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.head_typing hn hΓ hA hI hB hg ht

theorem head_leaf_typing : Ctx.JEqB 1 ∅ .nil .unit
    (Tm.head .unit .empty .unit .star Examples.leaf)
    (Tm.head .unit .empty .unit .star Examples.leaf) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.head_leaf_typing

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

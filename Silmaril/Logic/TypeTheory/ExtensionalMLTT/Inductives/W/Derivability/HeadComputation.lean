module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.ConstantStep
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Substitution
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.HeadComputation

@[expose] public section

/-! Actual recursive-call typing and normalized constant-result W-head computation. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I s a f p : Tm 0} {B : Tm 1} {L : Finset String}

theorem Ctx.JEqB.recChildren_constant_typing_of_hypotheses (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels H (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels H (.arr (B.lst a) I)
      (Tm.recChildren A B I.wk0 s a f) (Tm.recChildren A B I.wk0 s a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.recChildren_constant_typing_of_hypotheses hH hn hΓ hA hI hB hs ha hf

theorem Ctx.JEqB.constant_abstraction_beta_of_hypotheses {b : Tm 0} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hb : Γ.JEqB levels H I b b) (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H I (.app (.abs A b.wk0) a) b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constant_abstraction_beta_of_hypotheses hH hn hΓ hA hI hb ha

theorem Ctx.JEqB.head_beta_of_hypotheses {g : Tm 1} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (g.open x) (g.open x))
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels H I (Tm.head A B I g (.sup A B a f)) (g.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.head_beta_of_hypotheses hH hn hΓ hA hI hB hg ha hf

theorem Ctx.JEqB.recChildren_constant_beta_of_hypotheses (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels H (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f)
    (hp : Γ.JEqB levels H (B.lst a) p p) :
    Γ.JEqB levels H I
      (.app (Tm.recChildren A B I.wk0 s a f) p)
      (.wrec A B I.wk0 s (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.recChildren_constant_beta_of_hypotheses hH hn hΓ hA hI hB hs ha hf hp

theorem Ctx.JEqB.recChildren_constant_typing (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels ∅ (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels ∅ (.arr (B.lst a) I)
      (Tm.recChildren A B I.wk0 s a f) (Tm.recChildren A B I.wk0 s a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.recChildren_constant_typing hn hΓ hA hI hB hs ha hf

theorem Ctx.JEqB.constant_abstraction_beta {b : Tm 0} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hb : Γ.JEqB levels ∅ I b b) (ha : Γ.JEqB levels ∅ A a a) :
    Γ.JEqB levels ∅ I (.app (.abs A b.wk0) a) b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constant_abstraction_beta hn hΓ hA hI hb ha

theorem Ctx.JEqB.head_beta {g : Tm 1} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hg : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ I (g.open x) (g.open x))
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels ∅ I (Tm.head A B I g (.sup A B a f)) (g.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.head_beta hn hΓ hA hI hB hg ha hf

theorem Ctx.JEqB.recChildren_constant_beta (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hs : Γ.JEqB levels ∅ (Tm.wStepType A B I.wk0) s s)
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f)
    (hp : Γ.JEqB levels ∅ (B.lst a) p p) :
    Γ.JEqB levels ∅ I
      (.app (Tm.recChildren A B I.wk0 s a f) p)
      (.wrec A B I.wk0 s (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.recChildren_constant_beta hn hΓ hA hI hB hs ha hf hp

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

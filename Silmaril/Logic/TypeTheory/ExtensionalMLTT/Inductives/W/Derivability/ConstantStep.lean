module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Head
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.ConstantStepTyping

@[expose] public section

/-! Actual constant-motive W steps with arbitrary use of children and recursive hypotheses. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem Ctx.JEqB.arrow_abstraction_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I : Tm 0} {b : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hb : ∀ x ∉ L, (Γ.cons x A).JEqB levels H I (b.open x) (b.open x)) :
    Γ.JEqB levels H (Tm.arr A I) (.abs A b) (.abs A b) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.arrow_abstraction_of_hypotheses hh hn hΓ hA hI hb

theorem Ctx.JEqB.arrow_application_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I f a : Tm 0}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hf : Γ.JEqB levels H (.arr A I) f f) (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H I (.app f a) (.app f a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.arrow_application_of_hypotheses hh hn hΓ hA hI hf ha

theorem Ctx.JEqB.constantStep_typing_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels H I
        (((K.open x).open f).open r) (((K.open x).open f).open r)) :
    Γ.JEqB levels H (Tm.wStepType A B I.wk0)
      (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K)))
      (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constantStep_typing_of_hypotheses hh hn hΓ hA hI hB hK

theorem Ctx.JEqB.constantStep_first_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hh : HypothesisTransport levels H H) {Γ : Ctx} {A I a : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels H I
        (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels H A a a) :
    Γ.JEqB levels H
      (.arr (.arr (B.lst a) (.wtype A B)) (.arr (.arr (B.lst a) I) I))
      (.app (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) a)
      (.abs (.arr (B.lst a) (.wtype A B))
        (.abs ((Tm.arr (B.lst a) I).wk0) (K.lst a))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constantStep_first_beta_of_hypotheses hh hn hΓ hA hI hB hK ha

theorem Ctx.JEqB.arrow_abstraction {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I : Tm 0} {b : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hb : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ I (b.open x) (b.open x)) :
    Γ.JEqB levels ∅ (Tm.arr A I) (.abs A b) (.abs A b) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.arrow_abstraction hn hΓ hA hI hb

theorem Ctx.JEqB.arrow_application {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I f a : Tm 0}
    (hn : RuleBudget.Allows levels n) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hf : Γ.JEqB levels ∅ (.arr A I) f f) (ha : Γ.JEqB levels ∅ A a a) :
    Γ.JEqB levels ∅ I (.app f a) (.app f a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.arrow_application hn hΓ hA hI hf ha

theorem Ctx.JEqB.constantStep_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels ∅ I
        (((K.open x).open f).open r) (((K.open x).open f).open r)) :
    Γ.JEqB levels ∅ (Tm.wStepType A B I.wk0)
      (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K)))
      (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constantStep_typing hn hΓ hA hI hB hK

theorem Ctx.JEqB.constantStep_first_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels ∅ I
        (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels ∅ A a a) :
    Γ.JEqB levels ∅
      (.arr (.arr (B.lst a) (.wtype A B)) (.arr (.arr (B.lst a) I) I))
      (.app (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
        (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) a)
      (.abs (.arr (B.lst a) (.wtype A B))
        (.abs ((Tm.arr (B.lst a) I).wk0) (K.lst a))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constantStep_first_beta hn hΓ hA hI hB hK ha

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

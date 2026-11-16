module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.HeadComputation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Telescope
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.ConstantStepComputation

@[expose] public section

/-! Full application beta for arbitrary constant-motive W steps. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem Ctx.JEqB.constantStep_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} (hH : StructuralTheory levels H) {Γ : Ctx} {A I a f r : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A) (hI : Γ.JEqB levels H (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels H I
        (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f)
    (hr : Γ.JEqB levels H (.arr (B.lst a) I) r r) :
    Γ.JEqB levels H I
      (.app (.app (.app
        (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
          (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) a) f) r)
      (((K.lst a).lst f).lst r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constantStep_beta_of_hypotheses hH hn hΓ hA hI hB hK ha hf hr

theorem Ctx.JEqB.constantStep_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A I a f r : Tm 0} {B : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A) (hI : Γ.JEqB levels ∅ (.univ n) I I)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (Tm.arr (B.open x) (.wtype A B))).cons r
        (Tm.arr (B.open x) I)).JEqB levels ∅ I
        (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f)
    (hr : Γ.JEqB levels ∅ (.arr (B.lst a) I) r r) :
    Γ.JEqB levels ∅ I
      (.app (.app (.app
        (.abs A (.abs (Tm.arr B ((.wtype A B : Tm 0).castLE (by decide)))
          (.abs ((Tm.arr B (I.castLE (by decide))).wk0) K))) a) f) r)
      (((K.lst a).lst f).lst r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.constantStep_beta hn hΓ hA hI hB hK ha hf hr

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

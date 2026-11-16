module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.DependentStep
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.DependentRecChildren

@[expose] public section

/-! Actual recursive children for arbitrary dependent W motives, with application beta. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W


theorem Ctx.JEqB.recChildren_typing_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s : Tm 0} {B C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels H (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels H (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels H A a a) (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels H (.pi (B.lst a) (C.bsubst (fun _ => .app f.wk0 (.bv 0))))
      (Tm.recChildren A B C s a f) (Tm.recChildren A B C s a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.recChildren_typing_of_hypotheses hH hn hΓ hA hB hC hs ha hf

theorem Ctx.JEqB.recChildren_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s p : Tm 0} {B C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels H (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels H (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels H A a a) (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f)
    (hp : Γ.JEqB levels H (B.lst a) p p) :
    Γ.JEqB levels H (C.lst (.app f p))
      (.app (Tm.recChildren A B C s a f) p) (.wrec A B C s (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.recChildren_beta_of_hypotheses hH hn hΓ hA hB hC hs ha hf hp

theorem Ctx.JEqB.recChildren_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s : Tm 0} {B C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels ∅ (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels ∅ (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels ∅ A a a) (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels ∅ (.pi (B.lst a) (C.bsubst (fun _ => .app f.wk0 (.bv 0))))
      (Tm.recChildren A B C s a f) (Tm.recChildren A B C s a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.recChildren_typing hn hΓ hA hB hC hs ha hf

theorem Ctx.JEqB.recChildren_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s p : Tm 0} {B C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels ∅ (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels ∅ (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels ∅ A a a) (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f)
    (hp : Γ.JEqB levels ∅ (B.lst a) p p) :
    Γ.JEqB levels ∅ (C.lst (.app f p))
      (.app (Tm.recChildren A B C s a f) p) (.wrec A B C s (.app f p)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.recChildren_beta hn hΓ hA hB hC hs ha hf hp

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.ConstantStep
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Instantiation
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.DependentStepTyping

@[expose] public section

/-! Full dependent W steps synthesized from actual bodies and formed dependent recursive hypotheses. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W


theorem Ctx.JEqB.family_weaken_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ Δ : Ctx} {W : Tm 0} {C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels H .unit .star .star)
    (hW : Δ.JEqB levels H (.univ n) W W)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels H (.univ n) (C.open t) (C.open t)) :
    ∀ t ∉ L ∪ Δ.dv, (Δ.cons t W).JEqB levels H (.univ n) (C.open t) (C.open t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.family_weaken_of_hypotheses hH hn e hΔ hW hC

theorem Ctx.JEqB.family_instance_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ Δ : Ctx} {W t : Tm 0} {C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1))
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels H .unit .star .star)
    (hW : Δ.JEqB levels H (.univ n) W W)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels H (.univ n) (C.open t) (C.open t))
    (ht : Δ.JEqB levels H W t t) :
    Δ.JEqB levels H (.univ n) (C.lst t) (C.lst t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.family_instance_of_hypotheses hH hn e hΔ hW hC ht

theorem Ctx.JEqB.dependentIH_formation_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {W P f : Tm 0} {C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hW : Γ.JEqB levels H (.univ n) W W)
    (hP : Γ.JEqB levels H (.univ n) P P)
    (hf : Γ.JEqB levels H (.arr P W) f f)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels H (.univ n) (C.open t) (C.open t)) :
    Γ.JEqB levels H (.univ n)
      (.pi P (C.bsubst (fun _ => .app f.wk0 (.bv 0))))
      (.pi P (C.bsubst (fun _ => .app f.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.dependentIH_formation_of_hypotheses hH hn hΓ hW hP hf hC

theorem Ctx.JEqB.dependentStep_typing_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
    {K : Tm 3} {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels H (.univ n) (C.open t) (C.open t))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (.arr (B.open x) (.wtype A B))).cons r
        (.pi (B.open x) (C.bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))))).JEqB levels H
          (C.lst (.sup A B (.fv x) (.fv f)))
          (((K.open x).open f).open r) (((K.open x).open f).open r)) :
    Γ.JEqB levels H (Tm.wStepType A B C)
      (.abs A (.abs (.pi B ((Tm.wtype A B).castLE (Nat.zero_le 2)))
        (.abs (.pi (B.bsubst (fun _ => .bv 1)) (C.bsubst (fun _ => .app (.bv 1) (.bv 0)))) K)))
      (.abs A (.abs (.pi B ((Tm.wtype A B).castLE (Nat.zero_le 2)))
        (.abs (.pi (B.bsubst (fun _ => .bv 1)) (C.bsubst (fun _ => .app (.bv 1) (.bv 0)))) K))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.dependentStep_typing_of_hypotheses hH hn hΓ hA hB hC hK

theorem Ctx.JEqB.dependentStep_beta_of_hypotheses {H : Set Jdg} {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
    {K : Tm 3} {a f r : Tm 0} {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels H (.univ n) (C.open t) (C.open t))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (.arr (B.open x) (.wtype A B))).cons r
        (.pi (B.open x) (C.bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))))).JEqB levels H
          (C.lst (.sup A B (.fv x) (.fv f)))
          (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels H A a a)
    (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f)
    (hr : Γ.JEqB levels H (.pi (B.lst a) (C.bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels H (C.lst (.sup A B a f))
      (.app (.app (.app (.abs A (.abs (.pi B ((Tm.wtype A B).castLE (Nat.zero_le 2)))
        (.abs (.pi (B.bsubst (fun _ => .bv 1)) (C.bsubst (fun _ => .app (.bv 1) (.bv 0)))) K))) a) f) r)
      (((K.lst a).lst f).lst r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.dependentStep_beta_of_hypotheses hH hn hΓ hA hB hC hK ha hf hr

theorem Ctx.JEqB.family_weaken {levels : RuleBudget} {n : ℕ} {Γ Δ : Ctx} {W : Tm 0} {C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n)
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels ∅ .unit .star .star)
    (hW : Δ.JEqB levels ∅ (.univ n) W W)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels ∅ (.univ n) (C.open t) (C.open t)) :
    ∀ t ∉ L ∪ Δ.dv, (Δ.cons t W).JEqB levels ∅ (.univ n) (C.open t) (C.open t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.family_weaken hn e hΔ hW hC

theorem Ctx.JEqB.family_instance {levels : RuleBudget} {n : ℕ} {Γ Δ : Ctx} {W t : Tm 0} {C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels ∅ .unit .star .star)
    (hW : Δ.JEqB levels ∅ (.univ n) W W)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels ∅ (.univ n) (C.open t) (C.open t))
    (ht : Δ.JEqB levels ∅ W t t) :
    Δ.JEqB levels ∅ (.univ n) (C.lst t) (C.lst t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.family_instance hn e hΔ hW hC ht

theorem Ctx.JEqB.dependentIH_formation {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {W P f : Tm 0} {C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hW : Γ.JEqB levels ∅ (.univ n) W W)
    (hP : Γ.JEqB levels ∅ (.univ n) P P)
    (hf : Γ.JEqB levels ∅ (.arr P W) f f)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels ∅ (.univ n) (C.open t) (C.open t)) :
    Γ.JEqB levels ∅ (.univ n)
      (.pi P (C.bsubst (fun _ => .app f.wk0 (.bv 0))))
      (.pi P (C.bsubst (fun _ => .app f.wk0 (.bv 0)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.dependentIH_formation hn hΓ hW hP hf hC

theorem Ctx.JEqB.dependentStep_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
    {K : Tm 3} {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels ∅ (.univ n) (C.open t) (C.open t))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (.arr (B.open x) (.wtype A B))).cons r
        (.pi (B.open x) (C.bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))))).JEqB levels ∅
          (C.lst (.sup A B (.fv x) (.fv f)))
          (((K.open x).open f).open r) (((K.open x).open f).open r)) :
    Γ.JEqB levels ∅ (Tm.wStepType A B C)
      (.abs A (.abs (.pi B ((Tm.wtype A B).castLE (Nat.zero_le 2)))
        (.abs (.pi (B.bsubst (fun _ => .bv 1)) (C.bsubst (fun _ => .app (.bv 1) (.bv 0)))) K)))
      (.abs A (.abs (.pi B ((Tm.wtype A B).castLE (Nat.zero_le 2)))
        (.abs (.pi (B.bsubst (fun _ => .bv 1)) (C.bsubst (fun _ => .app (.bv 1) (.bv 0)))) K))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.dependentStep_typing hn hΓ hA hB hC hK

theorem Ctx.JEqB.dependentStep_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
    {K : Tm 3} {a f r : Tm 0} {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels ∅ (.univ n) (C.open t) (C.open t))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (.arr (B.open x) (.wtype A B))).cons r
        (.pi (B.open x) (C.bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))))).JEqB levels ∅
          (C.lst (.sup A B (.fv x) (.fv f)))
          (((K.open x).open f).open r) (((K.open x).open f).open r))
    (ha : Γ.JEqB levels ∅ A a a)
    (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f)
    (hr : Γ.JEqB levels ∅ (.pi (B.lst a) (C.bsubst (fun _ => .app f.wk0 (.bv 0)))) r r) :
    Γ.JEqB levels ∅ (C.lst (.sup A B a f))
      (.app (.app (.app (.abs A (.abs (.pi B ((Tm.wtype A B).castLE (Nat.zero_le 2)))
        (.abs (.pi (B.bsubst (fun _ => .bv 1)) (C.bsubst (fun _ => .app (.bv 1) (.bv 0)))) K))) a) f) r)
      (((K.lst a).lst f).lst r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.dependentStep_beta hn hΓ hA hB hC hK ha hf hr

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

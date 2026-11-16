module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.DependentStep

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg}

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem singleton_lst (C : Tm 1) (a : Tm 0) : C.lst a = C.bsubst (fun _ => a) := by
  rw [Tm.lst_eq_bsubst]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact Tm.castLE_refl a

private theorem wkn_one_open (B : Tm 1) (p : String) : (B.wkn 1).open p = B := by
  rw [Tm.wkn_past B 1 (Nat.le_refl 1)]
  simpa only [Tm.castLE_refl] using Tm.open_castLE B (Nat.le_refl 1) p

private theorem wkn_one_lst (B : Tm 1) (p : Tm 0) : (B.wkn 1).lst p = B := by
  rw [Tm.wkn_past B 1 (Nat.le_refl 1)]
  simpa only [Tm.castLE_refl] using Tm.lst_castLE B (Nat.le_refl 1) p

private theorem childFamily_lst (C : Tm 1) (f p : Tm 0) :
    (C.bsubst (fun _ => .app f.wk0 (.bv 0))).lst p = C.lst (.app f p) := by
  rw [Tm.lst_bsubst]
  conv_rhs => rw [singleton_lst]
  congr 1
  funext i
  simp only [Tm.lst, Tm.closed_wk0_lst, lastCases_zero, Tm.castLE_refl]

private theorem recChildren_data_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s : Tm 0} {B C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels H (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels H (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels H A a a) (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) ∧
    ∀ p ∉ Γ.dv, (Γ.cons p (B.lst a)).JEqB levels H (.univ n)
      ((C.bsubst (fun _ => .app f.wk0 (.bv 0))).open p)
      ((C.bsubst (fun _ => .app f.wk0 (.bv 0))).open p) ∧
    (Γ.cons p (B.lst a)).JEqB levels H
      ((C.bsubst (fun _ => .app f.wk0 (.bv 0))).open p)
      ((.wrec A.wk0 (B.wkn 1) (C.wkn 1) s.wk0 (.app f.wk0 (.bv 0)) : Tm 1).open p)
      ((.wrec A.wk0 (B.wkn 1) (C.wkn 1) s.wk0 (.app f.wk0 (.bv 0)) : Tm 1).open p) := by
  have hn' : RuleBudget.Allows levels n := by budget_omega
  have hP : Γ.JEqB levels H (.univ n) (B.lst a) (B.lst a) :=
    Ctx.JEqB.instantiate_type hn hΓ hA hB ha
  have hW : Γ.JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := .wtype hn' hA hB
  refine ⟨hP, ?_⟩
  intro p hp
  have hctx : (Γ.cons p (B.lst a)).JEqB levels H .unit .star .star := .cons_ok hn' hΓ hp hP
  have e : Γ.LookupLE (Γ.cons p (B.lst a)) := Ctx.LookupLE.fresh_cons hp (B.lst a)
  have hA' : (Γ.cons p (B.lst a)).JEqB levels H (.univ n) A A := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hp hn' hP hA
  have hW' : (Γ.cons p (B.lst a)).JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hp hn' hP hW
  have hP' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hp hn' hP hP
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hp hn' hP hf
  have hs' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hp hn' hP hs
  have hp' : (Γ.cons p (B.lst a)).JEqB levels H (B.lst a) (.fv p) (.fv p) := .var hctx (.here ..)
  have hfb := Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn' hctx hP' hW' hf' hp'
  have htype := Ctx.JEqB.family_instance_of_hypotheses hH hn e hctx hW' hC hfb
  have hterm := Ctx.JEqB.wrec hn' hn' hA'
    (Ctx.JEqB.family_weaken_of_hypotheses hH hn' e hctx hA' hB)
    (Ctx.JEqB.family_weaken_of_hypotheses hH hn' e hctx hW' hC) hs' hfb
  simpa only [Tm.open_bsubst, Tm.open, Tm.closed_wk0_open, singleton_lst,
    wkn_one_open, lastCases_zero] using And.intro htype hterm

theorem recChildren_typing_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s : Tm 0} {B C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels H (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels H (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels H A a a) (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels H (.pi (B.lst a) (C.bsubst (fun _ => .app f.wk0 (.bv 0))))
      (Tm.recChildren A B C s a f) (Tm.recChildren A B C s a f) := by
  have hdata := recChildren_data_of_hypotheses hH hn hΓ hA hB hC hs ha hf
  exact .abs (by budget_omega) hdata.1 (fun p hp => (hdata.2 p hp).1) (fun p hp => (hdata.2 p hp).2)

theorem recChildren_beta_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s p : Tm 0} {B C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels H (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels H (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels H A a a) (hf : Γ.JEqB levels H (.arr (B.lst a) (.wtype A B)) f f)
    (hp : Γ.JEqB levels H (B.lst a) p p) :
    Γ.JEqB levels H (C.lst (.app f p))
      (.app (Tm.recChildren A B C s a f) p) (.wrec A B C s (.app f p)) := by
  have hdata := recChildren_data_of_hypotheses hH hn hΓ hA hB hC hs ha hf
  simpa only [Tm.recChildren, childFamily_lst, Tm.lst, Tm.closed_wk0_lst,
    wkn_one_lst, lastCases_zero, Tm.castLE_refl] using
    Ctx.JEqB.beta_app (by budget_omega) hdata.1 (fun p hp => (hdata.2 p hp).1) (fun p hp => (hdata.2 p hp).2) hp


theorem recChildren_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s : Tm 0} {B C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels ∅ (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels ∅ (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels ∅ A a a) (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f) :
    Γ.JEqB levels ∅ (.pi (B.lst a) (C.bsubst (fun _ => .app f.wk0 (.bv 0))))
      (Tm.recChildren A B C s a f) (Tm.recChildren A B C s a f) :=
  recChildren_typing_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hB hC hs ha hf

theorem recChildren_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A a f s p : Tm 0} {B C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1)) (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hA : Γ.JEqB levels ∅ (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels ∅ (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels ∅ (.univ n) (C.open t) (C.open t))
    (hs : Γ.JEqB levels ∅ (Tm.wStepType A B C) s s)
    (ha : Γ.JEqB levels ∅ A a a) (hf : Γ.JEqB levels ∅ (.arr (B.lst a) (.wtype A B)) f f)
    (hp : Γ.JEqB levels ∅ (B.lst a) p p) :
    Γ.JEqB levels ∅ (C.lst (.app f p))
      (.app (Tm.recChildren A B C s a f) p) (.wrec A B C s (.app f p)) :=
  recChildren_beta_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hB hC hs ha hf hp

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

module
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.ConstantStep
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Instantiation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.DependentTelescope
@[expose] public section
namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg}

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lastCases_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

private theorem lastCases_two {α : Sort _} (a : α) (f : Fin 2 → α) :
    Fin.lastCases a f (2 : Fin 3) = a := Fin.lastCases_last

private theorem lastCases_zero_two {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (0 : Fin 2) = f 0 := by
  exact Fin.lastCases_castSucc (0 : Fin 1)

private theorem lastCases_one_three {α : Sort _} (a : α) (f : Fin 2 → α) :
    Fin.lastCases a f (1 : Fin 3) = f 1 := by
  exact Fin.lastCases_castSucc (1 : Fin 2)

private theorem lastCases_zero_three {α : Sort _} (a : α) (f : Fin 2 → α) :
    Fin.lastCases a f (0 : Fin 3) = f 0 := by
  exact Fin.lastCases_castSucc (0 : Fin 2)

private theorem lst_fv {k : ℕ} (t : Tm (k + 1)) (x : String) :
    t.lst (.fv x) = t.open x := by
  rw [Tm.lst_eq_bsubst, Tm.open_eq_bsubst]
  rfl

private theorem singleton_lst (C : Tm 1) (a : Tm 0) :
    C.lst a = C.bsubst (fun _ => a) := by
  rw [Tm.lst_eq_bsubst]
  congr 1
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact Tm.castLE_refl a

theorem family_weaken_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ Δ : Ctx} {W : Tm 0} {C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels n)
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels H .unit .star .star)
    (hW : Δ.JEqB levels H (.univ n) W W)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels H (.univ n) (C.open t) (C.open t)) :
    ∀ t ∉ L ∪ Δ.dv, (Δ.cons t W).JEqB levels H (.univ n) (C.open t) (C.open t) := by
  intro t ht
  exact Ctx.JEqB.weaken_of_hypotheses hH.weakening (hC t (fun h => ht (Finset.mem_union_left _ h))) (e.cons t W)
    (.cons_ok hn hΔ (fun h => ht (Finset.mem_union_right _ h)) hW)

theorem family_instance_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ Δ : Ctx} {W t : Tm 0} {C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1))
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels H .unit .star .star)
    (hW : Δ.JEqB levels H (.univ n) W W)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels H (.univ n) (C.open t) (C.open t))
    (ht : Δ.JEqB levels H W t t) :
    Δ.JEqB levels H (.univ n) (C.lst t) (C.lst t) :=
  Ctx.JEqB.instantiate_type hn hΔ hW (family_weaken_of_hypotheses hH (by budget_omega) e hΔ hW hC) ht

theorem dependentIH_formation_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {W P f : Tm 0} {C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hW : Γ.JEqB levels H (.univ n) W W)
    (hP : Γ.JEqB levels H (.univ n) P P)
    (hf : Γ.JEqB levels H (.arr P W) f f)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels H (.univ n) (C.open t) (C.open t)) :
    Γ.JEqB levels H (.univ n)
      (.pi P (C.bsubst (fun _ => .app f.wk0 (.bv 0))))
      (.pi P (C.bsubst (fun _ => .app f.wk0 (.bv 0)))) := by
  have hn' : RuleBudget.Allows levels n := by budget_omega
  apply Ctx.JEqB.pi (L := Γ.dv) hn' hP
  intro b hb
  have hctx : (Γ.cons b P).JEqB levels H .unit .star .star := .cons_ok hn' hΓ hb hP
  have hW' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hb hn' hP hW
  have hP' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hb hn' hP hP
  have hf' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hb hn' hP hf
  have hb' : (Γ.cons b P).JEqB levels H P (.fv b) (.fv b) := .var hctx (.here ..)
  have hfb := Ctx.JEqB.arrow_application_of_hypotheses hH.weakening hn' hctx hP' hW' hf' hb'
  have h := family_instance_of_hypotheses hH hn (Ctx.LookupLE.fresh_cons hb P) hctx hW' hC hfb
  simpa only [Tm.open_bsubst, Tm.open, Tm.closed_wk0_open, singleton_lst,
    lastCases_zero] using h

private def stepF (A : Tm 0) (B : Tm 1) : Tm 1 :=
  .pi B ((Tm.wtype A B).castLE (by decide))

private def stepR (B C : Tm 1) : Tm 2 :=
  .pi (B.bsubst (fun _ => .bv 1)) (C.bsubst (fun _ => .app (.bv 1) (.bv 0)))

private def stepD (A : Tm 0) (B C : Tm 1) : Tm 3 :=
  C.bsubst (fun _ => .sup (A.castLE (by decide)) (B.castLE (by decide)) (.bv 2) (.bv 1))

private theorem stepF_open (A : Tm 0) (B : Tm 1) (x : String) :
    (stepF A B).open x = .arr (B.open x) (.wtype A B) := by
  simp only [stepF, Tm.open, Tm.closed_castLE_open, Tm.arr, Tm.wk0,
    Tm.wkn_past _ 0 (Nat.zero_le _)]

private theorem stepR_open (B C : Tm 1) (x f : String) :
    ((stepR B C).open x).open f =
      .pi (B.open x) (C.bsubst (fun _ => .app (Tm.fv f).wk0 (.bv 0))) := by
  simp only [stepR, Tm.open, Tm.open_bsubst, Tm.wk0, Tm.wkn]
  congr 1
  · rw [Tm.open_eq_bsubst B x]
    congr 1
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [lastCases_one, Tm.open, lastCases_zero]
  · congr 1
    funext i
    simp only [lastCases_one_three, lastCases_zero_three, lastCases_one, lastCases_zero_two, Tm.open]

private theorem stepD_open (A : Tm 0) (B C : Tm 1) (x f r : String) :
    (((stepD A B C).open x).open f).open r =
      C.lst (.sup A B (.fv x) (.fv f)) := by
  have hB : (((B.castLE (by decide : 1 ≤ 4)).open x).open f).open r = B := by
    rw [Tm.open_castLE B (by decide : 1 ≤ 3), Tm.open_castLE B (by decide : 1 ≤ 2),
      Tm.open_castLE B (by decide : 1 ≤ 1), Tm.castLE_refl]
  simp only [stepD, Tm.open_bsubst, Tm.open, Tm.closed_castLE_open,
    Tm.castLE_refl, singleton_lst, hB]
  congr 1
  funext i
  simp only [lastCases_two, lastCases_one_three, lastCases_one, Tm.open]

private theorem tripleAbstraction {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    {A : Tm 0} {B : Tm 1} {C : Tm 2} {D K : Tm 3} {L : Finset String}
    (hn : RuleBudget.Allows levels n) (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, ∀ f ∉ insert x L,
      ((Γ.cons x A).cons f (B.open x)).JEqB levels H (.univ n)
        ((C.open x).open f) ((C.open x).open f))
    (hD : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (B.open x)).cons r ((C.open x).open f)).JEqB levels H (.univ n)
        (((D.open x).open f).open r) (((D.open x).open f).open r))
    (hK : ∀ x ∉ L, ∀ f ∉ insert x L, ∀ r ∉ insert f (insert x L),
      (((Γ.cons x A).cons f (B.open x)).cons r ((C.open x).open f)).JEqB levels H
        (((D.open x).open f).open r) (((K.open x).open f).open r) (((K.open x).open f).open r)) :
    Γ.JEqB levels H (.pi A (.pi B (.pi C D)))
      (.abs A (.abs B (.abs C K))) (.abs A (.abs B (.abs C K))) := by
  have hTail : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n)
      ((.pi B (.pi C D) : Tm 1).open x) ((.pi B (.pi C D) : Tm 1).open x) := by
    intro x hx
    simp only [Tm.open]
    apply Ctx.JEqB.pi (L := insert x L) hn (hB x hx)
    intro f hf
    simp only [Tm.open]
    exact Ctx.JEqB.pi (L := insert f (insert x L)) hn (hC x hx f hf) (hD x hx f hf)
  apply Ctx.JEqB.abs hn hA hTail
  intro x hx
  simp only [Tm.open]
  apply Ctx.JEqB.abs (L := insert x L) hn (hB x hx)
  · intro f hf
    simp only [Tm.open]
    exact Ctx.JEqB.pi (L := insert f (insert x L)) hn (hC x hx f hf) (hD x hx f hf)
  · intro f hf
    simp only [Tm.open]
    exact Ctx.JEqB.abs (L := insert f (insert x L)) hn (hC x hx f hf) (hD x hx f hf) (hK x hx f hf)

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg}

private theorem dependentStep_data_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
    {L : Finset String} (hH : StructuralTheory levels H) (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels H .unit .star .star)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hC : ∀ t ∉ L, (Γ.cons t (.wtype A B)).JEqB levels H (.univ n) (C.open t) (C.open t)) :
    (∀ x ∉ L ∪ Γ.dv, (Γ.cons x A).JEqB levels H (.univ n)
      ((stepF A B).open x) ((stepF A B).open x)) ∧
    (∀ x ∉ L ∪ Γ.dv, ∀ f ∉ insert x (L ∪ Γ.dv),
      ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H .unit .star .star ∧
      ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H (.univ n)
        (((stepR B C).open x).open f) (((stepR B C).open x).open f) ∧
      ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H (.univ n)
        (C.lst (.sup A B (.fv x) (.fv f))) (C.lst (.sup A B (.fv x) (.fv f)))) := by
  have hn' : RuleBudget.Allows levels n := by budget_omega
  let N := L ∪ Γ.dv
  have hW : Γ.JEqB levels H (.univ n) (.wtype A B) (.wtype A B) := .wtype hn' hA hB
  have hF : ∀ x ∉ N, (Γ.cons x A).JEqB levels H (.univ n)
      ((stepF A B).open x) ((stepF A B).open x) := by
    intro x hx
    have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
    have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hctx := Ctx.JEqB.cons_ok hn' hΓ hxΓ hA
    rw [stepF_open]
    exact Ctx.JEqB.arrow_formation_of_hypotheses hH.weakening hn' hctx (hB x hxL) (Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hΓ hxΓ hn' hA hW)
  have hlocal : ∀ x ∉ N, ∀ f ∉ insert x N,
      ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H .unit .star .star ∧
      ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H (.univ n)
        (((stepR B C).open x).open f) (((stepR B C).open x).open f) ∧
      ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H (.univ n)
        (C.lst (.sup A B (.fv x) (.fv f))) (C.lst (.sup A B (.fv x) (.fv f))) := by
    intro x hx f hf
    have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
    have hxΓ : x ∉ Γ.dv := fun h => hx (Finset.mem_union_right _ h)
    have hfParts : f ≠ x ∧ f ∉ L ∧ f ∉ Γ.dv := by
      simpa only [N, Finset.mem_insert, Finset.mem_union, not_or] using hf
    have hfΓ : f ∉ (Γ.cons x A).dv := by
      simpa only [Ctx.dv, Finset.mem_insert, not_or] using And.intro hfParts.1 hfParts.2.2
    have hctxA := Ctx.JEqB.cons_ok hn' hΓ hxΓ hA
    have hctxF := Ctx.JEqB.cons_ok hn' hctxA hfΓ (hF x hx)
    have eA : Γ.LookupLE (Γ.cons x A) := Ctx.LookupLE.fresh_cons hxΓ A
    have eF : Γ.LookupLE ((Γ.cons x A).cons f ((stepF A B).open x)) :=
      eA.trans (Ctx.LookupLE.fresh_cons hfΓ ((stepF A B).open x))
    have hWF := Ctx.JEqB.weaken_of_hypotheses hH.weakening hW eF hctxF
    have hAF := Ctx.JEqB.weaken_of_hypotheses hH.weakening hA eF hctxF
    have hBF := Ctx.JEqB.weaken_of_hypotheses hH.weakening (hB x hxL) (Ctx.LookupLE.fresh_cons hfΓ _) hctxF
    have hfVar : ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H
        (.arr (B.open x) (.wtype A B)) (.fv f) (.fv f) := by
      rw [← stepF_open]
      exact .var hctxF (.here ..)
    have hCF := family_weaken_of_hypotheses hH hn' eF hctxF hWF hC
    have hR := dependentIH_formation_of_hypotheses hH hn hctxF hWF hBF hfVar hCF
    have hRF : ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H (.univ n)
        (((stepR B C).open x).open f) (((stepR B C).open x).open f) := by
      simpa only [stepR_open] using hR
    have hxVar : (Γ.cons x A).JEqB levels H A (.fv x) (.fv x) := .var hctxA (.here ..)
    have hxF := Ctx.JEqB.weaken_of_hypotheses hH.weakening hxVar (Ctx.LookupLE.fresh_cons hfΓ _) hctxF
    have hfSup : ((Γ.cons x A).cons f ((stepF A B).open x)).JEqB levels H
        (.arr (B.lst (.fv x)) (.wtype A B)) (.fv f) (.fv f) := by
      simpa only [lst_fv] using hfVar
    have hSup := Ctx.JEqB.sup hn' hAF (family_weaken_of_hypotheses hH hn' eF hctxF hAF hB) hxF hfSup
    have hD := family_instance_of_hypotheses hH hn eF hctxF hWF hC hSup
    exact ⟨hctxF, hRF, hD⟩
  exact ⟨hF, hlocal⟩

theorem dependentStep_typing_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
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
        (.abs (.pi (B.bsubst (fun _ => .bv 1)) (C.bsubst (fun _ => .app (.bv 1) (.bv 0)))) K))) := by
  have hn' : RuleBudget.Allows levels n := by budget_omega
  let N := L ∪ Γ.dv
  obtain ⟨hF, hlocal⟩ := dependentStep_data_of_hypotheses hH hn hΓ hA hB hC
  change Γ.JEqB levels H (.pi A (.pi (stepF A B) (.pi (stepR B C) (stepD A B C)))) _ _
  apply tripleAbstraction (L := N) (C := stepR B C) (D := stepD A B C) hn' hA hF
  · intro x hx f hf
    exact (hlocal x hx f hf).2.1
  · intro x hx f hf r hr
    have hrΓ : r ∉ ((Γ.cons x A).cons f ((stepF A B).open x)).dv := by
      simp only [Ctx.dv, Finset.mem_insert, not_or] at hr ⊢
      exact ⟨hr.1, hr.2.1, fun h => hr.2.2 (Finset.mem_union_right _ h)⟩
    rw [stepD_open]
    exact Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening (hlocal x hx f hf).1 hrΓ hn' (hlocal x hx f hf).2.1 (hlocal x hx f hf).2.2
  · show ∀ x ∉ N, ∀ f ∉ insert x N, ∀ r ∉ insert f (insert x N),
      (((Γ.cons x A).cons f ((stepF A B).open x)).cons r
      (((stepR B C).open x).open f)).JEqB levels H
        (((stepD A B C).open x).open f |>.open r)
        (((K.open x).open f).open r) (((K.open x).open f).open r)
    intro x hx f hf r hr
    have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
    have hfL : f ∉ insert x L := fun h => hf (Finset.mem_insert.mpr ((Finset.mem_insert.mp h).elim Or.inl (fun q => Or.inr (Finset.mem_union_left _ q))))
    have hrL : r ∉ insert f (insert x L) := by
      intro h
      apply hr
      simpa only [Finset.mem_insert, Finset.mem_union, N] using
        ((Finset.mem_insert.mp h).elim Or.inl (fun q =>
          Or.inr ((Finset.mem_insert.mp q).elim Or.inl (fun z => Or.inr (Or.inl z)))))
    simpa only [stepF_open, stepR_open, stepD_open] using hK x hxL f hfL r hrL

private theorem stepF_lst (A a : Tm 0) (B : Tm 1) :
    (stepF A B).lst a = .arr (B.lst a) (.wtype A B) := by
  simp only [stepF, Tm.lst, Tm.closed_castLE_lst, Tm.arr, Tm.wk0,
    Tm.wkn_past _ 0 (Nat.zero_le _)]

private theorem stepR_lst (B C : Tm 1) (a f : Tm 0) :
    ((stepR B C).lst a).lst f =
      .pi (B.lst a) (C.bsubst (fun _ => .app f.wk0 (.bv 0))) := by
  simp only [stepR, Tm.lst, Tm.lst_bsubst]
  congr 1
  · rw [Tm.lst_eq_bsubst B a]
    congr 1
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp only [lastCases_one, Tm.closed_castLE_lst, Tm.castLE_refl, lastCases_zero]
  · congr 1
    funext i
    simp only [lastCases_one_three, lastCases_zero_three, lastCases_one, lastCases_zero_two,
      Tm.lst, Tm.wk0, Tm.wkn_past f 0 (Nat.zero_le _)]

private theorem stepD_lst (A : Tm 0) (B C : Tm 1) (a f r : Tm 0) :
    (((stepD A B C).lst a).lst f).lst r = C.lst (.sup A B a f) := by
  have hB : (((B.castLE (by decide : 1 ≤ 4)).lst a).lst f).lst r = B := by
    rw [Tm.lst_castLE B (by decide : 1 ≤ 3), Tm.lst_castLE B (by decide : 1 ≤ 2),
      Tm.lst_castLE B (by decide : 1 ≤ 1), Tm.castLE_refl]
  rw [stepD, Tm.lst_bsubst, Tm.lst_bsubst, Tm.lst_bsubst,
    singleton_lst C (.sup A B a f)]
  congr 1
  funext i
  simp only [Tm.lst, lastCases_two, lastCases_one_three, lastCases_one,
    Tm.closed_castLE_lst, Tm.castLE_refl, hB]


theorem dependentStep_beta_of_hypotheses {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
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
      (((K.lst a).lst f).lst r) := by
  have hn' : RuleBudget.Allows levels n := by budget_omega
  let N := L ∪ Γ.dv
  obtain ⟨hF, hlocal⟩ := dependentStep_data_of_hypotheses hH hn hΓ hA hB hC
  have hf' : Γ.JEqB levels H ((stepF A B).lst a) f f := by
    simpa only [stepF_lst] using hf
  have hr' : Γ.JEqB levels H (((stepR B C).lst a).lst f) r r := by
    simpa only [stepR_lst] using hr
  have hbeta : Γ.JEqB levels H (((stepD A B C).lst a).lst f |>.lst r)
      (.app (.app (.app (.abs A (.abs (stepF A B) (.abs (stepR B C) K))) a) f) r)
      (((K.lst a).lst f).lst r) := by
    refine Ctx.JEqB.tripleAbstraction_beta_of_hypotheses hH (L := N) (C := stepR B C)
      (D := stepD A B C) hn' hΓ hA hF ?_ ?_ ?_ ha hf' hr'

    · intro x hx f hf
      exact (hlocal x hx f hf).2.1
    · intro x hx f hf r hr
      have hrΓ : r ∉ ((Γ.cons x A).cons f ((stepF A B).open x)).dv := by
        simp only [Ctx.dv, Finset.mem_insert, not_or] at hr ⊢
        exact ⟨hr.1, hr.2.1, fun h => hr.2.2 (Finset.mem_union_right _ h)⟩
      rw [stepD_open]
      exact Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening (hlocal x hx f hf).1 hrΓ hn' (hlocal x hx f hf).2.1 (hlocal x hx f hf).2.2
    · show ∀ x ∉ N, ∀ f ∉ insert x N, ∀ r ∉ insert f (insert x N),
        (((Γ.cons x A).cons f ((stepF A B).open x)).cons r
          (((stepR B C).open x).open f)).JEqB levels H
            (((stepD A B C).open x).open f |>.open r)
            (((K.open x).open f).open r) (((K.open x).open f).open r)
      intro x hx f hf r hr
      have hxL : x ∉ L := fun h => hx (Finset.mem_union_left _ h)
      have hfL : f ∉ insert x L := fun h => hf (Finset.mem_insert.mpr ((Finset.mem_insert.mp h).elim Or.inl (fun q => Or.inr (Finset.mem_union_left _ q))))
      have hrL : r ∉ insert f (insert x L) := by
        intro h
        apply hr
        simpa only [Finset.mem_insert, Finset.mem_union, N] using
          ((Finset.mem_insert.mp h).elim Or.inl (fun q =>
            Or.inr ((Finset.mem_insert.mp q).elim Or.inl (fun z => Or.inr (Or.inl z)))))
      simpa only [stepF_open, stepR_open, stepD_open] using hK x hxL f hfL r hrL

  simpa only [stepD_lst, stepF, stepR] using hbeta



theorem family_weaken {levels : RuleBudget} {n : ℕ} {Γ Δ : Ctx} {W : Tm 0} {C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n)
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels ∅ .unit .star .star)
    (hW : Δ.JEqB levels ∅ (.univ n) W W)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels ∅ (.univ n) (C.open t) (C.open t)) :
    ∀ t ∉ L ∪ Δ.dv, (Δ.cons t W).JEqB levels ∅ (.univ n) (C.open t) (C.open t) :=
  family_weaken_of_hypotheses (StructuralTheory.empty levels) hn e hΔ hW hC

theorem family_instance {levels : RuleBudget} {n : ℕ} {Γ Δ : Ctx} {W t : Tm 0} {C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels ∅ .unit .star .star)
    (hW : Δ.JEqB levels ∅ (.univ n) W W)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels ∅ (.univ n) (C.open t) (C.open t))
    (ht : Δ.JEqB levels ∅ W t t) :
    Δ.JEqB levels ∅ (.univ n) (C.lst t) (C.lst t) :=
  family_instance_of_hypotheses (StructuralTheory.empty levels) hn e hΔ hW hC ht

theorem dependentIH_formation {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {W P f : Tm 0} {C : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels (n + 1))
    (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hW : Γ.JEqB levels ∅ (.univ n) W W)
    (hP : Γ.JEqB levels ∅ (.univ n) P P)
    (hf : Γ.JEqB levels ∅ (.arr P W) f f)
    (hC : ∀ t ∉ L, (Γ.cons t W).JEqB levels ∅ (.univ n) (C.open t) (C.open t)) :
    Γ.JEqB levels ∅ (.univ n)
      (.pi P (C.bsubst (fun _ => .app f.wk0 (.bv 0))))
      (.pi P (C.bsubst (fun _ => .app f.wk0 (.bv 0)))) :=
  dependentIH_formation_of_hypotheses (StructuralTheory.empty levels) hn hΓ hW hP hf hC

theorem dependentStep_typing {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
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
  dependentStep_typing_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hB hC hK

theorem dependentStep_beta {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {A : Tm 0} {B C : Tm 1}
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
  dependentStep_beta_of_hypotheses (StructuralTheory.empty levels) hn hΓ hA hB hC hK ha hf hr

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

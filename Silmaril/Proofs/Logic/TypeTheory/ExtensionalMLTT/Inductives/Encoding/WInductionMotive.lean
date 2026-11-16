module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem lastCases_one {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (1 : Fin 2) = a := Fin.lastCases_last

private theorem lastCases_first {α : Sort _} (a : α) (f : Fin 1 → α) :
    Fin.lastCases a f (0 : Fin 2) = f 0 := Fin.lastCases_castSucc 0

theorem canonical_open {k : ℕ} (S : Description) (t c : Tm (k + 1)) (x : String) :
    (S.canonical t c).open x = S.canonical (t.open x) (c.open x) := by
  simp only [Description.canonical, Tm.open, root_open]

theorem canonical_lst {k : ℕ} (S : Description) (t c : Tm (k + 1)) (a : Tm 0) :
    (S.canonical t c).lst a = S.canonical (t.lst a) (c.lst a) := by
  simp only [Description.canonical, Tm.lst, root_lst]

/-- Original fibre introduction from an actual raw tree and actual recursive coherence. -/
theorem canonical_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {t c : Tm 0}
    (ht : Γ.JEqB levels H S.raw t t) (hc : Γ.JEqB levels H (S.coherence n t) c c) :
    Γ.JEqB levels H (S.fibre n (S.root t)) (S.canonical t c) (S.canonical t c) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hr : Γ.JEqB levels H S.index (S.root t) (S.root t) := root_typing_of_hypotheses hH D.toFormationData ht
  have hE : Γ.JEqB levels H (.univ n)
      (.id S.index (S.root t) (S.root t)) (.id S.index (S.root t) (S.root t)) :=
    .id hn D.index hr hr
  have hcoh : Γ.JEqB levels H (.univ n) (S.coherence n t) (S.coherence n t) := coherence_formation_of_hypotheses hH D ht
  have htail : Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) (S.root t).wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst t)
      (.pair (.refl (S.root t)) c) (.pair (.refl (S.root t)) c) := by
    rw [fibreTail_lst]
    exact .pair hn hE (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh) (.refl hr)
      (by simpa only [Tm.closed_wk0_lst] using hc)
  exact .pair hn (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hr) ht htail

private theorem motive_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H)
    (hm : RuleBudget.Allows levels (m + 1)) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.index).JEqB levels H (.univ (max n (m + 1)))
      ((.pi (S.fibreAt n (.bv 0)) (.univ m) : Tm 1).open x)
      ((.pi (S.fibreAt n (.bv 0)) (.univ m) : Tm 1).open x) := by
  intro x hx
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hk : RuleBudget.Allows levels (max n (m + 1)) := RuleBudget.Allows.max hn hm
  have hctx : (Γ.cons x S.index).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hx D.index
  have dx := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hx S.index) hctx
  have hi : (Γ.cons x S.index).JEqB levels H S.index (.fv x) (.fv x) :=
    .var hctx (.here Γ x S.index)
  have hF : (Γ.cons x S.index).JEqB levels H (.univ n)
      (S.fibre n (.fv x)) (S.fibre n (.fv x)) := fibre_formation_of_hypotheses hH dx hi
  have hU : ∀ y ∉ (Γ.cons x S.index).dv,
      ((Γ.cons x S.index).cons y (S.fibre n (.fv x))).JEqB levels H (.univ (max n (m + 1)))
        ((.univ m : Tm 1).open y) ((.univ m : Tm 1).open y) := by
    intro y hy
    simpa only [Tm.open] using Ctx.JEqB.cumul hk (Nat.le_max_right n (m + 1))
      (Ctx.JEqB.univ hm (Ctx.JEqB.cons_ok hn hctx hy hF))
  simpa only [Tm.open, fibreAt_open, lastCases_zero, fibreAt_closed] using
    Ctx.JEqB.pi hk (Ctx.JEqB.cumul hk (Nat.le_max_left n (m + 1)) hF) hU

/-- Motive application respects actual indexed arguments and arbitrary original fibre values. -/
theorem motive_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i j t u : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hij : Γ.JEqB levels H S.index i j) (htu : Γ.JEqB levels H (S.fibre n i) t u) :
    Γ.JEqB levels H (.univ m) (.app (.app C i) t) (.app (.app C j) u) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hk : RuleBudget.Allows levels (max n (m + 1)) := RuleBudget.Allows.max hn hm
  have hi := hij.trans hij.symm
  have hfirst : Γ.JEqB levels H (.pi (S.fibre n i) (.univ m)) (.app C i) (.app C j) := by
    simpa only [Tm.lst, fibreAt_lst, Tm.castLE_refl, fibreAt_closed, lastCases_zero] using Ctx.JEqB.app hk
      (Ctx.JEqB.cumul hk (Nat.le_max_left n (m + 1)) D.index) (motive_codomain_of_hypotheses hH D hm) hC hij
  have hF : Γ.JEqB levels H (.univ n) (S.fibre n i) (S.fibre n i) := fibre_formation_of_hypotheses hH D hi
  have hU : ∀ x ∉ Γ.dv, (Γ.cons x (S.fibre n i)).JEqB levels H (.univ (max n (m + 1)))
      ((.univ m : Tm 1).open x) ((.univ m : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.cumul hk (Nat.le_max_right n (m + 1))
      (Ctx.JEqB.univ hm (Ctx.JEqB.cons_ok hn D.context hx hF))
  simpa only [Tm.lst] using Ctx.JEqB.app hk
    (Ctx.JEqB.cumul hk (Nat.le_max_left n (m + 1)) hF) hU hfirst htu

theorem inductionMotive_open (S : Description) (n : ℕ) (C : Tm 0) (x : String) :
    (S.inductionMotive n C).open x =
      .pi (S.coherence n (.fv x))
        (.app (.app (C.castLE (Nat.zero_le 1)) (S.root (.fv x))) (S.canonical (.fv x) (.bv 0))) := by
  simp only [Description.inductionMotive, Tm.open, coherence_open, root_open, canonical_open,
    Tm.closed_castLE_open, lastCases_zero, lastCases_one, lastCases_first]

/-- The ordinary W motive is formed from the actual fully dependent indexed motive. -/
theorem inductionMotive_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H)
    (hm : RuleBudget.Allows levels (m + 1)) {C : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels H (.univ (max n m))
      ((S.inductionMotive n C).open x) ((S.inductionMotive n C).open x) := by
  intro x hx
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hctx : (Γ.cons x S.raw).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hx (raw_formation_of_hypotheses hH D.toFormationData)
  have dx := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hx S.raw) hctx
  have ht : (Γ.cons x S.raw).JEqB levels H S.raw (.fv x) (.fv x) :=
    .var hctx (.here Γ x S.raw)
  have hcoh : (Γ.cons x S.raw).JEqB levels H (.univ n)
      (S.coherence n (.fv x)) (S.coherence n (.fv x)) := coherence_formation_of_hypotheses hH dx ht
  have hCx := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hx hn (raw_formation_of_hypotheses hH D.toFormationData) hC
  have hbody : ∀ c ∉ (Γ.cons x S.raw).dv,
      ((Γ.cons x S.raw).cons c (S.coherence n (.fv x))).JEqB levels H (.univ (max n m))
        ((.app (.app (C.castLE (Nat.zero_le 1)) (S.root (.fv x)))
          (S.canonical (.fv x) (.bv 0)) : Tm 1).open c)
        ((.app (.app (C.castLE (Nat.zero_le 1)) (S.root (.fv x)))
          (S.canonical (.fv x) (.bv 0)) : Tm 1).open c) := by
    intro c hc
    have hctxc : ((Γ.cons x S.raw).cons c (S.coherence n (.fv x))).JEqB levels H .unit .star .star :=
      .cons_ok hn hctx hc hcoh
    have dc := dx.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hc (S.coherence n (.fv x))) hctxc
    have ht' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx hc hn hcoh ht
    have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening hctx hc hn hcoh hCx
    have hc' : ((Γ.cons x S.raw).cons c (S.coherence n (.fv x))).JEqB levels H
        (S.coherence n (.fv x)) (.fv c) (.fv c) := .var hctxc (.here _ c _)
    have hcanonical := canonical_typing_of_hypotheses hH dc ht' hc'
    have hmotive := motive_congr_of_hypotheses hH dc hm hC' (root_typing_of_hypotheses hH dc.toFormationData ht') hcanonical
    simpa only [Tm.open, Tm.closed_castLE_open, Tm.castLE_refl, root_open, canonical_open,
      lastCases_zero] using Ctx.JEqB.cumul hq (Nat.le_max_right n m) hmotive
  simpa only [inductionMotive_open] using
    Ctx.JEqB.pi hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hcoh) hbody

/-- Transport the indexed motive from an arbitrary original fibre value to its canonical form. -/
theorem motive_reconstruction_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i t : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (.univ m) (.app (.app C i) t)
      (.app (.app C (S.root (.fst t))) (S.canonical (.fst t) (.snd (.snd t)))) :=
  motive_congr_of_hypotheses hH D hm hC (fibre_index_eq_of_hypotheses hH D hi ht).symm (fibre_reconstruction_of_hypotheses hH D hi ht)

private theorem cast_one_eq_wk0 (I : Tm 0) : I.castLE (Nat.zero_le 1) = I.wk0 :=
  (Tm.wkn_past I 0 (Nat.le_refl 0)).symm

theorem inductionMotive_lst (S : Description) (n : ℕ) (C t : Tm 0) :
    (S.inductionMotive n C).lst t =
      .pi (S.coherence n t)
        (.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0))) := by
  simp only [Description.inductionMotive, Tm.lst, coherence_lst, root_lst, canonical_lst,
    Tm.closed_castLE_lst, lastCases_zero, lastCases_one, lastCases_first, Tm.castLE_refl,
    cast_one_eq_wk0]

/-- Actual formation of the canonical motive under an original coherence declaration. -/
theorem canonicalMotive_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H)
    (hm : RuleBudget.Allows levels (m + 1)) {C t : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C) (ht : Γ.JEqB levels H S.raw t t) :
    ∀ c ∉ Γ.dv, (Γ.cons c (S.coherence n t)).JEqB levels H (.univ m)
      ((.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0)) : Tm 1).open c)
      ((.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0)) : Tm 1).open c) := by
  intro c hc
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hcoh : Γ.JEqB levels H (.univ n) (S.coherence n t) (S.coherence n t) := coherence_formation_of_hypotheses hH D ht
  have hctx : (Γ.cons c (S.coherence n t)).JEqB levels H .unit .star .star :=
    .cons_ok hn D.context hc hcoh
  have dc := D.weaken_of_hypotheses hH.weakening (Ctx.LookupLE.fresh_cons hc (S.coherence n t)) hctx
  have ht' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hc hn hcoh ht
  have hC' := Ctx.JEqB.weaken_cons_of_hypotheses hH.weakening D.context hc hn hcoh hC
  have hc' : (Γ.cons c (S.coherence n t)).JEqB levels H (S.coherence n t) (.fv c) (.fv c) :=
    .var hctx (.here Γ c (S.coherence n t))
  have hcan := canonical_typing_of_hypotheses hH dc ht' hc'
  simpa only [Tm.open, Tm.closed_wk0_open, root_open, canonical_open, lastCases_zero] using
    motive_congr_of_hypotheses hH dc hm hC' (root_typing_of_hypotheses hH dc.toFormationData ht') hcan

/-- Actual congruence of the constructed raw motive along raw-tree equality. -/
theorem inductionMotive_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C t u : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (htu : Γ.JEqB levels H S.raw t u) :
    Γ.JEqB levels H (.univ (max n m))
      ((S.inductionMotive n C).lst t) ((S.inductionMotive n C).lst u) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hq' : RuleBudget.Allows levels (max n m + 1) := by have := D.bound; budget_omega
  have hW : Γ.JEqB levels H (.univ (max n m)) S.raw S.raw :=
    .cumul hq (Nat.le_max_left n m) (raw_formation_of_hypotheses hH D.toFormationData)
  have hM := inductionMotive_formation_of_hypotheses hH D hm hC
  have habs := Ctx.JEqB.abstract_type hq' D.context hW hM
  have hU : ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels H (.univ (max n m + 1))
      ((.univ (max n m) : Tm 1).open x) ((.univ (max n m) : Tm 1).open x) := by
    intro x hx
    simpa only [Tm.open] using Ctx.JEqB.univ hq'
      (Ctx.JEqB.cons_ok hn D.context hx (raw_formation_of_hypotheses hH D.toFormationData))
  have happ : Γ.JEqB levels H (.univ (max n m))
      (.app (.abs S.raw (S.inductionMotive n C)) t)
      (.app (.abs S.raw (S.inductionMotive n C)) u) := by
    simpa only [Tm.lst] using Ctx.JEqB.app hq'
      (Ctx.JEqB.cumul hq' (Nat.le_succ (max n m)) hW) hU habs htu
  have ht := htu.trans htu.symm
  have hu := htu.symm.trans htu
  exact ((Ctx.JEqB.type_beta hq' D.context hW hM ht).symm.trans happ).trans
    (Ctx.JEqB.type_beta hq' D.context hW hM hu)

/-- Canonical motive application respects actual equality of coherence arguments. -/
theorem canonicalMotive_apply_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i t r r' c : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t)
    (hr : Γ.JEqB levels H ((S.inductionMotive n C).lst (.fst t)) r r')
    (hc : Γ.JEqB levels H (S.coherence n (.fst t)) (.snd (.snd t)) c) :
    Γ.JEqB levels H (.app (.app C i) t) (.app r (.snd (.snd t))) (.app r' c) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  have hraw : Γ.JEqB levels H S.raw (.fst t) (.fst t) := fibre_fst_typing_of_hypotheses hH D hi ht
  have hcoh : Γ.JEqB levels H (.univ n)
      (S.coherence n (.fst t)) (S.coherence n (.fst t)) := coherence_formation_of_hypotheses hH D hraw
  have hrec : Γ.JEqB levels H
      (.pi (S.coherence n (.fst t))
        (.app (.app C.wk0 (S.root (Tm.fst t).wk0)) (S.canonical (Tm.fst t).wk0 (.bv 0)))) r r' := by
    simpa only [inductionMotive_lst] using hr
  have hbody : ∀ c ∉ Γ.dv, (Γ.cons c (S.coherence n (.fst t))).JEqB levels H (.univ (max n m))
      ((.app (.app C.wk0 (S.root (Tm.fst t).wk0)) (S.canonical (Tm.fst t).wk0 (.bv 0)) : Tm 1).open c)
      ((.app (.app C.wk0 (S.root (Tm.fst t).wk0)) (S.canonical (Tm.fst t).wk0 (.bv 0)) : Tm 1).open c) := by
    intro c hc
    exact .cumul hq (Nat.le_max_right n m) (canonicalMotive_codomain_of_hypotheses hH D hm hC hraw c hc)
  have happ : Γ.JEqB levels H
      (.app (.app C (S.root (.fst t))) (S.canonical (.fst t) (.snd (.snd t))))
      (.app r (.snd (.snd t))) (.app r' c) := by
    simpa only [Tm.lst, root_lst, canonical_lst, Tm.closed_wk0_lst, lastCases_zero,
      Tm.castLE_refl] using Ctx.JEqB.app hq (Ctx.JEqB.cumul hq (Nat.le_max_left n m) hcoh)
        hbody hrec hc
  exact .conv (by budget_omega) (motive_reconstruction_of_hypotheses hH D hm hC hi ht).symm happ

/-- Apply a canonical raw motive result to an arbitrary inhabitant of the original fibre. -/
theorem canonicalMotive_apply_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i t r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t)
    (hr : Γ.JEqB levels H ((S.inductionMotive n C).lst (.fst t)) r r) :
    Γ.JEqB levels H (.app (.app C i) t) (.app r (.snd (.snd t))) (.app r (.snd (.snd t))) :=
  canonicalMotive_apply_congr_of_hypotheses hH D hm hC hi ht hr (fibre_coherence_typing_of_hypotheses hH D hi ht)

/-- Apply an actual raw W recursor and transport its canonical result to any original fibre value.

The source indexed step is constructed separately; this lemma only performs
W elimination and the final motive transport.
-/
theorem rawInduction_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i t : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (Tm.wStepType S.totalShape S.positions (S.inductionMotive n C)) s s)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (.app (.app C i) t)
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) s (.fst t)) (.snd (.snd t)))
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) s (.fst t)) (.snd (.snd t))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hq : RuleBudget.Allows levels (max n m) := RuleBudget.Allows.max hn (by budget_omega)
  exact canonicalMotive_apply_of_hypotheses hH D hm hC hi ht (Ctx.JEqB.wrec hn hq
    (totalShape_formation D.toFormationData) (positions_formation_of_hypotheses hH D.toFormationData)
    (inductionMotive_formation_of_hypotheses hH D hm hC) hs (fibre_fst_typing_of_hypotheses hH D hi ht))

/-- At closed scope the indexed step retains the exact original constructor. -/
theorem nodeAt_closed (S : Description) (i a f : Tm 0) : S.nodeAt i a f = S.node i a f := by
  simp only [Description.nodeAt, Description.node, Tm.castLE_refl, Description.positionAt]


theorem canonical_typing (D : IndexedFormationData S levels n Γ) {t c : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t t) (hc : Γ.JEqB levels ∅ (S.coherence n t) c c) :
    Γ.JEqB levels ∅ (S.fibre n (S.root t)) (S.canonical t c) (S.canonical t c) :=
  canonical_typing_of_hypotheses (StructuralTheory.empty levels) D ht hc

theorem motive_congr (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i j t u : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hij : Γ.JEqB levels ∅ S.index i j) (htu : Γ.JEqB levels ∅ (S.fibre n i) t u) :
    Γ.JEqB levels ∅ (.univ m) (.app (.app C i) t) (.app (.app C j) u) :=
  motive_congr_of_hypotheses (StructuralTheory.empty levels) D hm hC hij htu

theorem inductionMotive_formation (D : IndexedFormationData S levels n Γ)
    (hm : RuleBudget.Allows levels (m + 1)) {C : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels ∅ (.univ (max n m))
      ((S.inductionMotive n C).open x) ((S.inductionMotive n C).open x) :=
  inductionMotive_formation_of_hypotheses (StructuralTheory.empty levels) D hm hC

theorem motive_reconstruction (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i t : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (.univ m) (.app (.app C i) t)
      (.app (.app C (S.root (.fst t))) (S.canonical (.fst t) (.snd (.snd t)))) :=
  motive_reconstruction_of_hypotheses (StructuralTheory.empty levels) D hm hC hi ht

theorem canonicalMotive_codomain (D : IndexedFormationData S levels n Γ)
    (hm : RuleBudget.Allows levels (m + 1)) {C t : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C) (ht : Γ.JEqB levels ∅ S.raw t t) :
    ∀ c ∉ Γ.dv, (Γ.cons c (S.coherence n t)).JEqB levels ∅ (.univ m)
      ((.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0)) : Tm 1).open c)
      ((.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0)) : Tm 1).open c) :=
  canonicalMotive_codomain_of_hypotheses (StructuralTheory.empty levels) D hm hC ht

theorem rawInduction_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i t : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (Tm.wStepType S.totalShape S.positions (S.inductionMotive n C)) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (.app (.app C i) t)
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) s (.fst t)) (.snd (.snd t)))
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) s (.fst t)) (.snd (.snd t))) :=
  rawInduction_typing_of_hypotheses (StructuralTheory.empty levels) D hm hC hs hi ht

theorem inductionMotive_congr (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C t u : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (htu : Γ.JEqB levels ∅ S.raw t u) :
    Γ.JEqB levels ∅ (.univ (max n m))
      ((S.inductionMotive n C).lst t) ((S.inductionMotive n C).lst u) :=
  inductionMotive_congr_of_hypotheses (StructuralTheory.empty levels) D hm hC htu

theorem canonicalMotive_apply_congr (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i t r r' c : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t)
    (hr : Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.fst t)) r r')
    (hc : Γ.JEqB levels ∅ (S.coherence n (.fst t)) (.snd (.snd t)) c) :
    Γ.JEqB levels ∅ (.app (.app C i) t) (.app r (.snd (.snd t))) (.app r' c) :=
  canonicalMotive_apply_congr_of_hypotheses (StructuralTheory.empty levels) D hm hC hi ht hr hc

theorem canonicalMotive_apply (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i t r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t)
    (hr : Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.fst t)) r r) :
    Γ.JEqB levels ∅ (.app (.app C i) t) (.app r (.snd (.snd t))) (.app r (.snd (.snd t))) :=
  canonicalMotive_apply_of_hypotheses (StructuralTheory.empty levels) D hm hC hi ht hr

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

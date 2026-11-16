module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Induction.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WInductionMotive

@[expose] public section

/-! Canonical indexed motives and their actual ordinary-W recursor adapter.

The raw-step synthesis and final original indexed eliminator are exported by
`Induction.RawStep.Thms`.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n m : ℕ} {Γ : Ctx}


/-- Indexed induction retains structurally stable judgment hypotheses at the exact budget. -/
theorem canonical_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {t c : Tm 0}
    (ht : Γ.JEqB levels H S.raw t t) (hc : Γ.JEqB levels H (S.coherence n t) c c) :
    Γ.JEqB levels H (S.fibre n (S.root t)) (S.canonical t c) (S.canonical t c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonical_typing_of_hypotheses hH D ht hc

theorem motive_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i j t u : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hij : Γ.JEqB levels H S.index i j) (htu : Γ.JEqB levels H (S.fibre n i) t u) :
    Γ.JEqB levels H (.univ m) (.app (.app C i) t) (.app (.app C j) u) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.motive_congr_of_hypotheses hH D hm hC hij htu

theorem inductionMotive_formation_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H)
    (hm : RuleBudget.Allows levels (m + 1)) {C : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels H (.univ (max n m))
      ((S.inductionMotive n C).open x) ((S.inductionMotive n C).open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionMotive_formation_of_hypotheses hH D hm hC

theorem motive_reconstruction_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i t : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (.univ m) (.app (.app C i) t)
      (.app (.app C (S.root (.fst t))) (S.canonical (.fst t) (.snd (.snd t)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.motive_reconstruction_of_hypotheses hH D hm hC hi ht

theorem canonicalMotive_codomain_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H)
    (hm : RuleBudget.Allows levels (m + 1)) {C t : Tm 0}
    (hC : Γ.JEqB levels H (S.motiveType n m) C C) (ht : Γ.JEqB levels H S.raw t t) :
    ∀ c ∉ Γ.dv, (Γ.cons c (S.coherence n t)).JEqB levels H (.univ m)
      ((.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0)) : Tm 1).open c)
      ((.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0)) : Tm 1).open c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonicalMotive_codomain_of_hypotheses hH D hm hC ht

theorem rawInduction_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C s i t : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hs : Γ.JEqB levels H (Tm.wStepType S.totalShape S.positions (S.inductionMotive n C)) s s)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (.app (.app C i) t)
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) s (.fst t)) (.snd (.snd t)))
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) s (.fst t)) (.snd (.snd t))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.rawInduction_typing_of_hypotheses hH D hm hC hs hi ht

theorem inductionMotive_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C t u : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (htu : Γ.JEqB levels H S.raw t u) :
    Γ.JEqB levels H (.univ (max n m))
      ((S.inductionMotive n C).lst t) ((S.inductionMotive n C).lst u) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionMotive_congr_of_hypotheses hH D hm hC htu

theorem canonicalMotive_apply_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i t r r' c : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t)
    (hr : Γ.JEqB levels H ((S.inductionMotive n C).lst (.fst t)) r r')
    (hc : Γ.JEqB levels H (S.coherence n (.fst t)) (.snd (.snd t)) c) :
    Γ.JEqB levels H (.app (.app C i) t) (.app r (.snd (.snd t))) (.app r' c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonicalMotive_apply_congr_of_hypotheses hH D hm hC hi ht hr hc

theorem canonicalMotive_apply_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) (hm : RuleBudget.Allows levels (m + 1))
    {C i t r : Tm 0} (hC : Γ.JEqB levels H (S.motiveType n m) C C)
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t)
    (hr : Γ.JEqB levels H ((S.inductionMotive n C).lst (.fst t)) r r) :
    Γ.JEqB levels H (.app (.app C i) t) (.app r (.snd (.snd t))) (.app r (.snd (.snd t))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonicalMotive_apply_of_hypotheses hH D hm hC hi ht hr

theorem canonical_open {k : ℕ} (S : Description) (t c : Tm (k + 1)) (x : String) :
    (S.canonical t c).open x = S.canonical (t.open x) (c.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonical_open S t c x

theorem canonical_lst {k : ℕ} (S : Description) (t c : Tm (k + 1)) (a : Tm 0) :
    (S.canonical t c).lst a = S.canonical (t.lst a) (c.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonical_lst S t c a

theorem canonical_typing (D : IndexedFormationData S levels n Γ) {t c : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t t) (hc : Γ.JEqB levels ∅ (S.coherence n t) c c) :
    Γ.JEqB levels ∅ (S.fibre n (S.root t)) (S.canonical t c) (S.canonical t c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonical_typing D ht hc

theorem motive_congr (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i j t u : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hij : Γ.JEqB levels ∅ S.index i j) (htu : Γ.JEqB levels ∅ (S.fibre n i) t u) :
    Γ.JEqB levels ∅ (.univ m) (.app (.app C i) t) (.app (.app C j) u) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.motive_congr D hm hC hij htu

theorem inductionMotive_open (S : Description) (n : ℕ) (C : Tm 0) (x : String) :
    (S.inductionMotive n C).open x =
      .pi (S.coherence n (.fv x))
        (.app (.app (C.castLE (Nat.zero_le 1)) (S.root (.fv x))) (S.canonical (.fv x) (.bv 0))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionMotive_open S n C x

theorem inductionMotive_formation (D : IndexedFormationData S levels n Γ)
    (hm : RuleBudget.Allows levels (m + 1)) {C : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C) :
    ∀ x ∉ Γ.dv, (Γ.cons x S.raw).JEqB levels ∅ (.univ (max n m))
      ((S.inductionMotive n C).open x) ((S.inductionMotive n C).open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionMotive_formation D hm hC

theorem motive_reconstruction (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i t : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (.univ m) (.app (.app C i) t)
      (.app (.app C (S.root (.fst t))) (S.canonical (.fst t) (.snd (.snd t)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.motive_reconstruction D hm hC hi ht

theorem inductionMotive_lst (S : Description) (n : ℕ) (C t : Tm 0) :
    (S.inductionMotive n C).lst t =
      .pi (S.coherence n t)
        (.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionMotive_lst S n C t

theorem canonicalMotive_codomain (D : IndexedFormationData S levels n Γ)
    (hm : RuleBudget.Allows levels (m + 1)) {C t : Tm 0}
    (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C) (ht : Γ.JEqB levels ∅ S.raw t t) :
    ∀ c ∉ Γ.dv, (Γ.cons c (S.coherence n t)).JEqB levels ∅ (.univ m)
      ((.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0)) : Tm 1).open c)
      ((.app (.app C.wk0 (S.root t.wk0)) (S.canonical t.wk0 (.bv 0)) : Tm 1).open c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonicalMotive_codomain D hm hC ht

theorem rawInduction_typing (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C s i t : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hs : Γ.JEqB levels ∅ (Tm.wStepType S.totalShape S.positions (S.inductionMotive n C)) s s)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (.app (.app C i) t)
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) s (.fst t)) (.snd (.snd t)))
      (.app (.wrec S.totalShape S.positions (S.inductionMotive n C) s (.fst t)) (.snd (.snd t))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.rawInduction_typing D hm hC hs hi ht

theorem nodeAt_closed (S : Description) (i a f : Tm 0) : S.nodeAt i a f = S.node i a f :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nodeAt_closed S i a f

theorem inductionMotive_congr (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C t u : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (htu : Γ.JEqB levels ∅ S.raw t u) :
    Γ.JEqB levels ∅ (.univ (max n m))
      ((S.inductionMotive n C).lst t) ((S.inductionMotive n C).lst u) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.inductionMotive_congr D hm hC htu

theorem canonicalMotive_apply_congr (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i t r r' c : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t)
    (hr : Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.fst t)) r r')
    (hc : Γ.JEqB levels ∅ (S.coherence n (.fst t)) (.snd (.snd t)) c) :
    Γ.JEqB levels ∅ (.app (.app C i) t) (.app r (.snd (.snd t))) (.app r' c) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonicalMotive_apply_congr D hm hC hi ht hr hc

theorem canonicalMotive_apply (D : IndexedFormationData S levels n Γ) (hm : RuleBudget.Allows levels (m + 1))
    {C i t r : Tm 0} (hC : Γ.JEqB levels ∅ (S.motiveType n m) C C)
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t)
    (hr : Γ.JEqB levels ∅ ((S.inductionMotive n C).lst (.fst t)) r r) :
    Γ.JEqB levels ∅ (.app (.app C i) t) (.app r (.snd (.snd t))) (.app r (.snd (.snd t))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.canonicalMotive_apply D hm hC hi ht hr

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

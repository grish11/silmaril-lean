module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Node.Direct.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Extensionality

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

/-- The edge proof carried by an arbitrary original fibre value. -/
theorem fibre_edge_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (.id S.index (S.root (.fst t)) i) (.fst (.snd t)) (.fst (.snd t)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hraw := fibre_fst_typing_of_hypotheses hH D hi ht
  have hE := Ctx.JEqB.id hn D.index (root_typing_of_hypotheses hH D.toFormationData hraw) hi
  have hcoh := coherence_formation_of_hypotheses hH D hraw
  exact .fst hn hE (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh) (fibre_snd_typing_of_hypotheses hH D hi ht)

/-- Actual coherence, extracted from the original fibre rather than supplied separately. -/
theorem fibre_coherence_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (S.coherence n (.fst t)) (.snd (.snd t)) (.snd (.snd t)) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hraw := fibre_fst_typing_of_hypotheses hH D hi ht
  have hE := Ctx.JEqB.id hn D.index (root_typing_of_hypotheses hH D.toFormationData hraw) hi
  have hcoh := coherence_formation_of_hypotheses hH D hraw
  simpa only [Tm.closed_wk0_lst] using
    Ctx.JEqB.snd hn hE (Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh) (fibre_snd_typing_of_hypotheses hH D hi ht)

/-- Equality reflection identifies the actual raw root with the requested fibre index. -/
theorem fibre_index_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H S.index (S.root (.fst t)) i :=
  .reflect (root_typing_of_hypotheses hH D.toFormationData (fibre_fst_typing_of_hypotheses hH D hi ht)) hi (fibre_edge_typing_of_hypotheses hH D hi ht)

/-- Every original fibre inhabitant is its raw tree plus canonical identity and actual coherence. -/
theorem fibre_reconstruction_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (S.fibre n i) t
      (.pair (.fst t) (.pair (.refl (S.root (.fst t))) (.snd (.snd t)))) := by
  have hn : RuleBudget.Allows levels n := by have := D.bound; budget_omega
  have hraw : Γ.JEqB levels H S.raw (.fst t) (.fst t) := fibre_fst_typing_of_hypotheses hH D hi ht
  have hroot := root_typing_of_hypotheses hH D.toFormationData hraw
  have hE : Γ.JEqB levels H (.univ n)
      (.id S.index (S.root (.fst t)) i) (.id S.index (S.root (.fst t)) i) :=
    .id hn D.index hroot hi
  have hcoh : Γ.JEqB levels H (.univ n)
      (S.coherence n (.fst t)) (S.coherence n (.fst t)) := coherence_formation_of_hypotheses hH D hraw
  have hfamily := Ctx.JEqB.constant_family_of_hypotheses hH.weakening hn D.context hE hcoh
  have hedge := fibre_edge_typing_of_hypotheses hH D hi ht
  have hc := fibre_coherence_typing_of_hypotheses hH D hi ht
  have htailEta := Ctx.JEqB.sigma_eta hn hE hfamily (fibre_snd_typing_of_hypotheses hH D hi ht)
  have htailPair : Γ.JEqB levels H
      (.sigma (.id S.index (S.root (.fst t)) i) (S.coherence n (.fst t)).wk0)
      (.pair (.fst (.snd t)) (.snd (.snd t)))
      (.pair (.refl (S.root (.fst t))) (.snd (.snd t))) := by
    exact .pair hn hE hfamily (.id_uip hroot hi hedge)
      (by simpa only [Tm.closed_wk0_lst] using hc)
  have htail : Γ.JEqB levels H
      ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
        (S.coherence n (.bv 1)) : Tm 1).lst (.fst t))
      (.snd t) (.pair (.refl (S.root (.fst t))) (.snd (.snd t))) := by
    simpa only [fibreTail_lst] using htailEta.trans htailPair
  have hpair : Γ.JEqB levels H (S.fibre n i)
      (.pair (.fst t) (.snd t))
      (.pair (.fst t) (.pair (.refl (S.root (.fst t))) (.snd (.snd t)))) :=
    .pair hn (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hi) hraw htail
  exact (Ctx.JEqB.sigma_eta hn (raw_formation_of_hypotheses hH D.toFormationData) (fibreTail_formation_of_hypotheses hH D hi) ht).trans hpair

theorem fibre_edge_typing (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (.id S.index (S.root (.fst t)) i) (.fst (.snd t)) (.fst (.snd t)) :=
  fibre_edge_typing_of_hypotheses (StructuralTheory.empty levels) D hi ht

theorem fibre_coherence_typing (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (S.coherence n (.fst t)) (.snd (.snd t)) (.snd (.snd t)) :=
  fibre_coherence_typing_of_hypotheses (StructuralTheory.empty levels) D hi ht

theorem fibre_index_eq (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ S.index (S.root (.fst t)) i :=
  fibre_index_eq_of_hypotheses (StructuralTheory.empty levels) D hi ht

theorem fibre_reconstruction (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (S.fibre n i) t
      (.pair (.fst t) (.pair (.refl (S.root (.fst t))) (.snd (.snd t)))) :=
  fibre_reconstruction_of_hypotheses (StructuralTheory.empty levels) D hi ht

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

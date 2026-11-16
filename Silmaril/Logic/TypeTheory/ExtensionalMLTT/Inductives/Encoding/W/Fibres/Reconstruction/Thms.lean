module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Node.Direct.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Extensionality
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WFibreReconstruction

@[expose] public section

/-! Reconstruction and reflected index equality for every original fibre inhabitant. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}


theorem fibre_edge_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (.id S.index (S.root (.fst t)) i) (.fst (.snd t)) (.fst (.snd t)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_edge_typing_of_hypotheses hH D hi ht

theorem fibre_coherence_typing_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (S.coherence n (.fst t)) (.snd (.snd t)) (.snd (.snd t)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_coherence_typing_of_hypotheses hH D hi ht

theorem fibre_index_eq_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H S.index (S.root (.fst t)) i :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_index_eq_of_hypotheses hH D hi ht

theorem fibre_reconstruction_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i t : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ht : Γ.JEqB levels H (S.fibre n i) t t) :
    Γ.JEqB levels H (S.fibre n i) t
      (.pair (.fst t) (.pair (.refl (S.root (.fst t))) (.snd (.snd t)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_reconstruction_of_hypotheses hH D hi ht

theorem fibre_edge_typing (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (.id S.index (S.root (.fst t)) i) (.fst (.snd t)) (.fst (.snd t)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_edge_typing D hi ht

theorem fibre_coherence_typing (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (S.coherence n (.fst t)) (.snd (.snd t)) (.snd (.snd t)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_coherence_typing D hi ht

theorem fibre_index_eq (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ S.index (S.root (.fst t)) i :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_index_eq D hi ht

theorem fibre_reconstruction (D : IndexedFormationData S levels n Γ) {i t : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ht : Γ.JEqB levels ∅ (S.fibre n i) t t) :
    Γ.JEqB levels ∅ (S.fibre n i) t
      (.pair (.fst t) (.pair (.refl (S.root (.fst t))) (.snd (.snd t)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_reconstruction D hi ht

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

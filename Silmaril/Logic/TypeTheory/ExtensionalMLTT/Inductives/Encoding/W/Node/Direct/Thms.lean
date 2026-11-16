module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Node
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Next
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WDirectNode

@[expose] public section

/-! The original constructor with children at the direct source next index. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}


theorem fibre_congr_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i j : Tm 0}
    (hij : Γ.JEqB levels H S.index i j) :
    Γ.JEqB levels H (.univ n) (S.fibre n i) (S.fibre n j) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_congr_of_hypotheses hH D hij

theorem childFibres_tagged_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n)
      (.pi (S.positionAt i a) (S.childFibres n (.pair i a)))
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childFibres_tagged_beta_of_hypotheses hH D hi ha

theorem node_typing_direct_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a f : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hf : Γ.JEqB levels H (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) f f) :
    Γ.JEqB levels H (S.fibre n i) (S.node i a f) (S.node i a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_typing_direct_of_hypotheses hH D hi ha hf

theorem fibre_congr (D : IndexedFormationData S levels n Γ) {i j : Tm 0}
    (hij : Γ.JEqB levels ∅ S.index i j) :
    Γ.JEqB levels ∅ (.univ n) (S.fibre n i) (S.fibre n j) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_congr D hij

theorem childFibres_tagged_beta (D : IndexedFormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n)
      (.pi (S.positionAt i a) (S.childFibres n (.pair i a)))
      (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childFibres_tagged_beta D hi ha

theorem node_typing_direct (D : IndexedFormationData S levels n Γ) {i a f : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hf : Γ.JEqB levels ∅ (.pi (S.positionAt i a) (S.fibreAt n ((S.next.lst i).lst a))) f f) :
    Γ.JEqB levels ∅ (S.fibre n i) (S.node i a f) (S.node i a f) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.node_typing_direct D hi ha hf

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

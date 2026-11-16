module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Fibres.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WFibreFamily

@[expose] public section

/-! The original fibre under bound indices and tagged-position conversion. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg}

theorem fibreAt_formation_of_hypotheses {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    Γ.JEqB levels H (.univ n) (S.fibreAt n i) (S.fibreAt n i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreAt_formation_of_hypotheses hH D hi

theorem positions_tagged_beta_of_hypotheses {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) (S.positions.lst (.pair i a)) (S.positionAt i a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positions_tagged_beta_of_hypotheses hH D hi ha

theorem fibreAt_closed (S : Description) (n : ℕ) (i : Tm 0) :
    S.fibreAt n i = S.fibre n i :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreAt_closed S n i

theorem fibreAt_open {k : ℕ} (S : Description) (n : ℕ) (i : Tm (k + 1)) (x : String) :
    (S.fibreAt n i).open x = S.fibreAt n (i.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreAt_open S n i x

theorem fibreAt_lst {k : ℕ} (S : Description) (n : ℕ) (i : Tm (k + 1)) (a : Tm 0) :
    (S.fibreAt n i).lst a = S.fibreAt n (i.lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreAt_lst S n i a

theorem fibreAt_formation {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    (D : IndexedFormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    Γ.JEqB levels ∅ (.univ n) (S.fibreAt n i) (S.fibreAt n i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreAt_formation D hi

theorem coherence_wk0 (S : Description) (n : ℕ) (t : Tm 0) :
    (S.coherence n t).wk0 = S.coherence n t.wk0 :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_wk0 S n t

theorem fibreTail_lst (S : Description) (n : ℕ) (i t : Tm 0) :
    ((.sigma (.id S.index.wk0 (S.root (.bv 0)) i.wk0)
      (S.coherence n (.bv 1)) : Tm 1).lst t) =
    .sigma (.id S.index (S.root t) i) (S.coherence n t).wk0 :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibreTail_lst S n i t

theorem positions_tagged_beta {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}
    (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) (S.positions.lst (.pair i a)) (S.positionAt i a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positions_tagged_beta D hi ha

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

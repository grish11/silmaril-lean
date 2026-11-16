module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Fibres
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WNextComputation

@[expose] public section

/-! Actual computation of the original indexed-W next-index templates. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {H : Set Jdg} {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}


theorem nextFamily_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H ((S.position.lst i).lst a) p p) :
    Γ.JEqB levels H S.index (.app (.app (.app S.nextFamily i) a) p)
      (((S.next.lst i).lst a).lst p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextFamily_beta_of_hypotheses hH D hi ha hp

theorem nextFamily_beta_direct_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H S.index (.app (.app (.app S.nextFamily i) a) p)
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextFamily_beta_direct_of_hypotheses hH D hi ha hp

theorem compiledChildIndex_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hp : Γ.JEqB levels H (S.positions.lst l) p p) :
    Γ.JEqB levels H S.index (S.compiledChildIndex l p) (S.childIndexAt l p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledChildIndex_beta_of_hypotheses hH D hl hp

theorem childIndexAt_tagged_beta_of_hypotheses (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H S.index (S.childIndexAt (.pair i a) p)
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childIndexAt_tagged_beta_of_hypotheses hH D hi ha hp

theorem nextFamily_beta (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ ((S.position.lst i).lst a) p p) :
    Γ.JEqB levels ∅ S.index (.app (.app (.app S.nextFamily i) a) p)
      (((S.next.lst i).lst a).lst p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextFamily_beta D hi ha hp

theorem nextFamily_beta_direct (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ S.index (.app (.app (.app S.nextFamily i) a) p)
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextFamily_beta_direct D hi ha hp

theorem compiledChildIndex_beta (D : IndexedFormationData S levels n Γ) {l p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hp : Γ.JEqB levels ∅ (S.positions.lst l) p p) :
    Γ.JEqB levels ∅ S.index (S.compiledChildIndex l p) (S.childIndexAt l p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledChildIndex_beta D hl hp

theorem childIndexAt_tagged_beta (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ S.index (S.childIndexAt (.pair i a) p)
      (S.next.bsubst (Fin.cases p (Fin.cases a (fun _ => i)))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childIndexAt_tagged_beta D hi ha hp

theorem successor_nextFamily_beta : Ctx.JEqB 2 ∅ .nil .nats
    (.app (.app (.app successorDescription.nextFamily .zero) .star) .star) (.succ .zero) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.successor_nextFamily_beta

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Source.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WSourceInstantiation

@[expose] public section

/-!
# Instantiating the original source telescope

These are actual object derivations. Single-name structural substitution
transports the dependent source contexts; beta then identifies compiled
positions with direct substitution. The original child-index term is curried
and applied using that object equality, without an additional compiled-child
certificate. Recursive coherence/fibre derivability remains separate.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

theorem double_lst_eq_bsubst (C : Tm 2) (i a : Tm 0) :
    (C.lst i).lst a = C.bsubst (Fin.cases a (fun _ => i)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.double_lst_eq_bsubst C i a

theorem shapeAt_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    Γ.JEqB levels H (.univ n) (S.shape.lst i) (S.shape.lst i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.shapeAt_formation_of_hypotheses hH D hi

theorem position_after_index_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    ∃ L : Finset String, ∀ y ∉ L, (Γ.cons y (S.shape.lst i)).JEqB levels H (.univ n)
      ((S.position.lst i).open y) ((S.position.lst i).open y) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.position_after_index_of_hypotheses hH D hi

theorem positionAt_formation_iterated_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) ((S.position.lst i).lst a) ((S.position.lst i).lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionAt_formation_iterated_of_hypotheses hH D hi ha

theorem positionFamily_beta_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) (.app (.app S.positionFamily i) a)
      ((S.position.lst i).lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionFamily_beta_of_hypotheses hH D hi ha

theorem positionAt_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) (S.positionAt i a) (S.positionAt i a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionAt_formation_of_hypotheses hH D hi ha

theorem positionFamily_beta_direct_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {i a : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a) :
    Γ.JEqB levels H (.univ n) (.app (.app S.positionFamily i) a) (S.positionAt i a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionFamily_beta_direct_of_hypotheses hH D hi ha

theorem compiledPositions_beta_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) {l : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l) :
    Γ.JEqB levels H (.univ n) (S.compiledPositions.lst l) (S.positions.lst l) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledPositions_beta_of_hypotheses hH D hl

theorem compiledRaw_beta_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) :
    Γ.JEqB levels H (.univ n) S.compiledRaw S.raw :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledRaw_beta_of_hypotheses hH D

theorem raw_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : FormationData S levels n Γ H) :
    Γ.JEqB levels H (.univ n) S.raw S.raw :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.raw_formation_of_hypotheses hH D

theorem nextValue_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i a p : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) (ha : Γ.JEqB levels H (S.shape.lst i) a a)
    (hp : Γ.JEqB levels H (S.positionAt i a) p p) :
    Γ.JEqB levels H S.index (.app (.app (.app S.nextFamily i) a) p)
      (.app (.app (.app S.nextFamily i) a) p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextValue_typing_of_hypotheses hH D hi ha hp

theorem compiledChildIndex_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {l p : Tm 0}
    (hl : Γ.JEqB levels H S.totalShape l l)
    (hp : Γ.JEqB levels H (S.compiledPositions.lst l) p p) :
    Γ.JEqB levels H S.index (S.compiledChildIndex l p) (S.compiledChildIndex l p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledChildIndex_typing_of_hypotheses hH D hl hp

theorem shapeAt_formation (D : FormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    Γ.JEqB levels ∅ (.univ n) (S.shape.lst i) (S.shape.lst i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.shapeAt_formation D hi

theorem position_after_index (D : FormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    ∃ L : Finset String, ∀ y ∉ L, (Γ.cons y (S.shape.lst i)).JEqB levels ∅ (.univ n)
      ((S.position.lst i).open y) ((S.position.lst i).open y) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.position_after_index D hi

theorem positionAt_formation_iterated (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) ((S.position.lst i).lst a) ((S.position.lst i).lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionAt_formation_iterated D hi ha

theorem positionFamily_beta (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) (.app (.app S.positionFamily i) a)
      ((S.position.lst i).lst a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionFamily_beta D hi ha

theorem positionAt_formation (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) (S.positionAt i a) (S.positionAt i a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionAt_formation D hi ha

theorem positionFamily_beta_direct (D : FormationData S levels n Γ) {i a : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a) :
    Γ.JEqB levels ∅ (.univ n) (.app (.app S.positionFamily i) a) (S.positionAt i a) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.positionFamily_beta_direct D hi ha

theorem compiledPositions_beta (D : FormationData S levels n Γ) {l : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l) :
    Γ.JEqB levels ∅ (.univ n) (S.compiledPositions.lst l) (S.positions.lst l) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledPositions_beta D hl

theorem compiledRaw_beta (D : FormationData S levels n Γ) :
    Γ.JEqB levels ∅ (.univ n) S.compiledRaw S.raw :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledRaw_beta D

theorem raw_formation (D : FormationData S levels n Γ) :
    Γ.JEqB levels ∅ (.univ n) S.raw S.raw :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.raw_formation D

theorem nextFamily_typing (D : IndexedFormationData S levels n Γ) :
    Γ.JEqB levels ∅ S.nextFamilyType S.nextFamily S.nextFamily :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextFamily_typing D

theorem nextValue_typing (D : IndexedFormationData S levels n Γ) {i a p : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) (ha : Γ.JEqB levels ∅ (S.shape.lst i) a a)
    (hp : Γ.JEqB levels ∅ (S.positionAt i a) p p) :
    Γ.JEqB levels ∅ S.index (.app (.app (.app S.nextFamily i) a) p)
      (.app (.app (.app S.nextFamily i) a) p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextValue_typing D hi ha hp

theorem compiledChildIndex_typing (D : IndexedFormationData S levels n Γ) {l p : Tm 0}
    (hl : Γ.JEqB levels ∅ S.totalShape l l)
    (hp : Γ.JEqB levels ∅ (S.compiledPositions.lst l) p p) :
    Γ.JEqB levels ∅ S.index (S.compiledChildIndex l p) (S.compiledChildIndex l p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.compiledChildIndex_typing D hl hp

/-- Curry the actual source child-index term under its original theory. -/
theorem nextFamily_typing_of_hypotheses {H : Set Jdg} (D : IndexedFormationData S levels n Γ H)
    (hh : HypothesisTransport levels H H) :
    Γ.JEqB levels H S.nextFamilyType S.nextFamily S.nextFamily :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextFamily_typing_of_hypotheses D hh

theorem successor_nextValue_typing : Ctx.JEqB 2 ∅ .nil .nats
    (.app (.app (.app successorDescription.nextFamily .zero) .star) .star)
    (.app (.app (.app successorDescription.nextFamily .zero) .star) .star) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.successor_nextValue_typing

def successorIndexedFormationData : IndexedFormationData successorDescription 2 0 .nil :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.successorIndexedFormationData

theorem nextFamily_data (D : IndexedFormationData S levels n Γ) :
    (∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels ∅ (.univ n)
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)) ∧
    (∀ x ∉ D.names, (Γ.cons x S.index).JEqB levels ∅
      ((.pi S.shape (.pi S.position (S.index.castLE (by decide))) : Tm 1).open x)
      ((.abs S.shape (.abs S.position S.next) : Tm 1).open x)
      ((.abs S.shape (.abs S.position S.next) : Tm 1).open x)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nextFamily_data D

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.W.Direct
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.ConstantStep
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.Encoding.WCoherenceTyping

@[expose] public section

/-! Actual derivability of the original recursive coherence and indexed fibre. -/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

variable {S : Description} {levels : RuleBudget} {n : ℕ} {Γ : Ctx}

def IndexedFormationData.weaken_of_hypotheses {H K : Set Jdg} {Δ : Ctx}
    (D : IndexedFormationData S levels n Γ H) (hh : HypothesisTransport levels H K)
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels K .unit .star .star) :
    IndexedFormationData S levels n Δ K :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedWeakenData_of_hypotheses D hh e hΔ

theorem coherenceBody_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) :
    ∀ x ∉ Γ.dv, ∀ f ∉ insert x Γ.dv, ∀ r ∉ insert f (insert x Γ.dv),
      (((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).cons r
        (.arr (S.positions.open x) (.univ n))).JEqB levels H (.univ n)
        (((S.coherenceBody.open x).open f).open r)
        (((S.coherenceBody.open x).open f).open r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceBody_typing_of_hypotheses hH D

theorem coherenceStep_typing_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) :
    Γ.JEqB levels H (Tm.wStepType S.totalShape S.positions (.univ n))
      (S.coherenceStep n) (S.coherenceStep n) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceStep_typing_of_hypotheses hH D

theorem coherence_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {t : Tm 0}
    (ht : Γ.JEqB levels H S.raw t t) :
    Γ.JEqB levels H (.univ n) (S.coherence n t) (S.coherence n t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_formation_of_hypotheses hH D ht

theorem fibre_formation_of_hypotheses {H : Set Jdg} (hH : StructuralTheory levels H) (D : IndexedFormationData S levels n Γ H) {i : Tm 0}
    (hi : Γ.JEqB levels H S.index i i) :
    Γ.JEqB levels H (.univ n) (S.fibre n i) (S.fibre n i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_formation_of_hypotheses hH D hi

def IndexedFormationData.weaken {Δ : Ctx} (D : IndexedFormationData S levels n Γ)
    (e : Γ.LookupLE Δ) (hΔ : Δ.JEqB levels ∅ .unit .star .star) :
    IndexedFormationData S levels n Δ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.indexedWeakenData D e hΔ

theorem root_open {k : ℕ} (S : Description) (t : Tm (k + 1)) (x : String) :
    (S.root t).open x = S.root (t.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.root_open S t x

theorem coherence_open {k : ℕ} (S : Description) (n : ℕ) (t : Tm (k + 1)) (x : String) :
    (S.coherence n t).open x = S.coherence n (t.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_open S n t x

theorem childIndexAt_open {k : ℕ} (S : Description) (l p : Tm (k + 1)) (x : String) :
    (S.childIndexAt l p).open x = S.childIndexAt (l.open x) (p.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.childIndexAt_open S l p x

theorem coherenceBody_open (S : Description) (label children ih : String) :
    ((S.coherenceBody.open label).open children).open ih =
      .pi (S.positions.lst (.fv label))
        (.sigma (.id S.index.wk0
          (S.root (.app (.fv children) (.bv 0)))
          (S.childIndexAt (.fv label) (.bv 0)))
          (.app (.fv ih) (.bv 1))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceBody_open S label children ih

theorem coherenceBody_typing (D : IndexedFormationData S levels n Γ) :
    ∀ x ∉ Γ.dv, ∀ f ∉ insert x Γ.dv, ∀ r ∉ insert f (insert x Γ.dv),
      (((Γ.cons x S.totalShape).cons f (.arr (S.positions.open x) S.raw)).cons r
        (.arr (S.positions.open x) (.univ n))).JEqB levels ∅ (.univ n)
        (((S.coherenceBody.open x).open f).open r)
        (((S.coherenceBody.open x).open f).open r) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceBody_typing D

theorem coherenceStep_typing (D : IndexedFormationData S levels n Γ) :
    Γ.JEqB levels ∅ (Tm.wStepType S.totalShape S.positions (.univ n))
      (S.coherenceStep n) (S.coherenceStep n) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceStep_typing D

theorem coherence_formation (D : IndexedFormationData S levels n Γ) {t : Tm 0}
    (ht : Γ.JEqB levels ∅ S.raw t t) :
    Γ.JEqB levels ∅ (.univ n) (S.coherence n t) (S.coherence n t) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherence_formation D ht

theorem fibre_formation (D : IndexedFormationData S levels n Γ) {i : Tm 0}
    (hi : Γ.JEqB levels ∅ S.index i i) :
    Γ.JEqB levels ∅ (.univ n) (S.fibre n i) (S.fibre n i) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.fibre_formation D hi

def nullaryIndexedFormationData : IndexedFormationData nullaryDescription 2 0 .nil :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullaryIndexedFormationData

def nullaryRawLeaf : Tm 0 :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullaryRawLeaf

theorem nullaryRawLeaf_typing : Ctx.JEqB 2 ∅ .nil nullaryDescription.raw
    nullaryRawLeaf nullaryRawLeaf :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullaryRawLeaf_typing

theorem nullary_root_typing : Ctx.JEqB 2 ∅ .nil .unit
    (nullaryDescription.root nullaryRawLeaf) (nullaryDescription.root nullaryRawLeaf) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullary_root_typing

theorem nullary_coherence_formation : Ctx.JEqB 2 ∅ .nil (.univ 0)
    (nullaryDescription.coherence 0 nullaryRawLeaf) (nullaryDescription.coherence 0 nullaryRawLeaf) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullary_coherence_formation

theorem nullary_fibre_formation : Ctx.JEqB 2 ∅ .nil (.univ 0)
    (nullaryDescription.fibre 0 .star) (nullaryDescription.fibre 0 .star) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.nullary_fibre_formation

theorem coherenceStep_eq_constantStep (S : Description) (n : ℕ) :
    S.coherenceStep n =
      .abs S.totalShape (.abs (.arr S.positions (S.raw.castLE (by decide)))
        (.abs ((Tm.arr S.positions (.univ n)).wk0) S.coherenceBody)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms.coherenceStep_eq_constantStep S n

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.WEncoding.Terms
